
/- This file develops the memory model that is used in the dynamic
  semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
-/

/- Memory states are accessed by addresses [b, ofs]: pairs of a block
  identifier [b] and a byte offset [ofs] within that block.
  Each address is associated to permissions, also known as access rights.
  The following permissions are expressible:
- Freeable (exclusive access): all operations permitted
- Writable: load, store and pointer comparison operations are permitted,
  but freeing is not.
- Readable: only load and pointer comparison operations are permitted.
- Nonempty: valid, but only pointer comparisons are permitted.
- Empty: not yet allocated or previously freed; no operation permitted.

The first four cases are represented by the following type of permissions.
Being empty is represented by the absence of any permission.
-/

import .memdata data.nat.bquant data.nat.dvd

namespace memory
open maps memdata values ast memdata.memval word integers

inductive permission : Type
| Freeable : permission
| Writable : permission
| Readable : permission
| Nonempty : permission
export permission

/- In the list, each permission implies the other permissions further down the
    list.  We reflect this fact by the following order over permissions. -/

inductive perm_order : permission → permission → Prop
| perm_refl (p)  : perm_order p p
| perm_F_any (p) : perm_order Freeable p
| perm_W_R       : perm_order Writable Readable
| perm_any_N (p) : perm_order p Nonempty
export perm_order

lemma perm_order_trans {p1 p2 p3}
  (p12 : perm_order p1 p2) (p23 : perm_order p2 p3) : perm_order p1 p3 := sorry

instance : decidable_rel perm_order :=
λ p1 p2, by cases p1; cases p2; {right, constructor} <|> {left, intro h, cases h}

/- Each address has not one, but two permissions associated
  with it.  The first is the current permission.  It governs whether
  operations (load, store, free, etc) over this address succeed or
  not.  The other is the maximal permission.  It is always at least as
  strong as the current permission.  Once a block is allocated, the
  maximal permission of an address within this block can only
  decrease, as a result of [free] or [drop_perm] operations, or of
  external calls.  In contrast, the current permission of an address
  can be temporarily lowered by an external call, then raised again by
  another external call. -/

inductive perm_kind : Type
| Max : perm_kind
| Cur : perm_kind
open perm_kind

local notation a # b := PTree.get b a

def perm_order' : option permission → permission → Prop
| (some p') p := perm_order p' p
| none      p := false

instance (op p) : decidable (perm_order' op p) :=
by cases op; dsimp [perm_order']; apply_instance

def perm_order'' : option permission → option permission → Prop
| _  none      := true
| p1 (some p2) := perm_order' p1 p2

theorem perm_order''.refl (op) : perm_order'' op op :=
by { cases op, trivial, apply perm_refl }

structure mem : Type :=
(mem_contents : PTree.t (PTree.t memval))  /- [block → offset → memval] -/
(mem_access : PTree.t (ℕ → perm_kind → option permission))
                                         /- [block → offset → kind → option permission] -/
(nextblock : block)
(access_max : ∀ (b : block) (ofs : ℕ), let m := (mem_access#b).get_or_else (λ_ _, none) in
  perm_order'' (m ofs Max) (m ofs Cur))
(nextblock_noaccess : ∀ {b : block} (ofs : ℕ) (k : perm_kind), nextblock ≤ b →
  (mem_access#b).get_or_else (λ_ _, none) ofs k = none)

/- * Validity of blocks and accesses -/

/- A block address is valid if it was previously allocated. It remains valid
  even after being freed. -/

def valid_block (m : mem) (b : block) := b < m.nextblock
instance valid_block_dec (m b) : decidable (valid_block m b) := by delta valid_block; apply_instance

theorem valid_not_valid_diff {m b b'} (h1 : valid_block m b) : ¬ valid_block m b' → b ≠ b' :=
mt $ λ bb, by rw bb at h1; assumption

def mem.access (m : mem) (b : block) : ℕ → perm_kind → option permission :=
(m.mem_access#b).get_or_else (λ_ _, none)

def mem.get_block (m : mem) (b : block) : PTree.t memval :=
(m.mem_contents#b).get_or_else (PTree.empty _)

def mem.contents (m : mem) (b : block) (ofs : ℕ) : memval :=
(m.get_block b # num.succ' ofs).get_or_else Undef

/- Permissions -/

def perm (m : mem) (b : block) (ofs : ℕ) (k : perm_kind) : permission → Prop :=
perm_order' (m.access b ofs k)

theorem perm_implies {m b ofs k p1 p2} :
  perm_order p1 p2 → perm m b ofs k p1 → perm m b ofs k p2 :=
by { delta perm, cases m.access b ofs k, apply λ_, id, apply λa b, perm_order_trans b a }

theorem perm_cur_max {m b ofs p} : perm m b ofs Cur p → perm m b ofs Max p := sorry

theorem perm_cur {m b ofs k p} : perm m b ofs Cur p → perm m b ofs k p := sorry

theorem perm_max {m b ofs k p} : perm m b ofs k p → perm m b ofs Max p := sorry

theorem perm_valid_block {m b ofs k p} : perm m b ofs k p → valid_block m b := sorry

instance perm_dec (m b ofs k p) : decidable (perm m b ofs k p) :=
by delta perm; apply_instance

def range_perm (m b lo hi k p) := ∀ ⦃ofs⦄, lo ≤ ofs → ofs < hi → perm m b ofs k p

theorem range_perm_implies {m b lo hi k p1 p2} :
  perm_order p1 p2 → range_perm m b lo hi k p1 → range_perm m b lo hi k p2 :=
λ o r ofs h1 h2, perm_implies o (r h1 h2)

theorem range_perm_cur {m b lo hi k p} :
  range_perm m b lo hi Cur p → range_perm m b lo hi k p :=
λ r ofs h1 h2, perm_cur (r h1 h2)

theorem range_perm_max {m b lo hi k p} :
  range_perm m b lo hi k p → range_perm m b lo hi Max p :=
λ r ofs h1 h2, perm_max (r h1 h2)

instance range_perm_dec {m b lo hi k p} : decidable (range_perm m b lo hi k p) :=
decidable_lo_hi _ _ _

/- [valid_access m chunk b ofs p] holds if a memory access
    of the given chunk is possible in [m] at address [b, ofs]
    with current permissions [p].
    This means:
- The range of bytes accessed all have current permission [p].
- The offset [ofs] is aligned.
-/

def valid_access (m) (chunk b ofs p) : Prop :=
range_perm m b ofs (ofs + memory_chunk.size chunk) Cur p ∧ chunk.align ∣ ofs

theorem valid_access_implies {m chunk b ofs p1 p2} :
  perm_order p1 p2 → valid_access m chunk b ofs p1 → valid_access m chunk b ofs p2 :=
λ o, and.imp (range_perm_implies o) id

theorem valid_access_freeable_any {m chunk b ofs p} :
  valid_access m chunk b ofs Freeable → valid_access m chunk b ofs p :=
valid_access_implies (by constructor)

lemma valid_access_perm {m chunk b ofs p} (k) :
  valid_access m chunk b ofs p → perm m b ofs k p :=
λ ⟨h, _⟩, perm_cur $ h (le_refl _) (nat.lt_add_of_pos_right chunk.size_pos)

theorem valid_access_valid_block {m chunk b ofs} :
  valid_access m chunk b ofs Nonempty → valid_block m b :=
λ h, decidable.by_contradiction $ λ hn,
have t : mem.access m b ofs Cur = none, from m.nextblock_noaccess ofs Cur (le_of_not_gt hn),
have p : _, from valid_access_perm Cur h,
by delta perm at p; rw t at p; exact p

lemma valid_access_compat {m} {chunk1 chunk2 : memory_chunk} {b ofs p} :
  chunk1.size = chunk2.size → chunk2.align ≤ chunk1.align →
  valid_access m chunk1 b ofs p → valid_access m chunk2 b ofs p := sorry

instance valid_access_dec (m chunk b ofs p) : decidable (valid_access m chunk b ofs p) :=
by delta valid_access; apply_instance

/- [valid_pointer m b ofs] returns [tt] if the address [b, ofs]
  is nonempty in [m] and [ff] if it is empty. -/
def valid_pointer (m : mem) (b : block) (ofs : ℕ) : bool := perm m b ofs Cur Nonempty

theorem valid_pointer_nonempty_perm {m b ofs} :
  valid_pointer m b ofs ↔ perm m b ofs Cur Nonempty :=
to_bool_iff _

theorem valid_pointer_valid_access {m b ofs} :
  valid_pointer m b ofs ↔ valid_access m Mint8unsigned b ofs Nonempty :=
valid_pointer_nonempty_perm.trans
⟨λh, ⟨λofs0 lo hi,
  have ofs = ofs0, from le_antisymm lo (nat.le_of_lt_succ hi),
  by rwa -show ofs = ofs0, from le_antisymm lo (nat.le_of_lt_succ hi),
  one_dvd _⟩,
valid_access_perm _⟩

/- C allows pointers one past the last element of an array.  These are not
  valid according to the previously defined [valid_pointer]. The property
  [weak_valid_pointer m b ofs] holds if address [b, ofs] is a valid pointer
  in [m], or a pointer one past a valid block in [m].  -/

def weak_valid_pointer (m : mem) (b : block) (ofs : ℕ) :=
valid_pointer m b ofs || valid_pointer m b (ofs - 1)

lemma weak_valid_pointer_spec {m b ofs} :
  weak_valid_pointer m b ofs ↔
    valid_pointer m b ofs ∨ valid_pointer m b (ofs - 1) :=
bor_iff _ _

lemma valid_pointer_implies {m b ofs}
  (v : valid_pointer m b ofs) : weak_valid_pointer m b ofs :=
weak_valid_pointer_spec.2 $ or.inl v

/- * Operations over memory stores -/

/- The initial store -/

protected def empty : mem :=
{ mem_contents       := PTree.empty _,
  mem_access         := PTree.empty _,
  nextblock          := 1,
  access_max         := λ b ofs, by rw PTree.gempty; trivial,
  nextblock_noaccess := λ b ofs k h, by rw PTree.gempty; trivial }
instance : has_emptyc mem := ⟨memory.empty⟩

/- Allocation of a fresh block with the given bounds.  Return an updated
  memory state and the address of the fresh block, which initially contains
  undefined cells.  Note that allocation never fails: we model an
  infinite memory. -/

def mem.alloc (m : mem) (lo hi : ℕ) : mem :=
{ mem_contents := PTree.set m.nextblock (PTree.empty _) m.mem_contents,
  mem_access := PTree.set m.nextblock
    (λ ofs k, if lo ≤ ofs ∧ ofs < hi then some Freeable else none) m.mem_access,
  nextblock := m.nextblock.succ,
  access_max := λ b ofs, by {
    rw PTree.gsspec,
    by_cases (b = m.nextblock); simp [h],
    simp [option.get_or_else, perm_order''.refl],
    apply m.access_max },
  nextblock_noaccess := λ b ofs k h, by {
    rw PTree.gsspec,
    note := nat.of_pos_num_le.1 h,
    rw nat.of_pos_num_succ_coe at this,
    by_cases (b = m.nextblock) with h'; simp [h'],
    { note := @not_le_of_gt nat _ _ _ this,
      rw h' at this, exact absurd (le_refl _) this },
    { apply m.nextblock_noaccess,
      exact le_of_lt (nat.of_pos_num_lt.2 this) } } }

/- Freeing a block between the given bounds.
  Return the updated memory state where the given range of the given block
  has been invalidated: future reads and writes to this
  range will fail.  Requires freeable permission on the given range. -/

def unchecked_free (m : mem) (b : block) (lo hi : ℕ) : mem :=
{ mem_contents       := m.mem_contents,
  mem_access         := option.cases_on (m.mem_access#b) m.mem_access $
    λ old, PTree.set b (λ ofs k, if lo ≤ ofs ∧ ofs < hi then none else old ofs k) m.mem_access,
  nextblock          := m.nextblock,
  access_max         := λ b' ofs, by {
    ginduction m.mem_access#b with h f; dsimp,
    { exact m.access_max b' ofs },
    { rw PTree.gsspec,
      note := m.access_max b' ofs,
      by_cases (b' = b) with bb; simp [bb, option.get_or_else]; simp [bb] at this,
      by_cases (lo ≤ ofs ∧ ofs < hi) with lh; simp [lh]; simp [h, option.get_or_else] at this,
      all_goals {exact this} } },
  nextblock_noaccess := λ b' ofs k hl, by {
    ginduction m.mem_access#b with h f; dsimp,
    { apply m.nextblock_noaccess ofs k hl },
    { rw PTree.gsspec,
      note := m.nextblock_noaccess ofs k hl,
      by_cases (b' = b) with bb; simp [bb, option.get_or_else],
      { simp [bb, h, option.get_or_else] at this,
        by_cases (lo ≤ ofs ∧ ofs < hi) with lh; simp [lh, this] },
      { exact this } } } }

def free (m : mem) (b : block) (lo hi : ℕ) : option mem :=
if range_perm m b lo hi Cur Freeable then some (unchecked_free m b lo hi) else none

def free_list : mem → list (block × ℕ × ℕ) → option mem
| m []                  := some m
| m ((b, lo, hi) :: l') := do m' ← free m b lo hi, free_list m' l'

/- Memory reads. -/

/- Reading N adjacent bytes in a block content. -/

def getN' (c : PTree.t memval) : ℕ → pos_num → list memval
| 0        p := []
| (n' + 1) p := (c#p).get_or_else Undef :: getN' n' p.succ

def getN (n p : ℕ) (c : PTree.t memval) : list memval :=
getN' c n (num.succ' p)

def get1 (p : ℕ) (c : PTree.t memval) : memval :=
(PTree.get (num.succ' p) c).get_or_else Undef

/- [load chunk m b ofs] perform a read in memory state [m], at address
  [b] and offset [ofs].  It returns the value of the memory chunk
  at that address.  [None] is returned if the accessed bytes
  are not readable. -/

def load (chunk : memory_chunk) (m : mem) (b : block) (ofs : ℕ) : option val :=
if valid_access m chunk b ofs Readable
then decode_val chunk $ getN chunk.size ofs (m.get_block b) else none

/- [loadv chunk m addr] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. -/

def loadv (chunk : memory_chunk) (m : mem) : val → option val
| (Vptr b ofs) := load chunk m b (unsigned ofs)
| _ := none

/- [load_bytes m b ofs n] reads [n] consecutive bytes starting at
  location [(b, ofs)].  Returns [None] if the accessed locations are
  not readable. -/

def load_bytes (m : mem) (b : block) (ofs n : ℕ) : option (list memval) :=
if range_perm m b ofs (ofs + n) Cur Readable then getN n ofs (m.get_block b) else none

/- Memory stores. -/

/- Writing N adjacent bytes in a block content. -/

def setN' : list memval → pos_num → PTree.t memval → PTree.t memval
| []         p c := c
| (v :: vl') p c := setN' vl' p.succ (PTree.set p v c)

def setN (vl : list memval) (ofs : ℕ) : PTree.t memval → PTree.t memval :=
setN' vl (num.succ' ofs)

theorem setN_other {vl c p q} : (∀ r, p ≤ r → r < p + list.length vl → r ≠ q) →
  get1 q (setN vl p c) = get1 q c := sorry

theorem setN_outside {vl c p q} : q < p ∨ q ≥ p + list.length vl →
  get1 q (setN vl p c) = get1 q c :=
by { intro h,
     apply setN_other,
     intros r h1 h2 hn,
     rw hn at h1 h2,
     cases h,
     { exact not_le_of_gt a h1 },
     { exact not_le_of_gt h2 a } }

theorem getN_setN_same {vl p c} : getN (list.length vl) p (setN vl p c) = vl := sorry

theorem getN.ext {c1 c2 n p} :
  (∀ i, p ≤ i → i < p + n → get1 i c1 = get1 i c2) →
  getN n p c1 = getN n p c2 := sorry

def interval_disjoint (x dx y dy : ℕ) := ∀ r, x ≤ r → r < x + dx → y ≤ r → r < y + dy → false

theorem getN_setN_disjoint {vl q c n p} :
  interval_disjoint p n q (list.length vl) → getN n p (setN vl q c) = getN n p c := sorry

theorem getN_setN_outside {vl q c n p} :
  p + n ≤ q ∨ q + list.length vl ≤ p → getN n p (setN vl q c) = getN n p c :=
by { intro h,
     apply getN_setN_disjoint,
     intros r hx hdx hy hdy,
     cases h,
     { exact not_le_of_gt hdx (le_trans a hy) },
     { exact not_le_of_gt hdy (le_trans a hx) } }

/- [store chunk m b ofs v] perform a write in memory state [m].
  Value [v] is stored at address [b] and offset [ofs].
  Return the updated memory store, or [None] if the accessed bytes
  are not writable. -/

def store.val (chunk : memory_chunk) (m : mem) (b : block) (ofs : ℕ) (v : val) : mem :=
{ mem_contents       := PTree.set b (setN (encode_val chunk v) ofs (m.get_block b)) m.mem_contents,
  mem_access         := m.mem_access,
  nextblock          := m.nextblock,
  access_max         := m.access_max,
  nextblock_noaccess := m.nextblock_noaccess }

def store (chunk : memory_chunk) (m : mem) (b : block) (ofs : ℕ) (v : val) : option mem :=
bnot (valid_access m chunk b ofs Writable) |> store.val chunk m b ofs v

/- [storev chunk m addr v] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. -/

def storev (chunk : memory_chunk) (m : mem) : val → val → option mem
| (Vptr b ofs) v := store chunk m b (unsigned ofs) v
| _            v := none

/- [store_bytes m b ofs bytes] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable. -/

def store_bytes (m : mem) (b : block) (ofs : ℕ) (bytes : list memval) : option mem :=
bnot (range_perm m b ofs (ofs + bytes.length) Cur Writable) |>
{ mem_contents       := PTree.set b (setN bytes ofs (m.get_block b)) m.mem_contents,
  mem_access         := m.mem_access,
  nextblock          := m.nextblock,
  access_max         := m.access_max,
  nextblock_noaccess := m.nextblock_noaccess }

/- [drop_perm m b lo hi p] sets the max permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have current permissions
    [Freeable] in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions. -/

def drop_perm (m : mem) (b : block) (lo hi : ℕ) (p : permission) : option mem :=
if rp : range_perm m b lo hi Cur Freeable then some
{ mem_contents       := m.mem_contents,
  mem_access         := option.cases_on (m.mem_access#b) m.mem_access $
    λ old, PTree.set b (λ ofs k, if lo ≤ ofs ∧ ofs < hi then some p else old ofs k) m.mem_access,
  nextblock          := m.nextblock,
  access_max         := λ b' ofs, by {
    ginduction m.mem_access#b with h f; dsimp,
    { exact m.access_max b' ofs },
    { rw PTree.gsspec,
      note := m.access_max b' ofs,
      by_cases (b' = b) with bb; simp [bb, option.get_or_else]; simp [bb] at this,
      { by_cases (lo ≤ ofs ∧ ofs < hi) with lh; simp [lh]; simp [h, option.get_or_else] at this,
        { apply perm_order''.refl },
        { assumption } },
      { exact this } } },
  nextblock_noaccess := λ b' ofs k hb, by {
    ginduction m.mem_access#b with h f; dsimp,
    { apply m.nextblock_noaccess ofs k hb },
    { rw PTree.gsspec,
      by_cases (b' = b) with bb; simp [bb, option.get_or_else],
      { by_cases (lo ≤ ofs ∧ ofs < hi) with lh,
        { cases lh with hl hh,
          apply absurd (rp hl hh),
          note := m.nextblock_noaccess ofs Cur hb,
          simp [bb, h, option.get_or_else] at this,
          simp [perm, mem.access, h, option.get_or_else, this],
          exact not_false },
        { note := m.nextblock_noaccess ofs k hb,
          simp [bb, h, option.get_or_else] at this,
          simp [lh, this] } },
      { exact m.nextblock_noaccess ofs k hb } } } }
else none

/- * Properties of the memory operations -/

/- Properties of the empty store. -/

theorem nextblock_empty : (∅ : mem).nextblock = 1 := rfl

theorem perm_empty {b ofs k p} : ¬ perm ∅ b ofs k p := id

theorem valid_access_empty {chunk b ofs p} : ¬ valid_access ∅ chunk b ofs p :=
mt (valid_access_perm Cur) perm_empty

/- ** Properties related to [load] -/

theorem valid_access_load {m chunk b ofs}
  (h : valid_access m chunk b ofs Readable) : ∃ v, load chunk m b ofs = some v :=
⟨_, by unfold load; rw if_pos h; refl⟩

theorem load_valid_access {m chunk b ofs v}
  (h : load chunk m b ofs = some v) : valid_access m chunk b ofs Readable :=
by unfold load at h; by_contradiction; simp [a] at h; contradiction

lemma load_result {chunk m b ofs v}
  (h : load chunk m b ofs = some v) : v = decode_val chunk (getN chunk.size ofs (m.get_block b)) :=
by { simp [load, load_valid_access h] at h,
     note := show _ = some _, from h.symm,
     injection this, assumption }

theorem load_type {m chunk b ofs v} (h : load chunk m b ofs = some v) : v.has_type chunk.type :=
by rw load_result h; apply decode_val_type

theorem load_cast {m chunk b ofs v} (h : load chunk m b ofs = some v) : decode_val_cast_type v chunk :=
by rw load_result h; apply decode_val_cast

theorem load_int8_signed_unsigned {m b ofs} :
  load Mint8signed m b ofs = sign_ext W8 <$> load Mint8unsigned m b ofs := sorry

theorem load_int16_signed_unsigned {m b ofs} :
  load Mint16signed m b ofs = sign_ext W16 <$> load Mint16unsigned m b ofs := sorry

/- ** Properties related to [load_bytes] -/

theorem range_perm_load_bytes {m b ofs len}
  (h : range_perm m b ofs (ofs + len) Cur Readable) : ∃ bytes, load_bytes m b ofs len = some bytes :=
⟨_, by unfold load_bytes; rw if_pos h; refl⟩

theorem load_bytes_range_perm {m b ofs len bytes}
  (h : load_bytes m b ofs len = some bytes) : range_perm m b ofs (ofs + len) Cur Readable :=
by unfold load_bytes at h; by_contradiction; simp [a] at h; contradiction

theorem load_bytes_getN {m b ofs n bytes}
  (h : load_bytes m b ofs n = some bytes) :
  getN n ofs (mem.get_block m b) = bytes :=
by { note := load_bytes_range_perm h,
     unfold load valid_access,
     unfold load_bytes at h,
     note := show some _ = _, by simp [this] at h; exact h,
     injection this with this,
     assumption }

theorem load_bytes_load {chunk m b ofs bytes}
  (h : load_bytes m b ofs (memory_chunk.size chunk) = some bytes) (al : chunk.align ∣ ofs) :
  load chunk m b ofs = some (decode_val chunk bytes) :=
by { note := load_bytes_range_perm h,
     unfold load valid_access,
     rw if_pos,
     { rw load_bytes_getN h; refl },
     { constructor; assumption } }

theorem load_load_bytes {chunk m b ofs v} (h : load chunk m b ofs = some v) :
  ∃ bytes, load_bytes m b ofs chunk.size = some bytes ∧ v = decode_val chunk bytes :=
let ⟨rp, al⟩ := load_valid_access h, ⟨bytes, h'⟩ := range_perm_load_bytes rp in
⟨bytes, h', option.no_confusion (h.symm.trans (load_bytes_load h' al)) id⟩

lemma getN_length {c n p} : (getN n p c).length = n :=
by delta getN; generalize (num.succ' p) p; induction n; intro p; simph [getN']

theorem load_bytes_length {m b ofs n bytes}
  (h : load_bytes m b ofs n = some bytes) : bytes.length = n :=
by rw [-load_bytes_getN h, getN_length]

theorem load_bytes_empty {m b ofs} : load_bytes m b ofs 0 = some [] :=
by {delta load_bytes, rw if_pos, refl, intros r h1 h2, exact absurd h1 (not_le_of_gt h2)}

lemma getN_concat {c n1 n2 p} : getN (n1 + n2) p c = getN n1 p c ++ getN n2 (p + n1) c := sorry

theorem load_bytes_concat {m b ofs n1 n2 bytes1 bytes2} :
  load_bytes m b ofs n1 = some bytes1 →
  load_bytes m b (ofs + n1) n2 = some bytes2 →
  load_bytes m b ofs (n1 + n2) = some (bytes1 ++ bytes2) := sorry

theorem load_bytes_split {m b ofs n1 n2 bytes} :
  load_bytes m b ofs (n1 + n2) = some bytes →
  ∃ bytes1, ∃ bytes2,
     load_bytes m b ofs n1 = some bytes1
  ∧ load_bytes m b (ofs + n1) n2 = some bytes2
  ∧ bytes = bytes1 ++ bytes2 := sorry

theorem load_rep {ch : memory_chunk} {m1 m2 : mem} {b ofs v1 v2} :
  (∀ z < ch.size, get1 (ofs + z) (m1.get_block b) = get1 (ofs + z) (m2.get_block b)) →
  load ch m1 b ofs = some v1 → load ch m2 b ofs = some v2 → v1 = v2 := sorry

theorem load_int64_split {m b ofs v} :
  load Mint64 m b ofs = some v → ¬ archi.ptr64 →
  ∃ v1 v2,
     load Mint32 m b ofs = some (if archi.big_endian then v1 else v2)
  ∧ load Mint32 m b (ofs + 4) = some (if archi.big_endian then v2 else v1)
  ∧ lessdef v (long_of_words v1 v2) := sorry

lemma addressing_int64_split {i : ptrofs} : ¬ archi.ptr64 → 8 ∣ unsigned i →
  unsigned (i + ptrofs.of_int (repr 4)) = unsigned i + 4 := sorry

theorem loadv_int64_split {m a v} : loadv Mint64 m a = some v → ¬ archi.ptr64 →
  ∃ v1 v2,
     loadv Mint32 m a = some (if archi.big_endian then v1 else v2)
  ∧ loadv Mint32 m (a + Vint (repr 4)) = some (if archi.big_endian then v2 else v1)
  ∧ lessdef v (long_of_words v1 v2) := sorry

/- ** Properties related to [store] -/

def valid_access_store {m1 chunk b ofs v}
  (h : valid_access m1 chunk b ofs Writable) : { m2 : mem // store chunk m1 b ofs v = some m2 } :=
⟨_, by unfold store; rw to_bool_tt h; refl⟩

section store
parameters {chunk : memory_chunk} {m1 m2 : mem} {b : block} {ofs : ℕ} {v : val}
parameter (STORE : store chunk m1 b ofs v = some m2)
include STORE

lemma store_val_eq : m2 = store.val chunk m1 b ofs v :=
by {unfold store at STORE, cases to_bool (valid_access m1 chunk b ofs Writable); try {contradiction},
    simp [option.rhoare] at STORE, injection STORE, exact h.symm}

lemma store_access : m2.mem_access = m1.mem_access :=
by rw store_val_eq STORE; refl

lemma store_mem_contents :
  m2.mem_contents = PTree.set b (setN (encode_val chunk v) ofs (m1.get_block b)) m1.mem_contents :=
by rw store_val_eq STORE; refl

theorem perm_store {b' ofs' k p} : perm m2 b' ofs' k p ↔ perm m1 b' ofs' k p :=
by unfold perm mem.access; rw store_access STORE; exact iff.rfl

theorem nextblock_store : m2.nextblock = m1.nextblock :=
by rw store_val_eq STORE; refl

theorem store_valid_block {b'} : valid_block m2 b' ↔ valid_block m1 b' :=
by unfold valid_block; rw nextblock_store STORE; exact iff.rfl

theorem store_valid_access {chunk' b' ofs' p} :
  valid_access m2 chunk' b' ofs' p ↔ valid_access m1 chunk' b' ofs' p :=
and_congr (forall_congr $ λ_, forall_congr $ λ_, forall_congr $ λ_, perm_store) iff.rfl

theorem store_valid_access' : valid_access m1 chunk b ofs Writable :=
by unfold store at STORE; by_contradiction; rw to_bool_ff a at STORE; contradiction

theorem load_store_similar {chunk' : memory_chunk} :
  chunk'.size = chunk.size → chunk'.align ≤ chunk.align →
  ∃ v', load chunk' m2 b ofs = some v' ∧ decode_encode_val v chunk chunk' v' := sorry

theorem load_store_similar_2 {chunk' : memory_chunk} :
  chunk'.size = chunk.size → chunk'.align ≤ chunk.align → chunk'.type = chunk.type →
  load chunk' m2 b ofs = some (val.load_result chunk' v) :=
λ hs ha ht, let ⟨v', h1, ed⟩ := load_store_similar hs ha in
by rw [h1, decode_encode_val_similar ed ht.symm hs.symm]

theorem load_store_same : load chunk m2 b ofs = some (val.load_result chunk v) :=
load_store_similar_2 rfl (le_refl _) rfl

theorem load_store_other {chunk' : memory_chunk} {b' ofs'} :
  b' ≠ b ∨ ofs' + chunk'.size ≤ ofs ∨ ofs + chunk.size ≤ ofs' →
  load chunk' m2 b' ofs' = load chunk' m1 b' ofs' := sorry

theorem load_bytes_store_same : load_bytes m2 b ofs chunk.size = some (encode_val chunk v) := sorry

theorem load_bytes_store_other {b' ofs' n} :
  b' ≠ b ∨ n = 0 ∨ ofs' + n ≤ ofs ∨ ofs + chunk.size ≤ ofs' →
  load_bytes m2 b' ofs' n = load_bytes m1 b' ofs' n := sorry

lemma setN_in {vl p q c} : p ≤ q → q < p + list.length vl → get1 q (setN vl p c) ∈ vl := sorry

lemma getN_in {c q n p} : p ≤ q → q < p + n → get1 q c ∈ getN n p c := sorry

end store

lemma load_store_overlap {chunk m1 b ofs v m2 chunk' ofs' v'} :
  store chunk m1 b ofs v = some m2 → load chunk' m2 b ofs' = some v' →
  ofs' + chunk'.size > ofs → ofs + chunk.size > ofs' →
  ∃ mv1 mvl mv1' mvl',
      shape_encoding chunk v (mv1 :: mvl)
  ∧  shape_decoding chunk' (mv1' :: mvl') v'
  ∧  (   (ofs' = ofs ∧ mv1' = mv1)
       ∨ (ofs' > ofs ∧ mv1' ∈ mvl)
       ∨ (ofs' < ofs ∧ mv1 ∈ mvl')) := sorry

def compat_pointer_chunks : memory_chunk → memory_chunk → bool
| Mint32 Mint32 := tt
| Mint32 Many32 := tt
| Many32 Mint32 := tt
| Many32 Many32 := tt
| Mint64 Mint64 := tt
| Mint64 Many64 := tt
| Many64 Mint64 := tt
| Many64 Many64 := tt
| _      _      := ff

lemma compat_pointer_chunks_true {chunk1 chunk2} :
  (chunk1 = Mint32 ∨ chunk1 = Many32 ∨ chunk1 = Mint64 ∨ chunk1 = Many64) →
  (chunk2 = Mint32 ∨ chunk2 = Many32 ∨ chunk2 = Mint64 ∨ chunk2 = Many64) →
  quantity_chunk chunk1 = quantity_chunk chunk2 → compat_pointer_chunks chunk1 chunk2 :=
by cases chunk1; cases chunk2; exact dec_trivial

theorem load_pointer_store {chunk m1 b ofs v m2 chunk' b' ofs' vb vo} :
  store chunk m1 b ofs v = some m2 →
  load chunk' m2 b' ofs' = some (Vptr vb vo) →
  (v = Vptr vb vo ∧ compat_pointer_chunks chunk chunk' ∧ b' = b ∧ ofs' = ofs)
  ∨ (b' ≠ b ∨ ofs' + chunk'.size ≤ ofs ∨ ofs + chunk.size ≤ ofs') := sorry

theorem load_store_pointer_overlap {chunk m1 b ofs vb vo m2 chunk' ofs' v} :
  store chunk m1 b ofs (Vptr vb vo) = some m2 → load chunk' m2 b ofs' = some v →
  ofs' ≠ ofs → ofs' + chunk'.size > ofs → ofs + chunk.size > ofs' → v = Vundef := sorry

theorem load_store_pointer_mismatch {chunk m1 b ofs vb vo m2 chunk' v} :
  store chunk m1 b ofs (Vptr vb vo) = some m2 → load chunk' m2 b ofs = some v →
  ¬ compat_pointer_chunks chunk chunk' → v = Vundef := sorry

lemma store_similar_chunks {chunk1 chunk2 v1 v2 m b ofs} :
  encode_val chunk1 v1 = encode_val chunk2 v2 → chunk1.align = chunk2.align →
  store chunk1 m b ofs v1 = store chunk2 m b ofs v2 := sorry

theorem store_signed_unsigned_8 {m b ofs v} :
  store Mint8signed m b ofs v = store Mint8unsigned m b ofs v := sorry

theorem store_signed_unsigned_16 {m b ofs v} :
  store Mint16signed m b ofs v = store Mint16unsigned m b ofs v := sorry

theorem store_int8_zero_ext {m b ofs n} :
  store Mint8unsigned m b ofs (Vint (zero_ext 8 n)) =
  store Mint8unsigned m b ofs (Vint n) := sorry

theorem store_int8_sign_ext {m b ofs n} :
  store Mint8signed m b ofs (Vint (sign_ext W8 n)) =
  store Mint8signed m b ofs (Vint n) := sorry

theorem store_int16_zero_ext {m b ofs n} :
  store Mint16unsigned m b ofs (Vint (zero_ext 16 n)) =
  store Mint16unsigned m b ofs (Vint n) := sorry

theorem store_int16_sign_ext {m b ofs n} :
  store Mint16signed m b ofs (Vint (sign_ext W16 n)) =
  store Mint16signed m b ofs (Vint n) := sorry


/- ** Properties related to [store_bytes]. -/

theorem range_perm_store_bytes {m1 b ofs bytes}
  (h : range_perm m1 b ofs (ofs + list.length bytes) Cur Writable) :
  { m2 : mem // store_bytes m1 b ofs bytes = some m2 } :=
⟨_, by unfold store_bytes; rw to_bool_tt h; refl⟩

theorem store_bytes_store {m1 b ofs chunk v m2} :
  store_bytes m1 b ofs (encode_val chunk v) = some m2 →
  chunk.align ∣ ofs → store chunk m1 b ofs v = some m2 := sorry

theorem store_store_bytes {m1 b ofs chunk v m2} :
  store chunk m1 b ofs v = some m2 →
  store_bytes m1 b ofs (encode_val chunk v) = some m2 := sorry

section store_bytes
parameter m1 : mem
parameter b : block
parameter ofs : ℤ
parameter bytes : list memval
parameter m2 : mem
Hypothesis STORE : store_bytes m1 b ofs bytes = some m2

lemma store_bytes_access : mem_access m2 = mem_access m1
Proof
  unfold store_bytes in STORE
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  inv STORE
  auto
Qed

lemma store_bytes_mem_contents :
   mem_contents m2 = PTree.set b (setN bytes ofs m1.(mem_contents)#b) m1.(mem_contents)
Proof
  unfold store_bytes in STORE
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  inv STORE
  auto
Qed

theorem perm_store_bytes_1 :
  ∀ b' ofs' k p, perm m1 b' ofs' k p → perm m2 b' ofs' k p
Proof
  intros. unfold perm in *. rewrite store_bytes_access; auto
Qed

theorem perm_store_bytes_2 :
  ∀ b' ofs' k p, perm m2 b' ofs' k p → perm m1 b' ofs' k p
Proof
  intros. unfold perm in *. rewrite store_bytes_access in H; auto
Qed

Local Hint Resolve perm_store_bytes_1 perm_store_bytes_2 : mem

theorem store_bytes_valid_access_1 :
  ∀ chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p → valid_access m2 chunk' b' ofs' p
Proof
  intros. inv H. constructor; try red; auto with mem
Qed

theorem store_bytes_valid_access_2 :
  ∀ chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p → valid_access m1 chunk' b' ofs' p
Proof
  intros. inv H. constructor; try red; auto with mem
Qed

Local Hint Resolve store_bytes_valid_access_1 store_bytes_valid_access_2 : mem

theorem nextblock_store_bytes :
  nextblock m2 = nextblock m1
Proof
  intros
  unfold store_bytes in STORE
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  inv STORE
  auto
Qed

theorem store_bytes_valid_block_1 :
  ∀ b', valid_block m1 b' → valid_block m2 b'
Proof
  unfold valid_block; intros. rewrite nextblock_store_bytes; auto
Qed

theorem store_bytes_valid_block_2 :
  ∀ b', valid_block m2 b' → valid_block m1 b'
Proof
  unfold valid_block; intros. rewrite nextblock_store_bytes in H; auto
Qed

Local Hint Resolve store_bytes_valid_block_1 store_bytes_valid_block_2 : mem

theorem store_bytes_range_perm :
  range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable
Proof
  intros
  unfold store_bytes in STORE
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  inv STORE
  auto
Qed

theorem load_bytes_store_bytes_same :
  load_bytes m2 b ofs (Z_of_nat (length bytes)) = some bytes
Proof
  intros. assert (STORE2:=STORE). unfold store_bytes in STORE2. unfold load_bytes. 
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  try discriminate
  rewrite pred_dec_true
  decEq. inv STORE2; simpl. rewrite PTree.gss. rewrite nat_of_Z_of_nat
  apply getN_setN_same
  red; eauto with mem
Qed

theorem load_bytes_store_bytes_disjoint :
  ∀ b' ofs' len,
  len >= 0 →
  b' ≠ b ∨ Intv.disjoint (ofs', ofs' + len) (ofs, ofs + Z_of_nat (length bytes)) →
  load_bytes m2 b' ofs' len = load_bytes m1 b' ofs' len
Proof
  intros. unfold load_bytes
  destruct (range_perm_dec m1 b' ofs' (ofs' + len) Cur Readable)
  rewrite pred_dec_true
  rewrite store_bytes_mem_contents. decEq
  rewrite PTree.gsspec. destruct (peq b' b). subst b'
  apply getN_setN_disjoint. rewrite nat_of_Z_eq; auto. intuition congruence
  auto
  red; auto with mem
  apply pred_dec_false
  red; intros; elim n. red; auto with mem
Qed

theorem load_bytes_store_bytes_other :
  ∀ b' ofs' len,
  len >= 0 →
  b' ≠ b
  ∨ ofs' + len <= ofs
  ∨ ofs + Z_of_nat (length bytes) <= ofs' →
  load_bytes m2 b' ofs' len = load_bytes m1 b' ofs' len
Proof
  intros. apply load_bytes_store_bytes_disjoint; auto
  destruct H0; auto. right. apply Intv.disjoint_range; auto
Qed

theorem load_store_bytes_other :
  ∀ chunk b' ofs',
  b' ≠ b
  ∨ ofs' + size_chunk chunk <= ofs
  ∨ ofs + Z_of_nat (length bytes) <= ofs' →
  load chunk m2 b' ofs' = load chunk m1 b' ofs'
Proof
  intros. unfold load
  destruct (valid_access_dec m1 chunk b' ofs' Readable)
  rewrite pred_dec_true
  rewrite store_bytes_mem_contents. decEq
  rewrite PTree.gsspec. destruct (peq b' b). subst b'
  rewrite getN_setN_outside. auto. rewrite <- size_chunk_conv. intuition congruence
  auto
  destruct v; split; auto. red; auto with mem
  apply pred_dec_false
  red; intros; elim n. destruct H0. split; auto. red; auto with mem
Qed

end STOREBYTES

lemma setN_concat :
  ∀ bytes1 bytes2 ofs c,
  setN (bytes1 ++ bytes2) ofs c = setN bytes2 (ofs + Z_of_nat (length bytes1)) (setN bytes1 ofs c)
Proof
  induction bytes1; intros
  simpl. decEq. omega
  simpl length. rewrite inj_S. simpl. rewrite IHbytes1. decEq. omega
Qed

theorem store_bytes_concat :
  ∀ m b ofs bytes1 m1 bytes2 m2,
  store_bytes m b ofs bytes1 = some m1 →
  store_bytes m1 b (ofs + Z_of_nat(length bytes1)) bytes2 = some m2 →
  store_bytes m b ofs (bytes1 ++ bytes2) = some m2
Proof
  intros. generalize H; intro ST1. generalize H0; intro ST2
  unfold store_bytes; unfold store_bytes in ST1; unfold store_bytes in ST2
  destruct (range_perm_dec m b ofs (ofs + Z_of_nat(length bytes1)) Cur Writable); try congruence
  destruct (range_perm_dec m1 b (ofs + Z_of_nat(length bytes1)) (ofs + Z_of_nat(length bytes1) + Z_of_nat(length bytes2)) Cur Writable); try congruence
  destruct (range_perm_dec m b ofs (ofs + Z_of_nat (length (bytes1 ++ bytes2))) Cur Writable)
  inv ST1; inv ST2; simpl. decEq. apply mkmem_ext; auto
  rewrite PTree.gss.  rewrite setN_concat. symmetry. apply PTree.set2
  elim n
  rewrite app_length. rewrite inj_plus. red; intros
  destruct (zlt ofs0 (ofs + Z_of_nat(length bytes1)))
  apply r. omega
  eapply perm_store_bytes_2; eauto. apply r0. omega
Qed

theorem store_bytes_split :
  ∀ m b ofs bytes1 bytes2 m2,
  store_bytes m b ofs (bytes1 ++ bytes2) = some m2 →
  ∃ m1,
     store_bytes m b ofs bytes1 = some m1
  ∧ store_bytes m1 b (ofs + Z_of_nat(length bytes1)) bytes2 = some m2
Proof
  intros
  destruct (range_perm_store_bytes m b ofs bytes1) as [m1 ST1]
  red; intros. exploit store_bytes_range_perm; eauto. rewrite app_length
  rewrite inj_plus. omega
  destruct (range_perm_store_bytes m1 b (ofs + Z_of_nat (length bytes1)) bytes2) as [m2' ST2]
  red; intros. eapply perm_store_bytes_1; eauto. exploit store_bytes_range_perm
  eexact H. instantiate (1 := ofs0). rewrite app_length. rewrite inj_plus. omega
  auto
  assert (some m2 = some m2')
  rewrite <- H. eapply store_bytes_concat; eauto
  inv H0
  ∃ m1; split; auto
Qed

theorem store_int64_split :
  ∀ m b ofs v m',
  store Mint64 m b ofs v = some m' → Archi.ptr64 = ff →
  ∃ m1,
     store Mint32 m b ofs (if Archi.big_endian then Val.hiword v else Val.loword v) = some m1
  ∧ store Mint32 m1 b (ofs + 4) (if Archi.big_endian then Val.loword v else Val.hiword v) = some m'
Proof
  intros
  exploit store_valid_access_3; eauto. intros [A B]. simpl in *
  exploit store_store_bytes. eexact H. intros SB
  rewrite encode_val_int64 in SB by auto
  exploit store_bytes_split. eexact SB. intros [m1 [SB1 SB2]]
  rewrite encode_val_length in SB2. simpl in SB2
  ∃ m1; split
  apply store_bytes_store. exact SB1
  simpl. apply Zdivides_trans with 8; auto. ∃ 2; auto
  apply store_bytes_store. exact SB2
  simpl. apply Zdivide_plus_r. apply Zdivides_trans with 8; auto. ∃ 2; auto. ∃ 1; auto
Qed

theorem storev_int64_split :
  ∀ m a v m',
  storev Mint64 m a v = some m' → Archi.ptr64 = ff →
  ∃ m1,
     storev Mint32 m a (if Archi.big_endian then Val.hiword v else Val.loword v) = some m1
  ∧ storev Mint32 m1 (Val.add a (Vint (Int.repr 4))) (if Archi.big_endian then Val.loword v else Val.hiword v) = some m'
Proof
  intros. destruct a; simpl in H; inv H. rewrite H2
  exploit store_int64_split; eauto. intros [m1 [A B]]
  ∃ m1; split
  exact A
  unfold storev, Val.add. rewrite H0
  rewrite addressing_int64_split; auto
  exploit store_valid_access_3. eexact H2. intros [P Q]. exact Q
Qed

#exit
/- ** Properties related to [alloc]. -/

section ALLOC

parameter m1 : mem
Variables lo hi : ℤ
parameter m2 : mem
parameter b : block
Hypothesis ALLOC : alloc m1 lo hi = (m2, b)

theorem nextblock_alloc :
  nextblock m2 = Psucc (nextblock m1)
Proof
  injection ALLOC; intros. rewrite <- H0; auto
Qed

theorem alloc_result :
  b = nextblock m1
Proof
  injection ALLOC; auto
Qed

theorem valid_block_alloc :
  ∀ b', valid_block m1 b' → valid_block m2 b'
Proof
  unfold valid_block; intros. rewrite nextblock_alloc
  apply Plt_trans_succ; auto
Qed

theorem fresh_block_alloc :
  ~(valid_block m1 b)
Proof
  unfold valid_block. rewrite alloc_result. apply Plt_strict
Qed

theorem valid_new_block :
  valid_block m2 b
Proof
  unfold valid_block. rewrite alloc_result. rewrite nextblock_alloc. apply Plt_succ
Qed

Local Hint Resolve valid_block_alloc fresh_block_alloc valid_new_block : mem

theorem valid_block_alloc_inv :
  ∀ b', valid_block m2 b' → b' = b ∨ valid_block m1 b'
Proof
  unfold valid_block; intros
  rewrite nextblock_alloc in H. rewrite alloc_result
  exploit Plt_succ_inv; eauto. tauto
Qed

theorem perm_alloc_1 :
  ∀ b' ofs k p, perm m1 b' ofs k p → perm m2 b' ofs k p
Proof
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl
  subst b. rewrite PTree.gsspec. destruct (peq b' (nextblock m1)); auto
  rewrite nextblock_noaccess in H. contradiction. subst b'. apply Plt_strict
Qed

theorem perm_alloc_2 :
  ∀ ofs k, lo <= ofs < hi → perm m2 b ofs k Freeable
Proof
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl
  subst b. rewrite PTree.gss. unfold proj_sumbool. rewrite zle_true
  rewrite zlt_true. simpl. auto with mem. omega. omega
Qed

theorem perm_alloc_inv :
  ∀ b' ofs k p,
  perm m2 b' ofs k p →
  if eq_block b' b then lo <= ofs < hi else perm m1 b' ofs k p
Proof
  intros until p; unfold perm. inv ALLOC. simpl
  rewrite PTree.gsspec. unfold eq_block. destruct (peq b' (nextblock m1)); intros
  destruct (zle lo ofs); try contradiction. destruct (zlt ofs hi); try contradiction
  split; auto
  auto
Qed

theorem perm_alloc_3 :
  ∀ ofs k p, perm m2 b ofs k p → lo <= ofs < hi
Proof
  intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_true; auto
Qed

theorem perm_alloc_4 :
  ∀ b' ofs k p, perm m2 b' ofs k p → b' ≠ b → perm m1 b' ofs k p
Proof
  intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_false; auto
Qed

Local Hint Resolve perm_alloc_1 perm_alloc_2 perm_alloc_3 perm_alloc_4 : mem

theorem valid_access_alloc_other :
  ∀ chunk b' ofs p,
  valid_access m1 chunk b' ofs p →
  valid_access m2 chunk b' ofs p
Proof
  intros. inv H. constructor; auto with mem
  red; auto with mem
Qed

theorem valid_access_alloc_same :
  ∀ chunk ofs,
  lo <= ofs → ofs + size_chunk chunk <= hi → (align_chunk chunk | ofs) →
  valid_access m2 chunk b ofs Freeable
Proof
  intros. constructor; auto with mem
  red; intros. apply perm_alloc_2. omega
Qed

Local Hint Resolve valid_access_alloc_other valid_access_alloc_same : mem

theorem valid_access_alloc_inv :
  ∀ chunk b' ofs p,
  valid_access m2 chunk b' ofs p →
  if eq_block b' b
  then lo <= ofs ∧ ofs + size_chunk chunk <= hi ∧ (align_chunk chunk | ofs)
  else valid_access m1 chunk b' ofs p
Proof
  intros. inv H
  generalize (size_chunk_pos chunk); intro
  destruct (eq_block b' b). subst b'
  assert (perm m2 b ofs Cur p). apply H0. omega
  assert (perm m2 b (ofs + size_chunk chunk - 1) Cur p). apply H0. omega
  exploit perm_alloc_inv. eexact H2. rewrite dec_eq_true. intro
  exploit perm_alloc_inv. eexact H3. rewrite dec_eq_true. intro
  intuition omega
  split; auto. red; intros
  exploit perm_alloc_inv. apply H0. eauto. rewrite dec_eq_false; auto
Qed

theorem load_alloc_unchanged :
  ∀ chunk b' ofs,
  valid_block m1 b' →
  load chunk m2 b' ofs = load chunk m1 b' ofs
Proof
  intros. unfold load
  destruct (valid_access_dec m2 chunk b' ofs Readable)
  exploit valid_access_alloc_inv; eauto. destruct (eq_block b' b); intros
  subst b'. elimtype false. eauto with mem
  rewrite pred_dec_true; auto
  injection ALLOC; intros. rewrite <- H2; simpl
  rewrite PTree.gso. auto. rewrite H1. apply sym_not_equal; eauto with mem
  rewrite pred_dec_false. auto
  eauto with mem
Qed

theorem load_alloc_other :
  ∀ chunk b' ofs v,
  load chunk m1 b' ofs = some v →
  load chunk m2 b' ofs = some v
Proof
  intros. rewrite <- H. apply load_alloc_unchanged. eauto with mem
Qed

theorem load_alloc_same :
  ∀ chunk ofs v,
  load chunk m2 b ofs = some v →
  v = Vundef
Proof
  intros. exploit load_result; eauto. intro. rewrite H0
  injection ALLOC; intros. rewrite <- H2; simpl. rewrite <- H1
  rewrite PTree.gss. destruct (size_chunk_nat_pos chunk) as [n E]. rewrite E. simpl
  rewrite ZMap.gi. apply decode_val_undef. 
Qed

theorem load_alloc_same' :
  ∀ chunk ofs,
  lo <= ofs → ofs + size_chunk chunk <= hi → (align_chunk chunk | ofs) →
  load chunk m2 b ofs = some Vundef
Proof
  intros. assert (∃ v, load chunk m2 b ofs = some v)
    apply valid_access_load. constructor; auto
    red; intros. eapply perm_implies. apply perm_alloc_2. omega. auto with mem
  destruct H2 as [v LOAD]. rewrite LOAD. decEq
  eapply load_alloc_same; eauto
Qed

theorem load_bytes_alloc_unchanged :
  ∀ b' ofs n,
  valid_block m1 b' →
  load_bytes m2 b' ofs n = load_bytes m1 b' ofs n
Proof
  intros. unfold load_bytes
  destruct (range_perm_dec m1 b' ofs (ofs + n) Cur Readable)
  rewrite pred_dec_true
  injection ALLOC; intros A B. rewrite <- B; simpl
  rewrite PTree.gso. auto. rewrite A. eauto with mem
  red; intros. eapply perm_alloc_1; eauto
  rewrite pred_dec_false; auto
  red; intros; elim n0. red; intros. eapply perm_alloc_4; eauto. eauto with mem
Qed

theorem load_bytes_alloc_same :
  ∀ n ofs bytes byte,
  load_bytes m2 b ofs n = some bytes →
  In byte bytes → byte = Undef
Proof
  unfold load_bytes; intros. destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable); inv H
  revert H0
  injection ALLOC; intros A B. rewrite <- A; rewrite <- B; simpl. rewrite PTree.gss
  generalize (nat_of_Z n) ofs. induction n0; simpl; intros
  contradiction
  rewrite ZMap.gi in H0. destruct H0; eauto
Qed

end ALLOC

Local Hint Resolve valid_block_alloc fresh_block_alloc valid_new_block : mem
Local Hint Resolve valid_access_alloc_other valid_access_alloc_same : mem

/- ** Properties related to [free]. -/

theorem range_perm_free :
  ∀ m1 b lo hi,
  range_perm m1 b lo hi Cur Freeable →
  { m2 : mem | free m1 b lo hi = some m2 }
Proof
  intros; unfold free. rewrite pred_dec_true; auto. econstructor; eauto
Defined

section FREE

parameter m1 : mem
parameter bf : block
Variables lo hi : ℤ
parameter m2 : mem
Hypothesis FREE : free m1 bf lo hi = some m2

theorem free_range_perm :
  range_perm m1 bf lo hi Cur Freeable
Proof
  unfold free in FREE. destruct (range_perm_dec m1 bf lo hi Cur Freeable); auto
  congruence
Qed

lemma free_result :
  m2 = unchecked_free m1 bf lo hi
Proof
  unfold free in FREE. destruct (range_perm_dec m1 bf lo hi Cur Freeable)
  congruence. congruence
Qed

theorem nextblock_free :
  nextblock m2 = nextblock m1
Proof
  rewrite free_result; reflexivity
Qed

theorem valid_block_free_1 :
  ∀ b, valid_block m1 b → valid_block m2 b
Proof
  intros. rewrite free_result. assumption
Qed

theorem valid_block_free_2 :
  ∀ b, valid_block m2 b → valid_block m1 b
Proof
  intros. rewrite free_result in H. assumption
Qed

Local Hint Resolve valid_block_free_1 valid_block_free_2 : mem

theorem perm_free_1 :
  ∀ b ofs k p,
  b ≠ bf ∨ ofs < lo ∨ hi <= ofs →
  perm m1 b ofs k p →
  perm m2 b ofs k p
Proof
  intros. rewrite free_result. unfold perm, unchecked_free; simpl
  rewrite PTree.gsspec. destruct (peq b bf). subst b
  destruct (zle lo ofs); simpl
  destruct (zlt ofs hi); simpl
  elimtype false; intuition
  auto. auto
  auto
Qed

theorem perm_free_2 :
  ∀ ofs k p, lo <= ofs < hi → ~ perm m2 bf ofs k p
Proof
  intros. rewrite free_result. unfold perm, unchecked_free; simpl
  rewrite PTree.gss. unfold proj_sumbool. rewrite zle_true. rewrite zlt_true
  simpl. tauto. omega. omega
Qed

theorem perm_free_3 :
  ∀ b ofs k p,
  perm m2 b ofs k p → perm m1 b ofs k p
Proof
  intros until p. rewrite free_result. unfold perm, unchecked_free; simpl
  rewrite PTree.gsspec. destruct (peq b bf). subst b
  destruct (zle lo ofs); simpl
  destruct (zlt ofs hi); simpl. tauto
  auto. auto. auto
Qed

theorem perm_free_inv :
  ∀ b ofs k p,
  perm m1 b ofs k p →
  (b = bf ∧ lo <= ofs < hi) ∨ perm m2 b ofs k p
Proof
  intros. rewrite free_result. unfold perm, unchecked_free; simpl
  rewrite PTree.gsspec. destruct (peq b bf); auto. subst b
  destruct (zle lo ofs); simpl; auto
  destruct (zlt ofs hi); simpl; auto
Qed

theorem valid_access_free_1 :
  ∀ chunk b ofs p,
  valid_access m1 chunk b ofs p →
  b ≠ bf ∨ lo >= hi ∨ ofs + size_chunk chunk <= lo ∨ hi <= ofs →
  valid_access m2 chunk b ofs p
Proof
  intros. inv H. constructor; auto with mem
  red; intros. eapply perm_free_1; eauto
  destruct (zlt lo hi). intuition. right. omega
Qed

theorem valid_access_free_2 :
  ∀ chunk ofs p,
  lo < hi → ofs + size_chunk chunk > lo → ofs < hi →
  ~(valid_access m2 chunk bf ofs p)
Proof
  intros; red; intros. inv H2
  generalize (size_chunk_pos chunk); intros
  destruct (zlt ofs lo)
  elim (perm_free_2 lo Cur p)
  omega. apply H3. omega
  elim (perm_free_2 ofs Cur p)
  omega. apply H3. omega
Qed

theorem valid_access_free_inv_1 :
  ∀ chunk b ofs p,
  valid_access m2 chunk b ofs p →
  valid_access m1 chunk b ofs p
Proof
  intros. destruct H. split; auto
  red; intros. generalize (H ofs0 H1)
  rewrite free_result. unfold perm, unchecked_free; simpl
  rewrite PTree.gsspec. destruct (peq b bf). subst b
  destruct (zle lo ofs0); simpl
  destruct (zlt ofs0 hi); simpl
  tauto. auto. auto. auto
Qed

theorem valid_access_free_inv_2 :
  ∀ chunk ofs p,
  valid_access m2 chunk bf ofs p →
  lo >= hi ∨ ofs + size_chunk chunk <= lo ∨ hi <= ofs
Proof
  intros
  destruct (zlt lo hi); auto
  destruct (zle (ofs + size_chunk chunk) lo); auto
  destruct (zle hi ofs); auto
  elim (valid_access_free_2 chunk ofs p); auto. omega
Qed

theorem load_free :
  ∀ chunk b ofs,
  b ≠ bf ∨ lo >= hi ∨ ofs + size_chunk chunk <= lo ∨ hi <= ofs →
  load chunk m2 b ofs = load chunk m1 b ofs
Proof
  intros. unfold load
  destruct (valid_access_dec m2 chunk b ofs Readable)
  rewrite pred_dec_true
  rewrite free_result; auto
  eapply valid_access_free_inv_1; eauto
  rewrite pred_dec_false; auto
  red; intro; elim n. eapply valid_access_free_1; eauto
Qed

theorem load_free_2 :
  ∀ chunk b ofs v,
  load chunk m2 b ofs = some v → load chunk m1 b ofs = some v
Proof
  intros. unfold load. rewrite pred_dec_true
  rewrite (load_result _ _ _ _ _ H). rewrite free_result; auto
  apply valid_access_free_inv_1. eauto with mem
Qed

theorem load_bytes_free :
  ∀ b ofs n,
  b ≠ bf ∨ lo >= hi ∨ ofs + n <= lo ∨ hi <= ofs →
  load_bytes m2 b ofs n = load_bytes m1 b ofs n
Proof
  intros. unfold load_bytes
  destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable)
  rewrite pred_dec_true
  rewrite free_result; auto
  red; intros. eapply perm_free_3; eauto
  rewrite pred_dec_false; auto
  red; intros. elim n0; red; intros
  eapply perm_free_1; eauto. destruct H; auto. right; omega
Qed

theorem load_bytes_free_2 :
  ∀ b ofs n bytes,
  load_bytes m2 b ofs n = some bytes → load_bytes m1 b ofs n = some bytes
Proof
  intros. unfold load_bytes in *
  destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable); inv H
  rewrite pred_dec_true. rewrite free_result; auto
  red; intros. apply perm_free_3; auto
Qed

end FREE

Local Hint Resolve valid_block_free_1 valid_block_free_2
             perm_free_1 perm_free_2 perm_free_3
             valid_access_free_1 valid_access_free_inv_1 : mem

/- ** Properties related to [drop_perm] -/

theorem range_perm_drop_1 :
  ∀ m b lo hi p m', drop_perm m b lo hi p = some m' → range_perm m b lo hi Cur Freeable
Proof
  unfold drop_perm; intros
  destruct (range_perm_dec m b lo hi Cur Freeable). auto. discriminate
Qed

theorem range_perm_drop_2 :
  ∀ m b lo hi p,
  range_perm m b lo hi Cur Freeable → {m' | drop_perm m b lo hi p = some m' }
Proof
  unfold drop_perm; intros
  destruct (range_perm_dec m b lo hi Cur Freeable). econstructor. eauto. contradiction
Defined

section DROP

parameter m : mem
parameter b : block
parameter lo hi : ℤ
parameter p : permission
parameter m' : mem
Hypothesis DROP : drop_perm m b lo hi p = some m'

theorem nextblock_drop :
  nextblock m' = nextblock m
Proof
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP; auto
Qed

theorem drop_perm_valid_block_1 :
  ∀ b', valid_block m b' → valid_block m' b'
Proof
  unfold valid_block; rewrite nextblock_drop; auto
Qed

theorem drop_perm_valid_block_2 :
  ∀ b', valid_block m' b' → valid_block m b'
Proof
  unfold valid_block; rewrite nextblock_drop; auto
Qed

theorem perm_drop_1 :
  ∀ ofs k, lo <= ofs < hi → perm m' b ofs k p
Proof
  intros
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP
  unfold perm. simpl. rewrite PTree.gss. unfold proj_sumbool
  rewrite zle_true. rewrite zlt_true. simpl. constructor
  omega. omega
Qed

theorem perm_drop_2 :
  ∀ ofs k p', lo <= ofs < hi → perm m' b ofs k p' → perm_order p p'
Proof
  intros
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP
  revert H0. unfold perm; simpl. rewrite PTree.gss. unfold proj_sumbool
  rewrite zle_true. rewrite zlt_true. simpl. auto
  omega. omega
Qed

theorem perm_drop_3 :
  ∀ b' ofs k p', b' ≠ b ∨ ofs < lo ∨ hi <= ofs → perm m b' ofs k p' → perm m' b' ofs k p'
Proof
  intros
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP
  unfold perm; simpl. rewrite PTree.gsspec. destruct (peq b' b). subst b'
  unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi)
  byContradiction. intuition omega
  auto. auto. auto
Qed

theorem perm_drop_4 :
  ∀ b' ofs k p', perm m' b' ofs k p' → perm m b' ofs k p'
Proof
  intros
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP
  revert H. unfold perm; simpl. rewrite PTree.gsspec. destruct (peq b' b)
  subst b'. unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi)
  simpl. intros. apply perm_implies with p. apply perm_implies with Freeable. apply perm_cur
  apply r. tauto. auto with mem. auto
  auto. auto. auto
Qed

lemma valid_access_drop_1 :
  ∀ chunk b' ofs p',
  b' ≠ b ∨ ofs + size_chunk chunk <= lo ∨ hi <= ofs ∨ perm_order p p' →
  valid_access m chunk b' ofs p' → valid_access m' chunk b' ofs p'
Proof
  intros. destruct H0. split; auto
  red; intros
  destruct (eq_block b' b). subst b'
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto
  destruct (zle hi ofs0). eapply perm_drop_3; eauto
  apply perm_implies with p. eapply perm_drop_1; eauto. omega
  generalize (size_chunk_pos chunk); intros. intuition
  eapply perm_drop_3; eauto
Qed

lemma valid_access_drop_2 :
  ∀ chunk b' ofs p',
  valid_access m' chunk b' ofs p' → valid_access m chunk b' ofs p'
Proof
  intros. destruct H; split; auto
  red; intros. eapply perm_drop_4; eauto
Qed

theorem load_drop :
  ∀ chunk b' ofs,
  b' ≠ b ∨ ofs + size_chunk chunk <= lo ∨ hi <= ofs ∨ perm_order p Readable →
  load chunk m' b' ofs = load chunk m b' ofs
Proof
  intros
  unfold load
  destruct (valid_access_dec m chunk b' ofs Readable)
  rewrite pred_dec_true
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP. simpl. auto
  eapply valid_access_drop_1; eauto
  rewrite pred_dec_false. auto
  red; intros; elim n. eapply valid_access_drop_2; eauto
Qed

theorem load_bytes_drop :
  ∀ b' ofs n,
  b' ≠ b ∨ ofs + n <= lo ∨ hi <= ofs ∨ perm_order p Readable →
  load_bytes m' b' ofs n = load_bytes m b' ofs n
Proof
  intros
  unfold load_bytes
  destruct (range_perm_dec m b' ofs (ofs + n) Cur Readable)
  rewrite pred_dec_true
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP. simpl. auto
  red; intros
  destruct (eq_block b' b). subst b'
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto
  destruct (zle hi ofs0). eapply perm_drop_3; eauto
  apply perm_implies with p. eapply perm_drop_1; eauto. omega. intuition
  eapply perm_drop_3; eauto
  rewrite pred_dec_false; eauto
  red; intros; elim n0; red; intros
  eapply perm_drop_4; eauto
Qed

end DROP

/- * Generic injections -/

/- A memory state [m1] generically injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address.
-/

structure mem_inj (f : meminj) (m1 m2 : mem) : Prop :=
  mk_mem_inj {
    mi_perm :
      ∀ b1 b2 delta ofs k p,
      f b1 = some(b2, delta) →
      perm m1 b1 ofs k p →
      perm m2 b2 (ofs + delta) k p;
    mi_align :
      ∀ b1 b2 delta chunk ofs p,
      f b1 = some(b2, delta) →
      range_perm m1 b1 ofs (ofs + size_chunk chunk) Max p →
      (align_chunk chunk | delta);
    mi_memval :
      ∀ b1 ofs b2 delta,
      f b1 = some(b2, delta) →
      perm m1 b1 ofs Cur Readable →
      memval_inject f (ZMap.get ofs m1.(mem_contents)#b1) (ZMap.get (ofs+delta) m2.(mem_contents)#b2)
  }

/- Preservation of permissions -/

lemma perm_inj :
  ∀ f m1 m2 b1 ofs k p b2 delta,
  mem_inj f m1 m2 →
  perm m1 b1 ofs k p →
  f b1 = some(b2, delta) →
  perm m2 b2 (ofs + delta) k p
Proof
  intros. eapply mi_perm; eauto
Qed

lemma range_perm_inj :
  ∀ f m1 m2 b1 lo hi k p b2 delta,
  mem_inj f m1 m2 →
  range_perm m1 b1 lo hi k p →
  f b1 = some(b2, delta) →
  range_perm m2 b2 (lo + delta) (hi + delta) k p
Proof
  intros; red; intros
  replace ofs with ((ofs - delta) + delta) by omega
  eapply perm_inj; eauto. apply H0. omega
Qed

lemma valid_access_inj :
  ∀ f m1 m2 b1 b2 delta chunk ofs p,
  mem_inj f m1 m2 →
  f b1 = some(b2, delta) →
  valid_access m1 chunk b1 ofs p →
  valid_access m2 chunk b2 (ofs + delta) p
Proof
  intros. destruct H1 as [A B]. constructor
  replace (ofs + delta + size_chunk chunk)
     with ((ofs + size_chunk chunk) + delta) by omega
  eapply range_perm_inj; eauto
  apply ℤ.divide_add_r; auto. eapply mi_align; eauto with mem
Qed

/- Preservation of loads. -/

lemma getN_inj :
  ∀ f m1 m2 b1 b2 delta,
  mem_inj f m1 m2 →
  f b1 = some(b2, delta) →
  ∀ n ofs,
  range_perm m1 b1 ofs (ofs + Z_of_nat n) Cur Readable →
  list_forall2 (memval_inject f)
               (getN n ofs (m1.(mem_contents)#b1))
               (getN n (ofs + delta) (m2.(mem_contents)#b2))
Proof
  induction n; intros; simpl
  constructor
  rewrite inj_S in H1
  constructor
  eapply mi_memval; eauto
  apply H1. omega
  replace (ofs + delta + 1) with ((ofs + 1) + delta) by omega
  apply IHn. red; intros; apply H1; omega
Qed

lemma load_inj :
  ∀ f m1 m2 chunk b1 ofs b2 delta v1,
  mem_inj f m1 m2 →
  load chunk m1 b1 ofs = some v1 →
  f b1 = some (b2, delta) →
  ∃ v2, load chunk m2 b2 (ofs + delta) = some v2 ∧ Val.inject f v1 v2
Proof
  intros
  ∃ (decode_val chunk (getN (size_chunk_nat chunk) (ofs + delta) (m2.(mem_contents)#b2)))
  split. unfold load. apply pred_dec_true
  eapply valid_access_inj; eauto with mem
  exploit load_result; eauto. intro. rewrite H2
  apply decode_val_inject. apply getN_inj; auto
  rewrite <- size_chunk_conv. exploit load_valid_access; eauto. intros [A B]. auto
Qed

lemma load_bytes_inj :
  ∀ f m1 m2 len b1 ofs b2 delta bytes1,
  mem_inj f m1 m2 →
  load_bytes m1 b1 ofs len = some bytes1 →
  f b1 = some (b2, delta) →
  ∃ bytes2, load_bytes m2 b2 (ofs + delta) len = some bytes2
              ∧ list_forall2 (memval_inject f) bytes1 bytes2
Proof
  intros. unfold load_bytes in *
  destruct (range_perm_dec m1 b1 ofs (ofs + len) Cur Readable); inv H0
  ∃ (getN (nat_of_Z len) (ofs + delta) (m2.(mem_contents)#b2))
  split. apply pred_dec_true
  replace (ofs + delta + len) with ((ofs + len) + delta) by omega
  eapply range_perm_inj; eauto with mem
  apply getN_inj; auto
  destruct (zle 0 len). rewrite nat_of_Z_eq; auto. omega
  rewrite nat_of_Z_neg. simpl. red; intros; omegaContradiction. omega
Qed

/- Preservation of stores. -/

lemma setN_inj :
  ∀ (access : ℤ → Prop) delta f vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 →
  ∀ p c1 c2,
  (∀ q, access q → memval_inject f (ZMap.get q c1) (ZMap.get (q + delta) c2)) →
  (∀ q, access q → memval_inject f (ZMap.get q (setN vl1 p c1))
                                         (ZMap.get (q + delta) (setN vl2 (p + delta) c2)))
Proof
  induction 1; intros; simpl
  auto
  replace (p + delta + 1) with ((p + 1) + delta) by omega
  apply IHlist_forall2; auto
  intros. rewrite ZMap.gsspec at 1. destruct (ZIndexed.eq q0 p). subst q0
  rewrite ZMap.gss. auto
  rewrite ZMap.gso. auto. unfold ZIndexed.t in *. omega
Qed

def meminj_no_overlap (f : meminj) (m : mem) : Prop :=
  ∀ b1 b1' delta1 b2 b2' delta2 ofs1 ofs2,
  b1 ≠ b2 →
  f b1 = some (b1', delta1) →
  f b2 = some (b2', delta2) →
  perm m b1 ofs1 Max Nonempty →
  perm m b2 ofs2 Max Nonempty →
  b1' ≠ b2' ∨ ofs1 + delta1 ≠ ofs2 + delta2

lemma store_mapped_inj :
  ∀ f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  mem_inj f m1 m2 →
  store chunk m1 b1 ofs v1 = some n1 →
  meminj_no_overlap f m1 →
  f b1 = some (b2, delta) →
  Val.inject f v1 v2 →
  ∃ n2,
    store chunk m2 b2 (ofs + delta) v2 = some n2
    ∧ mem_inj f n1 n2
Proof
  intros
  assert (valid_access m2 chunk b2 (ofs + delta) Writable)
    eapply valid_access_inj; eauto with mem
  destruct (valid_access_store _ _ _ _ v2 H4) as [n2 STORE]
  ∃ n2; split. auto
  constructor
/- perm -/
  intros. eapply perm_store_1; [eexact STORE|]
  eapply mi_perm; eauto
  eapply perm_store_2; eauto
/- align -/
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto
  red; intros; eauto with mem
/- mem_contents -/
  intros
  rewrite (store_mem_contents _ _ _ _ _ _ H0)
  rewrite (store_mem_contents _ _ _ _ _ _ STORE)
  rewrite ! PTree.gsspec
  destruct (peq b0 b1). subst b0
  /- block = b1, block = b2 -/
  assert (b3 = b2) by congruence. subst b3
  assert (delta0 = delta) by congruence. subst delta0
  rewrite peq_true
  apply setN_inj with (access := λ ofs := perm m1 b1 ofs Cur Readable)
  apply encode_val_inject; auto. intros. eapply mi_memval; eauto. eauto with mem
  destruct (peq b3 b2). subst b3
  /- block <> b1, block = b2 -/
  rewrite setN_other. eapply mi_memval; eauto. eauto with mem
  rewrite encode_val_length. rewrite <- size_chunk_conv. intros
  assert (b2 ≠ b2 ∨ ofs0 + delta0 ≠ (r - delta) + delta)
    eapply H1; eauto. eauto 6 with mem
    exploit store_valid_access_3. eexact H0. intros [A B]
    eapply perm_implies. apply perm_cur_max. apply A. omega. auto with mem
  destruct H8. congruence. omega
  /- block <> b1, block <> b2 -/
  eapply mi_memval; eauto. eauto with mem
Qed

lemma store_unmapped_inj :
  ∀ f chunk m1 b1 ofs v1 n1 m2,
  mem_inj f m1 m2 →
  store chunk m1 b1 ofs v1 = some n1 →
  f b1 = none →
  mem_inj f n1 m2
Proof
  intros. constructor
/- perm -/
  intros. eapply mi_perm; eauto with mem
/- align -/
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto
  red; intros; eauto with mem
/- mem_contents -/
  intros
  rewrite (store_mem_contents _ _ _ _ _ _ H0)
  rewrite PTree.gso. eapply mi_memval; eauto with mem
  congruence
Qed

lemma store_outside_inj :
  ∀ f m1 m2 chunk b ofs v m2',
  mem_inj f m1 m2 →
  (∀ b' delta ofs',
    f b' = some(b, delta) →
    perm m1 b' ofs' Cur Readable →
    ofs <= ofs' + delta < ofs + size_chunk chunk → false) →
  store chunk m2 b ofs v = some m2' →
  mem_inj f m1 m2'
Proof
  intros. inv H. constructor
/- perm -/
  eauto with mem
/- access -/
  intros; eapply mi_align0; eauto
/- mem_contents -/
  intros
  rewrite (store_mem_contents _ _ _ _ _ _ H1)
  rewrite PTree.gsspec. destruct (peq b2 b). subst b2
  rewrite setN_outside. auto
  rewrite encode_val_length. rewrite <- size_chunk_conv
  destruct (zlt (ofs0 + delta) ofs); auto
  destruct (zle (ofs + size_chunk chunk) (ofs0 + delta)). omega
  byContradiction. eapply H0; eauto. omega
  eauto with mem
Qed

lemma store_bytes_mapped_inj :
  ∀ f m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
  mem_inj f m1 m2 →
  store_bytes m1 b1 ofs bytes1 = some n1 →
  meminj_no_overlap f m1 →
  f b1 = some (b2, delta) →
  list_forall2 (memval_inject f) bytes1 bytes2 →
  ∃ n2,
    store_bytes m2 b2 (ofs + delta) bytes2 = some n2
    ∧ mem_inj f n1 n2
Proof
  intros. inversion H
  assert (range_perm m2 b2 (ofs + delta) (ofs + delta + Z_of_nat (length bytes2)) Cur Writable)
    replace (ofs + delta + Z_of_nat (length bytes2))
       with ((ofs + Z_of_nat (length bytes1)) + delta)
    eapply range_perm_inj; eauto with mem
    eapply store_bytes_range_perm; eauto
    rewrite (list_forall2_length H3). omega
  destruct (range_perm_store_bytes _ _ _ _ H4) as [n2 STORE]
  ∃ n2; split. eauto
  constructor
/- perm -/
  intros
  eapply perm_store_bytes_1; [apply STORE |]
  eapply mi_perm0; eauto
  eapply perm_store_bytes_2; eauto
/- align -/
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto
  red; intros. eapply perm_store_bytes_2; eauto
/- mem_contents -/
  intros
  assert (perm m1 b0 ofs0 Cur Readable). eapply perm_store_bytes_2; eauto
  rewrite (store_bytes_mem_contents _ _ _ _ _ H0)
  rewrite (store_bytes_mem_contents _ _ _ _ _ STORE)
  rewrite ! PTree.gsspec. destruct (peq b0 b1). subst b0
  /- block = b1, block = b2 -/
  assert (b3 = b2) by congruence. subst b3
  assert (delta0 = delta) by congruence. subst delta0
  rewrite peq_true
  apply setN_inj with (access := λ ofs := perm m1 b1 ofs Cur Readable); auto
  destruct (peq b3 b2). subst b3
  /- block <> b1, block = b2 -/
  rewrite setN_other. auto
  intros
  assert (b2 ≠ b2 ∨ ofs0 + delta0 ≠ (r - delta) + delta)
    eapply H1; eauto 6 with mem
    exploit store_bytes_range_perm. eexact H0
    instantiate (1 := r - delta)
    rewrite (list_forall2_length H3). omega
    eauto 6 with mem
  destruct H9. congruence. omega
  /- block <> b1, block <> b2 -/
  eauto
Qed

lemma store_bytes_unmapped_inj :
  ∀ f m1 b1 ofs bytes1 n1 m2,
  mem_inj f m1 m2 →
  store_bytes m1 b1 ofs bytes1 = some n1 →
  f b1 = none →
  mem_inj f n1 m2
Proof
  intros. inversion H
  constructor
/- perm -/
  intros. eapply mi_perm0; eauto. eapply perm_store_bytes_2; eauto
/- align -/
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto
  red; intros. eapply perm_store_bytes_2; eauto
/- mem_contents -/
  intros
  rewrite (store_bytes_mem_contents _ _ _ _ _ H0)
  rewrite PTree.gso. eapply mi_memval0; eauto. eapply perm_store_bytes_2; eauto
  congruence
Qed

lemma store_bytes_outside_inj :
  ∀ f m1 m2 b ofs bytes2 m2',
  mem_inj f m1 m2 →
  (∀ b' delta ofs',
    f b' = some(b, delta) →
    perm m1 b' ofs' Cur Readable →
    ofs <= ofs' + delta < ofs + Z_of_nat (length bytes2) → false) →
  store_bytes m2 b ofs bytes2 = some m2' →
  mem_inj f m1 m2'
Proof
  intros. inversion H. constructor
/- perm -/
  intros. eapply perm_store_bytes_1; eauto with mem
/- align -/
  eauto
/- mem_contents -/
  intros
  rewrite (store_bytes_mem_contents _ _ _ _ _ H1)
  rewrite PTree.gsspec. destruct (peq b2 b). subst b2
  rewrite setN_outside. auto
  destruct (zlt (ofs0 + delta) ofs); auto
  destruct (zle (ofs + Z_of_nat (length bytes2)) (ofs0 + delta)). omega
  byContradiction. eapply H0; eauto. omega
  eauto with mem
Qed

lemma store_bytes_empty_inj :
  ∀ f m1 b1 ofs1 m1' m2 b2 ofs2 m2',
  mem_inj f m1 m2 →
  store_bytes m1 b1 ofs1 nil = some m1' →
  store_bytes m2 b2 ofs2 nil = some m2' →
  mem_inj f m1' m2'
Proof
  intros. destruct H. constructor
/- perm -/
  intros
  eapply perm_store_bytes_1; eauto
  eapply mi_perm0; eauto
  eapply perm_store_bytes_2; eauto
/- align -/
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto
  red; intros. eapply perm_store_bytes_2; eauto
/- mem_contents -/
  intros
  assert (perm m1 b0 ofs Cur Readable). eapply perm_store_bytes_2; eauto
  rewrite (store_bytes_mem_contents _ _ _ _ _ H0)
  rewrite (store_bytes_mem_contents _ _ _ _ _ H1)
  simpl. rewrite ! PTree.gsspec
  destruct (peq b0 b1); destruct (peq b3 b2); subst; eapply mi_memval0; eauto
Qed

/- Preservation of allocations -/

lemma alloc_right_inj :
  ∀ f m1 m2 lo hi b2 m2',
  mem_inj f m1 m2 →
  alloc m2 lo hi = (m2', b2) →
  mem_inj f m1 m2'
Proof
  intros. injection H0. intros NEXT MEM
  inversion H. constructor
/- perm -/
  intros. eapply perm_alloc_1; eauto
/- align -/
  eauto
/- mem_contents -/
  intros
  assert (perm m2 b0 (ofs + delta) Cur Readable)
    eapply mi_perm0; eauto
  assert (valid_block m2 b0) by eauto with mem
  rewrite <- MEM; simpl. rewrite PTree.gso. eauto with mem
  rewrite NEXT. eauto with mem
Qed

lemma alloc_left_unmapped_inj :
  ∀ f m1 m2 lo hi m1' b1,
  mem_inj f m1 m2 →
  alloc m1 lo hi = (m1', b1) →
  f b1 = none →
  mem_inj f m1' m2
Proof
  intros. inversion H. constructor
/- perm -/
  intros. exploit perm_alloc_inv; eauto. intros
  destruct (eq_block b0 b1). congruence. eauto
/- align -/
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto
  red; intros. exploit perm_alloc_inv; eauto
  destruct (eq_block b0 b1); auto. congruence
/- mem_contents -/
  injection H0; intros NEXT MEM. intros
  rewrite <- MEM; simpl. rewrite NEXT
  exploit perm_alloc_inv; eauto. intros
  rewrite PTree.gsspec. unfold eq_block in H4. destruct (peq b0 b1)
  rewrite ZMap.gi. constructor. eauto
Qed

def inj_offset_aligned (delta : ℤ) (size : ℤ) : Prop :=
  ∀ chunk, size_chunk chunk <= size → (align_chunk chunk | delta)

lemma alloc_left_mapped_inj :
  ∀ f m1 m2 lo hi m1' b1 b2 delta,
  mem_inj f m1 m2 →
  alloc m1 lo hi = (m1', b1) →
  valid_block m2 b2 →
  inj_offset_aligned delta (hi-lo) →
  (∀ ofs k p, lo <= ofs < hi → perm m2 b2 (ofs + delta) k p) →
  f b1 = some(b2, delta) →
  mem_inj f m1' m2
Proof
  intros. inversion H. constructor
/- perm -/
  intros
  exploit perm_alloc_inv; eauto. intros. destruct (eq_block b0 b1). subst b0
  rewrite H4 in H5; inv H5. eauto. eauto
/- align -/
  intros. destruct (eq_block b0 b1)
  subst b0. assert (delta0 = delta) by congruence. subst delta0
  assert (lo <= ofs < hi)
  { eapply perm_alloc_3; eauto. apply H6. generalize (size_chunk_pos chunk); omega. }
  assert (lo <= ofs + size_chunk chunk - 1 < hi)
  { eapply perm_alloc_3; eauto. apply H6. generalize (size_chunk_pos chunk); omega. }
  apply H2. omega
  eapply mi_align0 with (ofs := ofs) (p := p); eauto
  red; intros. eapply perm_alloc_4; eauto
/- mem_contents -/
  injection H0; intros NEXT MEM
  intros. rewrite <- MEM; simpl. rewrite NEXT
  exploit perm_alloc_inv; eauto. intros
  rewrite PTree.gsspec. unfold eq_block in H7
  destruct (peq b0 b1). rewrite ZMap.gi. constructor. eauto
Qed

lemma free_left_inj :
  ∀ f m1 m2 b lo hi m1',
  mem_inj f m1 m2 →
  free m1 b lo hi = some m1' →
  mem_inj f m1' m2
Proof
  intros. exploit free_result; eauto. intro FREE. inversion H. constructor
/- perm -/
  intros. eauto with mem
/- align -/
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto
  red; intros; eapply perm_free_3; eauto
/- mem_contents -/
  intros. rewrite FREE; simpl. eauto with mem
Qed

lemma free_right_inj :
  ∀ f m1 m2 b lo hi m2',
  mem_inj f m1 m2 →
  free m2 b lo hi = some m2' →
  (∀ b' delta ofs k p,
    f b' = some(b, delta) →
    perm m1 b' ofs k p → lo <= ofs + delta < hi → false) →
  mem_inj f m1 m2'
Proof
  intros. exploit free_result; eauto. intro FREE. inversion H
  assert (PERM :
    ∀ b1 b2 delta ofs k p,
    f b1 = some (b2, delta) →
    perm m1 b1 ofs k p → perm m2' b2 (ofs + delta) k p)
  intros
  intros. eapply perm_free_1; eauto
  destruct (eq_block b2 b); auto. subst b. right
  assert (~ (lo <= ofs + delta < hi)). red; intros; eapply H1; eauto
  omega
  constructor
/- perm -/
  auto
/- align -/
  eapply mi_align0; eauto
/- mem_contents -/
  intros. rewrite FREE; simpl. eauto
Qed

/- Preservation of [drop_perm] operations. -/

lemma drop_unmapped_inj :
  ∀ f m1 m2 b lo hi p m1',
  mem_inj f m1 m2 →
  drop_perm m1 b lo hi p = some m1' →
  f b = none →
  mem_inj f m1' m2
Proof
  intros. inv H. constructor
/- perm -/
  intros. eapply mi_perm0; eauto. eapply perm_drop_4; eauto
/- align -/
  intros. eapply mi_align0 with (ofs := ofs) (p := p0); eauto
  red; intros; eapply perm_drop_4; eauto
/- contents -/
  intros
  replace (ZMap.get ofs m1'.(mem_contents)#b1) with (ZMap.get ofs m1.(mem_contents)#b1)
  apply mi_memval0; auto. eapply perm_drop_4; eauto
  unfold drop_perm in H0; destruct (range_perm_dec m1 b lo hi Cur Freeable); inv H0; auto
Qed

lemma drop_mapped_inj :
  ∀ f m1 m2 b1 b2 delta lo hi p m1',
  mem_inj f m1 m2 →
  drop_perm m1 b1 lo hi p = some m1' →
  meminj_no_overlap f m1 →
  f b1 = some(b2, delta) →
  ∃ m2',
      drop_perm m2 b2 (lo + delta) (hi + delta) p = some m2'
   ∧ mem_inj f m1' m2'
Proof
  intros
  assert ({ m2' | drop_perm m2 b2 (lo + delta) (hi + delta) p = some m2' })
  apply range_perm_drop_2. red; intros
  replace ofs with ((ofs - delta) + delta) by omega
  eapply perm_inj; eauto. eapply range_perm_drop_1; eauto. omega
  destruct X as [m2' DROP]. ∃ m2'; split; auto
  inv H
  constructor
/- perm -/
  intros
  assert (perm m2 b3 (ofs + delta0) k p0)
    eapply mi_perm0; eauto. eapply perm_drop_4; eauto
  destruct (eq_block b1 b0)
  /- b1 = b0 -/
  subst b0. rewrite H2 in H; inv H
  destruct (zlt (ofs + delta0) (lo + delta0)). eapply perm_drop_3; eauto
  destruct (zle (hi + delta0) (ofs + delta0)). eapply perm_drop_3; eauto
  assert (perm_order p p0)
    eapply perm_drop_2.  eexact H0. instantiate (1 := ofs). omega. eauto
  apply perm_implies with p; auto
  eapply perm_drop_1. eauto. omega
  /- b1 <> b0 -/
  eapply perm_drop_3; eauto
  destruct (eq_block b3 b2); auto
  destruct (zlt (ofs + delta0) (lo + delta)); auto
  destruct (zle (hi + delta) (ofs + delta0)); auto
  exploit H1; eauto
  instantiate (1 := ofs + delta0 - delta)
  apply perm_cur_max. apply perm_implies with Freeable
  eapply range_perm_drop_1; eauto. omega. auto with mem
  eapply perm_drop_4; eauto. eapply perm_max. apply perm_implies with p0. eauto
  eauto with mem
  intuition
/- align -/
  intros. eapply mi_align0 with (ofs := ofs) (p := p0); eauto
  red; intros; eapply perm_drop_4; eauto
/- memval -/
  intros
  replace (m1'.(mem_contents)#b0) with (m1.(mem_contents)#b0)
  replace (m2'.(mem_contents)#b3) with (m2.(mem_contents)#b3)
  apply mi_memval0; auto. eapply perm_drop_4; eauto
  unfold drop_perm in DROP; destruct (range_perm_dec m2 b2 (lo + delta) (hi + delta) Cur Freeable); inv DROP; auto
  unfold drop_perm in H0; destruct (range_perm_dec m1 b1 lo hi Cur Freeable); inv H0; auto
Qed

lemma drop_outside_inj : ∀ f m1 m2 b lo hi p m2',
  mem_inj f m1 m2 →
  drop_perm m2 b lo hi p = some m2' →
  (∀ b' delta ofs' k p,
    f b' = some(b, delta) →
    perm m1 b' ofs' k p →
    lo <= ofs' + delta < hi → false) →
  mem_inj f m1 m2'
Proof
  intros. inv H. constructor
  /- perm -/
  intros. eapply perm_drop_3; eauto
  destruct (eq_block b2 b); auto. subst b2. right
  destruct (zlt (ofs + delta) lo); auto
  destruct (zle hi (ofs + delta)); auto
  byContradiction. exploit H1; eauto. omega
  /- align -/
  eapply mi_align0; eauto
  /- contents -/
  intros
  replace (m2'.(mem_contents)#b2) with (m2.(mem_contents)#b2)
  apply mi_memval0; auto
  unfold drop_perm in H0; destruct (range_perm_dec m2 b lo hi Cur Freeable); inv H0; auto
Qed

/- * Memory extensions -/

/-  A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by increasing the sizes of the memory blocks of [m1] (decreasing
  the low bounds, increasing the high bounds), and replacing some of
  the [Vundef] values stored in [m1] by more defined values stored
  in [m2] at the same locations. -/

structure extends' (m1 m2 : mem) : Prop :=
  mk_extends {
    mext_next : nextblock m1 = nextblock m2;
    mext_inj :  mem_inj inject_id m1 m2;
    mext_perm_inv : ∀ b ofs k p,
      perm m2 b ofs k p →
      perm m1 b ofs k p ∨ ~perm m1 b ofs Max Nonempty
  }

def extends := extends'

theorem extends_refl :
  ∀ m, extends m m
Proof
  intros. constructor. auto. constructor
  intros. unfold inject_id in H; inv H. replace (ofs + 0) with ofs by omega. auto
  intros. unfold inject_id in H; inv H. apply ℤ.divide_0_r
  intros. unfold inject_id in H; inv H. replace (ofs + 0) with ofs by omega
  apply memval_lessdef_refl
  tauto
Qed

theorem load_extends :
  ∀ chunk m1 m2 b ofs v1,
  extends m1 m2 →
  load chunk m1 b ofs = some v1 →
  ∃ v2, load chunk m2 b ofs = some v2 ∧ Val.lessdef v1 v2
Proof
  intros. inv H. exploit load_inj; eauto. unfold inject_id; reflexivity
  intros [v2 [A B]]. ∃ v2; split
  replace (ofs + 0) with ofs in A by omega. auto
  rewrite val_inject_id in B. auto
Qed

theorem loadv_extends :
  ∀ chunk m1 m2 addr1 addr2 v1,
  extends m1 m2 →
  loadv chunk m1 addr1 = some v1 →
  Val.lessdef addr1 addr2 →
  ∃ v2, loadv chunk m2 addr2 = some v2 ∧ Val.lessdef v1 v2
Proof
  unfold loadv; intros. inv H1
  destruct addr2; try congruence. eapply load_extends; eauto
  congruence
Qed

theorem load_bytes_extends :
  ∀ m1 m2 b ofs len bytes1,
  extends m1 m2 →
  load_bytes m1 b ofs len = some bytes1 →
  ∃ bytes2, load_bytes m2 b ofs len = some bytes2
              ∧ list_forall2 memval_lessdef bytes1 bytes2
Proof
  intros. inv H
  replace ofs with (ofs + 0) by omega. eapply load_bytes_inj; eauto
Qed

theorem store_within_extends :
  ∀ chunk m1 m2 b ofs v1 m1' v2,
  extends m1 m2 →
  store chunk m1 b ofs v1 = some m1' →
  Val.lessdef v1 v2 →
  ∃ m2',
     store chunk m2 b ofs v2 = some m2'
  ∧ extends m1' m2'
Proof
  intros. inversion H
  exploit store_mapped_inj; eauto
    unfold inject_id; red; intros. inv H3; inv H4. auto
    unfold inject_id; reflexivity
    rewrite val_inject_id. eauto
  intros [m2' [A B]]
  ∃ m2'; split
  replace (ofs + 0) with ofs in A by omega. auto
  constructor; auto
  rewrite (nextblock_store _ _ _ _ _ _ H0)
  rewrite (nextblock_store _ _ _ _ _ _ A)
  auto
  intros. exploit mext_perm_inv0; intuition eauto using perm_store_1, perm_store_2
Qed

theorem store_outside_extends :
  ∀ chunk m1 m2 b ofs v m2',
  extends m1 m2 →
  store chunk m2 b ofs v = some m2' →
  (∀ ofs', perm m1 b ofs' Cur Readable → ofs <= ofs' < ofs + size_chunk chunk → false) →
  extends m1 m2'
Proof
  intros. inversion H. constructor
  rewrite (nextblock_store _ _ _ _ _ _ H0). auto
  eapply store_outside_inj; eauto
  unfold inject_id; intros. inv H2. eapply H1; eauto. omega
  intros. eauto using perm_store_2. 
Qed

theorem storev_extends :
  ∀ chunk m1 m2 addr1 v1 m1' addr2 v2,
  extends m1 m2 →
  storev chunk m1 addr1 v1 = some m1' →
  Val.lessdef addr1 addr2 →
  Val.lessdef v1 v2 →
  ∃ m2',
     storev chunk m2 addr2 v2 = some m2'
  ∧ extends m1' m2'
Proof
  unfold storev; intros. inv H1
  destruct addr2; try congruence. eapply store_within_extends; eauto
  congruence
Qed

theorem store_bytes_within_extends :
  ∀ m1 m2 b ofs bytes1 m1' bytes2,
  extends m1 m2 →
  store_bytes m1 b ofs bytes1 = some m1' →
  list_forall2 memval_lessdef bytes1 bytes2 →
  ∃ m2',
     store_bytes m2 b ofs bytes2 = some m2'
  ∧ extends m1' m2'
Proof
  intros. inversion H
  exploit store_bytes_mapped_inj; eauto
    unfold inject_id; red; intros. inv H3; inv H4. auto
    unfold inject_id; reflexivity
  intros [m2' [A B]]
  ∃ m2'; split
  replace (ofs + 0) with ofs in A by omega. auto
  constructor; auto
  rewrite (nextblock_store_bytes _ _ _ _ _ H0)
  rewrite (nextblock_store_bytes _ _ _ _ _ A)
  auto
  intros. exploit mext_perm_inv0; intuition eauto using perm_store_bytes_1, perm_store_bytes_2
Qed

theorem store_bytes_outside_extends :
  ∀ m1 m2 b ofs bytes2 m2',
  extends m1 m2 →
  store_bytes m2 b ofs bytes2 = some m2' →
  (∀ ofs', perm m1 b ofs' Cur Readable → ofs <= ofs' < ofs + Z_of_nat (length bytes2) → false) →
  extends m1 m2'
Proof
  intros. inversion H. constructor
  rewrite (nextblock_store_bytes _ _ _ _ _ H0). auto
  eapply store_bytes_outside_inj; eauto
  unfold inject_id; intros. inv H2. eapply H1; eauto. omega
  intros. eauto using perm_store_bytes_2. 
Qed

theorem alloc_extends :
  ∀ m1 m2 lo1 hi1 b m1' lo2 hi2,
  extends m1 m2 →
  alloc m1 lo1 hi1 = (m1', b) →
  lo2 <= lo1 → hi1 <= hi2 →
  ∃ m2',
     alloc m2 lo2 hi2 = (m2', b)
  ∧ extends m1' m2'
Proof
  intros. inv H
  case_eq (alloc m2 lo2 hi2); intros m2' b' ALLOC
  assert (b' = b)
    rewrite (alloc_result _ _ _ _ _ H0)
    rewrite (alloc_result _ _ _ _ _ ALLOC)
    auto
  subst b'
  ∃ m2'; split; auto
  constructor
  rewrite (nextblock_alloc _ _ _ _ _ H0)
  rewrite (nextblock_alloc _ _ _ _ _ ALLOC)
  congruence
  eapply alloc_left_mapped_inj with (m1 := m1) (m2 := m2') (b2 := b) (delta := 0); eauto
  eapply alloc_right_inj; eauto
  eauto with mem
  red. intros. apply Zdivide_0
  intros
  eapply perm_implies with Freeable; auto with mem
  eapply perm_alloc_2; eauto
  omega
  intros. eapply perm_alloc_inv in H; eauto
  generalize (perm_alloc_inv _ _ _ _ _ H0 b0 ofs Max Nonempty); intros PERM
  destruct (eq_block b0 b)
  subst b0. 
  assert (EITHER : lo1 <= ofs < hi1 ∨ ~(lo1 <= ofs < hi1)) by omega
  destruct EITHER
  left. apply perm_implies with Freeable; auto with mem. eapply perm_alloc_2; eauto
  right; tauto
  exploit mext_perm_inv0; intuition eauto using perm_alloc_1, perm_alloc_4
Qed

theorem free_left_extends :
  ∀ m1 m2 b lo hi m1',
  extends m1 m2 →
  free m1 b lo hi = some m1' →
  extends m1' m2
Proof
  intros. inv H. constructor
  rewrite (nextblock_free _ _ _ _ _ H0). auto
  eapply free_left_inj; eauto
  intros. exploit mext_perm_inv0; eauto. intros [A|A]. 
  eapply perm_free_inv in A; eauto. destruct A as [[A B]|A]; auto
  subst b0. right; eapply perm_free_2; eauto
  intuition eauto using perm_free_3
Qed

theorem free_right_extends :
  ∀ m1 m2 b lo hi m2',
  extends m1 m2 →
  free m2 b lo hi = some m2' →
  (∀ ofs k p, perm m1 b ofs k p → lo <= ofs < hi → false) →
  extends m1 m2'
Proof
  intros. inv H. constructor
  rewrite (nextblock_free _ _ _ _ _ H0). auto
  eapply free_right_inj; eauto
  unfold inject_id; intros. inv H. eapply H1; eauto. omega
  intros. eauto using perm_free_3. 
Qed

theorem free_parallel_extends :
  ∀ m1 m2 b lo hi m1',
  extends m1 m2 →
  free m1 b lo hi = some m1' →
  ∃ m2',
     free m2 b lo hi = some m2'
  ∧ extends m1' m2'
Proof
  intros. inversion H
  assert ({ m2' : mem | free m2 b lo hi = some m2' })
    apply range_perm_free. red; intros
    replace ofs with (ofs + 0) by omega
    eapply perm_inj with (b1 := b); eauto
    eapply free_range_perm; eauto
  destruct X as [m2' FREE]. ∃ m2'; split; auto
  constructor
  rewrite (nextblock_free _ _ _ _ _ H0)
  rewrite (nextblock_free _ _ _ _ _ FREE). auto
  eapply free_right_inj with (m1 := m1'); eauto
  eapply free_left_inj; eauto
  unfold inject_id; intros. inv H1
  eapply perm_free_2. eexact H0. instantiate (1 := ofs); omega. eauto
  intros. exploit mext_perm_inv0; eauto using perm_free_3. intros [A|A]
  eapply perm_free_inv in A; eauto. destruct A as [[A B]|A]; auto
  subst b0. right; eapply perm_free_2; eauto
  right; intuition eauto using perm_free_3
Qed

theorem valid_block_extends :
  ∀ m1 m2 b,
  extends m1 m2 →
  (valid_block m1 b ↔ valid_block m2 b)
Proof
  intros. inv H. unfold valid_block. rewrite mext_next0. tauto
Qed

theorem perm_extends :
  ∀ m1 m2 b ofs k p,
  extends m1 m2 → perm m1 b ofs k p → perm m2 b ofs k p
Proof
  intros. inv H. replace ofs with (ofs + 0) by omega
  eapply perm_inj; eauto
Qed

theorem perm_extends_inv :
  ∀ m1 m2 b ofs k p,
  extends m1 m2 → perm m2 b ofs k p → perm m1 b ofs k p ∨ ~perm m1 b ofs Max Nonempty
Proof
  intros. inv H; eauto
Qed

theorem valid_access_extends :
  ∀ m1 m2 chunk b ofs p,
  extends m1 m2 → valid_access m1 chunk b ofs p → valid_access m2 chunk b ofs p
Proof
  intros. inv H. replace ofs with (ofs + 0) by omega
  eapply valid_access_inj; eauto. auto
Qed

theorem valid_pointer_extends :
  ∀ m1 m2 b ofs,
  extends m1 m2 → valid_pointer m1 b ofs = tt → valid_pointer m2 b ofs = tt
Proof
  intros
  rewrite valid_pointer_valid_access in *
  eapply valid_access_extends; eauto
Qed

theorem weak_valid_pointer_extends :
  ∀ m1 m2 b ofs,
  extends m1 m2 →
  weak_valid_pointer m1 b ofs = tt → weak_valid_pointer m2 b ofs = tt
Proof
  intros until 1. unfold weak_valid_pointer. rewrite !orb_true_iff
  intros []; eauto using valid_pointer_extends
Qed

/- * Memory injections -/

/- A memory state [m1] injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address;
- unallocated blocks in [m1] must be mapped to [None] by [f];
- if [f b = Some(b', delta)], [b'] must be valid in [m2];
- distinct blocks in [m1] are mapped to non-overlapping sub-blocks in [m2];
- the sizes of [m2]'s blocks are representable with unsigned machine integers;
- pointers that could be represented using unsigned machine integers remain
  representable after the injection.
-/

structure inject' (f : meminj) (m1 m2 : mem) : Prop :=
  mk_inject {
    mi_inj :
      mem_inj f m1 m2;
    mi_freeblocks :
      ∀ b, ~(valid_block m1 b) → f b = none;
    mi_mappedblocks :
      ∀ b b' delta, f b = some(b', delta) → valid_block m2 b';
    mi_no_overlap :
      meminj_no_overlap f m1;
    mi_representable :
      ∀ b b' delta ofs,
      f b = some(b', delta) →
      perm m1 b (Ptrofs.unsigned ofs) Max Nonempty ∨ perm m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty →
      delta >= 0 ∧ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned;
    mi_perm_inv :
      ∀ b1 ofs b2 delta k p,
      f b1 = some(b2, delta) →
      perm m2 b2 (ofs + delta) k p →
      perm m1 b1 ofs k p ∨ ~perm m1 b1 ofs Max Nonempty
  }
def inject := inject'

Local Hint Resolve mi_mappedblocks : mem

/- Preservation of access validity and pointer validity -/

theorem valid_block_inject_1 :
  ∀ f m1 m2 b1 b2 delta,
  f b1 = some(b2, delta) →
  inject f m1 m2 →
  valid_block m1 b1
Proof
  intros. inv H. destruct (plt b1 (nextblock m1)). auto
  assert (f b1 = none). eapply mi_freeblocks; eauto. congruence
Qed

theorem valid_block_inject_2 :
  ∀ f m1 m2 b1 b2 delta,
  f b1 = some(b2, delta) →
  inject f m1 m2 →
  valid_block m2 b2
Proof
  intros. eapply mi_mappedblocks; eauto
Qed

Local Hint Resolve valid_block_inject_1 valid_block_inject_2 : mem

theorem perm_inject :
  ∀ f m1 m2 b1 b2 delta ofs k p,
  f b1 = some(b2, delta) →
  inject f m1 m2 →
  perm m1 b1 ofs k p → perm m2 b2 (ofs + delta) k p
Proof
  intros. inv H0. eapply perm_inj; eauto
Qed

theorem perm_inject_inv :
  ∀ f m1 m2 b1 ofs b2 delta k p,
  inject f m1 m2 →
  f b1 = some(b2, delta) →
  perm m2 b2 (ofs + delta) k p →
  perm m1 b1 ofs k p ∨ ~perm m1 b1 ofs Max Nonempty
Proof
  intros. eapply mi_perm_inv; eauto
Qed

theorem range_perm_inject :
  ∀ f m1 m2 b1 b2 delta lo hi k p,
  f b1 = some(b2, delta) →
  inject f m1 m2 →
  range_perm m1 b1 lo hi k p → range_perm m2 b2 (lo + delta) (hi + delta) k p
Proof
  intros. inv H0. eapply range_perm_inj; eauto
Qed

theorem valid_access_inject :
  ∀ f m1 m2 chunk b1 ofs b2 delta p,
  f b1 = some(b2, delta) →
  inject f m1 m2 →
  valid_access m1 chunk b1 ofs p →
  valid_access m2 chunk b2 (ofs + delta) p
Proof
  intros. eapply valid_access_inj; eauto. apply mi_inj; auto
Qed

theorem valid_pointer_inject :
  ∀ f m1 m2 b1 ofs b2 delta,
  f b1 = some(b2, delta) →
  inject f m1 m2 →
  valid_pointer m1 b1 ofs = tt →
  valid_pointer m2 b2 (ofs + delta) = tt
Proof
  intros
  rewrite valid_pointer_valid_access in H1
  rewrite valid_pointer_valid_access
  eapply valid_access_inject; eauto
Qed

theorem weak_valid_pointer_inject :
  ∀ f m1 m2 b1 ofs b2 delta,
  f b1 = some(b2, delta) →
  inject f m1 m2 →
  weak_valid_pointer m1 b1 ofs = tt →
  weak_valid_pointer m2 b2 (ofs + delta) = tt
Proof
  intros until 2. unfold weak_valid_pointer. rewrite !orb_true_iff
  replace (ofs + delta - 1) with ((ofs - 1) + delta) by omega
  intros []; eauto using valid_pointer_inject
Qed

/- The following lemmas establish the absence of machine integer overflow
  during address computations. -/

lemma address_inject :
  ∀ f m1 m2 b1 ofs1 b2 delta p,
  inject f m1 m2 →
  perm m1 b1 (Ptrofs.unsigned ofs1) Cur p →
  f b1 = some (b2, delta) →
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta
Proof
  intros
  assert (perm m1 b1 (Ptrofs.unsigned ofs1) Max Nonempty) by eauto with mem
  exploit mi_representable; eauto. intros [A B]
  assert (0 <= delta <= Ptrofs.max_unsigned)
    generalize (Ptrofs.unsigned_range ofs1). omega
  unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; omega
Qed

lemma address_inject' :
  ∀ f m1 m2 chunk b1 ofs1 b2 delta,
  inject f m1 m2 →
  valid_access m1 chunk b1 (Ptrofs.unsigned ofs1) Nonempty →
  f b1 = some (b2, delta) →
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta
Proof
  intros. destruct H0. eapply address_inject; eauto
  apply H0. generalize (size_chunk_pos chunk). omega
Qed

theorem weak_valid_pointer_inject_no_overflow :
  ∀ f m1 m2 b ofs b' delta,
  inject f m1 m2 →
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = tt →
  f b = some(b', delta) →
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned
Proof
  intros. rewrite weak_valid_pointer_spec in H0
  rewrite ! valid_pointer_nonempty_perm in H0
  exploit mi_representable; eauto. destruct H0; eauto with mem
  intros [A B]
  pose proof (Ptrofs.unsigned_range ofs)
  rewrite Ptrofs.unsigned_repr; omega
Qed

theorem valid_pointer_inject_no_overflow :
  ∀ f m1 m2 b ofs b' delta,
  inject f m1 m2 →
  valid_pointer m1 b (Ptrofs.unsigned ofs) = tt →
  f b = some(b', delta) →
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned
Proof
  eauto using weak_valid_pointer_inject_no_overflow, valid_pointer_implies
Qed

theorem valid_pointer_inject_val :
  ∀ f m1 m2 b ofs b' ofs',
  inject f m1 m2 →
  valid_pointer m1 b (Ptrofs.unsigned ofs) = tt →
  Val.inject f (Vptr b ofs) (Vptr b' ofs') →
  valid_pointer m2 b' (Ptrofs.unsigned ofs') = tt
Proof
  intros. inv H1
  erewrite address_inject'; eauto
  eapply valid_pointer_inject; eauto
  rewrite valid_pointer_valid_access in H0. eauto
Qed

theorem weak_valid_pointer_inject_val :
  ∀ f m1 m2 b ofs b' ofs',
  inject f m1 m2 →
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = tt →
  Val.inject f (Vptr b ofs) (Vptr b' ofs') →
  weak_valid_pointer m2 b' (Ptrofs.unsigned ofs') = tt
Proof
  intros. inv H1
  exploit weak_valid_pointer_inject; eauto. intros W
  rewrite weak_valid_pointer_spec in H0
  rewrite ! valid_pointer_nonempty_perm in H0
  exploit mi_representable; eauto. destruct H0; eauto with mem
  intros [A B]
  pose proof (Ptrofs.unsigned_range ofs)
  unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; auto; omega
Qed

theorem inject_no_overlap :
  ∀ f m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
  inject f m1 m2 →
  b1 ≠ b2 →
  f b1 = some (b1', delta1) →
  f b2 = some (b2', delta2) →
  perm m1 b1 ofs1 Max Nonempty →
  perm m1 b2 ofs2 Max Nonempty →
  b1' ≠ b2' ∨ ofs1 + delta1 ≠ ofs2 + delta2
Proof
  intros. inv H. eapply mi_no_overlap0; eauto
Qed

theorem different_pointers_inject :
  ∀ f m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  inject f m m' →
  b1 ≠ b2 →
  valid_pointer m b1 (Ptrofs.unsigned ofs1) = tt →
  valid_pointer m b2 (Ptrofs.unsigned ofs2) = tt →
  f b1 = some (b1', delta1) →
  f b2 = some (b2', delta2) →
  b1' ≠ b2' ∨
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
  Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2))
Proof
  intros
  rewrite valid_pointer_valid_access in H1
  rewrite valid_pointer_valid_access in H2
  rewrite (address_inject' _ _ _ _ _ _ _ _ H H1 H3)
  rewrite (address_inject' _ _ _ _ _ _ _ _ H H2 H4)
  inv H1. simpl in H5. inv H2. simpl in H1
  eapply mi_no_overlap; eauto
  apply perm_cur_max. apply (H5 (Ptrofs.unsigned ofs1)). omega
  apply perm_cur_max. apply (H1 (Ptrofs.unsigned ofs2)). omega
Qed

theorem disjoint_or_equal_inject :
  ∀ f m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz,
  inject f m m' →
  f b1 = some(b1', delta1) →
  f b2 = some(b2', delta2) →
  range_perm m b1 ofs1 (ofs1 + sz) Max Nonempty →
  range_perm m b2 ofs2 (ofs2 + sz) Max Nonempty →
  sz > 0 →
  b1 ≠ b2 ∨ ofs1 = ofs2 ∨ ofs1 + sz <= ofs2 ∨ ofs2 + sz <= ofs1 →
  b1' ≠ b2' ∨ ofs1 + delta1 = ofs2 + delta2
             ∨ ofs1 + delta1 + sz <= ofs2 + delta2
             ∨ ofs2 + delta2 + sz <= ofs1 + delta1
Proof
  intros
  destruct (eq_block b1 b2)
  assert (b1' = b2') by congruence. assert (delta1 = delta2) by congruence. subst
  destruct H5. congruence. right. destruct H5. left; congruence. right. omega
  destruct (eq_block b1' b2'); auto. subst. right. right
  set (i1 := (ofs1 + delta1, ofs1 + delta1 + sz))
  set (i2 := (ofs2 + delta2, ofs2 + delta2 + sz))
  change (snd i1 <= fst i2 ∨ snd i2 <= fst i1)
  apply Intv.range_disjoint'; simpl; try omega
  unfold Intv.disjoint, Intv.In; simpl; intros. red; intros
  exploit mi_no_overlap; eauto
  instantiate (1 := x - delta1). apply H2. omega
  instantiate (1 := x - delta2). apply H3. omega
  intuition
Qed

theorem aligned_area_inject :
  ∀ f m m' b ofs al sz b' delta,
  inject f m m' →
  al = 1 ∨ al = 2 ∨ al = 4 ∨ al = 8 → sz > 0 →
  (al | sz) →
  range_perm m b ofs (ofs + sz) Cur Nonempty →
  (al | ofs) →
  f b = some(b', delta) →
  (al | ofs + delta)
Proof
  intros
  assert (P : al > 0) by omega
  assert (Q : Zabs al <= Zabs sz). apply Zdivide_bounds; auto. omega
  rewrite Zabs_eq in Q; try omega. rewrite Zabs_eq in Q; try omega
  assert (R : ∃ chunk, al = align_chunk chunk ∧ al = size_chunk chunk)
    destruct H0. subst; ∃ Mint8unsigned; auto
    destruct H0. subst; ∃ Mint16unsigned; auto
    destruct H0. subst; ∃ Mint32; auto
    subst; ∃ Mint64; auto
  destruct R as [chunk [A B]]
  assert (valid_access m chunk b ofs Nonempty)
    split. red; intros; apply H3. omega. congruence
  exploit valid_access_inject; eauto. intros [C D]
  congruence
Qed

/- Preservation of loads -/

theorem load_inject :
  ∀ f m1 m2 chunk b1 ofs b2 delta v1,
  inject f m1 m2 →
  load chunk m1 b1 ofs = some v1 →
  f b1 = some (b2, delta) →
  ∃ v2, load chunk m2 b2 (ofs + delta) = some v2 ∧ Val.inject f v1 v2
Proof
  intros. inv H. eapply load_inj; eauto
Qed

theorem loadv_inject :
  ∀ f m1 m2 chunk a1 a2 v1,
  inject f m1 m2 →
  loadv chunk m1 a1 = some v1 →
  Val.inject f a1 a2 →
  ∃ v2, loadv chunk m2 a2 = some v2 ∧ Val.inject f v1 v2
Proof
  intros. inv H1; simpl in H0; try discriminate
  exploit load_inject; eauto. intros [v2 [LOAD INJ]]
  ∃ v2; split; auto. unfold loadv
  replace (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))
     with (Ptrofs.unsigned ofs1 + delta)
  auto. symmetry. eapply address_inject'; eauto with mem
Qed

theorem load_bytes_inject :
  ∀ f m1 m2 b1 ofs len b2 delta bytes1,
  inject f m1 m2 →
  load_bytes m1 b1 ofs len = some bytes1 →
  f b1 = some (b2, delta) →
  ∃ bytes2, load_bytes m2 b2 (ofs + delta) len = some bytes2
              ∧ list_forall2 (memval_inject f) bytes1 bytes2
Proof
  intros. inv H. eapply load_bytes_inj; eauto
Qed

/- Preservation of stores -/

theorem store_mapped_inject :
  ∀ f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  inject f m1 m2 →
  store chunk m1 b1 ofs v1 = some n1 →
  f b1 = some (b2, delta) →
  Val.inject f v1 v2 →
  ∃ n2,
    store chunk m2 b2 (ofs + delta) v2 = some n2
    ∧ inject f n1 n2
Proof
  intros. inversion H
  exploit store_mapped_inj; eauto. intros [n2 [STORE MI]]
  ∃ n2; split. eauto. constructor
/- inj -/
  auto
/- freeblocks -/
  eauto with mem
/- mappedblocks -/
  eauto with mem
/- no overlap -/
  red; intros. eauto with mem
/- representable -/
  intros. eapply mi_representable; try eassumption
  destruct H4; eauto with mem
/- perm inv -/
  intros. exploit mi_perm_inv0; eauto using perm_store_2. 
  intuition eauto using perm_store_1, perm_store_2
Qed

theorem store_unmapped_inject :
  ∀ f chunk m1 b1 ofs v1 n1 m2,
  inject f m1 m2 →
  store chunk m1 b1 ofs v1 = some n1 →
  f b1 = none →
  inject f n1 m2
Proof
  intros. inversion H
  constructor
/- inj -/
  eapply store_unmapped_inj; eauto
/- freeblocks -/
  eauto with mem
/- mappedblocks -/
  eauto with mem
/- no overlap -/
  red; intros. eauto with mem
/- representable -/
  intros. eapply mi_representable; try eassumption
  destruct H3; eauto with mem
/- perm inv -/
  intros. exploit mi_perm_inv0; eauto using perm_store_2. 
  intuition eauto using perm_store_1, perm_store_2
Qed

theorem store_outside_inject :
  ∀ f m1 m2 chunk b ofs v m2',
  inject f m1 m2 →
  (∀ b' delta ofs',
    f b' = some(b, delta) →
    perm m1 b' ofs' Cur Readable →
    ofs <= ofs' + delta < ofs + size_chunk chunk → false) →
  store chunk m2 b ofs v = some m2' →
  inject f m1 m2'
Proof
  intros. inversion H. constructor
/- inj -/
  eapply store_outside_inj; eauto
/- freeblocks -/
  auto
/- mappedblocks -/
  eauto with mem
/- no overlap -/
  auto
/- representable -/
  eauto with mem
/- perm inv -/
  intros. eauto using perm_store_2
Qed

theorem storev_mapped_inject :
  ∀ f chunk m1 a1 v1 n1 m2 a2 v2,
  inject f m1 m2 →
  storev chunk m1 a1 v1 = some n1 →
  Val.inject f a1 a2 →
  Val.inject f v1 v2 →
  ∃ n2,
    storev chunk m2 a2 v2 = some n2 ∧ inject f n1 n2
Proof
  intros. inv H1; simpl in H0; try discriminate
  unfold storev
  replace (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))
    with (Ptrofs.unsigned ofs1 + delta)
  eapply store_mapped_inject; eauto
  symmetry. eapply address_inject'; eauto with mem
Qed

theorem store_bytes_mapped_inject :
  ∀ f m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
  inject f m1 m2 →
  store_bytes m1 b1 ofs bytes1 = some n1 →
  f b1 = some (b2, delta) →
  list_forall2 (memval_inject f) bytes1 bytes2 →
  ∃ n2,
    store_bytes m2 b2 (ofs + delta) bytes2 = some n2
    ∧ inject f n1 n2
Proof
  intros. inversion H
  exploit store_bytes_mapped_inj; eauto. intros [n2 [STORE MI]]
  ∃ n2; split. eauto. constructor
/- inj -/
  auto
/- freeblocks -/
  intros. apply mi_freeblocks0. red; intros; elim H3; eapply store_bytes_valid_block_1; eauto
/- mappedblocks -/
  intros. eapply store_bytes_valid_block_1; eauto
/- no overlap -/
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_store_bytes_2; eauto
/- representable -/
  intros. eapply mi_representable0; eauto
  destruct H4; eauto using perm_store_bytes_2
/- perm inv -/
  intros. exploit mi_perm_inv0; eauto using perm_store_bytes_2. 
  intuition eauto using perm_store_bytes_1, perm_store_bytes_2
Qed

theorem store_bytes_unmapped_inject :
  ∀ f m1 b1 ofs bytes1 n1 m2,
  inject f m1 m2 →
  store_bytes m1 b1 ofs bytes1 = some n1 →
  f b1 = none →
  inject f n1 m2
Proof
  intros. inversion H
  constructor
/- inj -/
  eapply store_bytes_unmapped_inj; eauto
/- freeblocks -/
  intros. apply mi_freeblocks0. red; intros; elim H2; eapply store_bytes_valid_block_1; eauto
/- mappedblocks -/
  eauto with mem
/- no overlap -/
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_store_bytes_2; eauto
/- representable -/
  intros. eapply mi_representable0; eauto
  destruct H3; eauto using perm_store_bytes_2
/- perm inv -/
  intros. exploit mi_perm_inv0; eauto
  intuition eauto using perm_store_bytes_1, perm_store_bytes_2
Qed

theorem store_bytes_outside_inject :
  ∀ f m1 m2 b ofs bytes2 m2',
  inject f m1 m2 →
  (∀ b' delta ofs',
    f b' = some(b, delta) →
    perm m1 b' ofs' Cur Readable →
    ofs <= ofs' + delta < ofs + Z_of_nat (length bytes2) → false) →
  store_bytes m2 b ofs bytes2 = some m2' →
  inject f m1 m2'
Proof
  intros. inversion H. constructor
/- inj -/
  eapply store_bytes_outside_inj; eauto
/- freeblocks -/
  auto
/- mappedblocks -/
  intros. eapply store_bytes_valid_block_1; eauto
/- no overlap -/
  auto
/- representable -/
  auto
/- perm inv -/
  intros. eapply mi_perm_inv0; eauto using perm_store_bytes_2
Qed

theorem store_bytes_empty_inject :
  ∀ f m1 b1 ofs1 m1' m2 b2 ofs2 m2',
  inject f m1 m2 →
  store_bytes m1 b1 ofs1 nil = some m1' →
  store_bytes m2 b2 ofs2 nil = some m2' →
  inject f m1' m2'
Proof
  intros. inversion H. constructor; intros
/- inj -/
  eapply store_bytes_empty_inj; eauto
/- freeblocks -/
  intros. apply mi_freeblocks0. red; intros; elim H2; eapply store_bytes_valid_block_1; eauto
/- mappedblocks -/
  intros. eapply store_bytes_valid_block_1; eauto
/- no overlap -/
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_store_bytes_2; eauto
/- representable -/
  intros. eapply mi_representable0; eauto
  destruct H3; eauto using perm_store_bytes_2
/- perm inv -/
  intros. exploit mi_perm_inv0; eauto using perm_store_bytes_2. 
  intuition eauto using perm_store_bytes_1, perm_store_bytes_2
Qed

/- Preservation of allocations -/

theorem alloc_right_inject :
  ∀ f m1 m2 lo hi b2 m2',
  inject f m1 m2 →
  alloc m2 lo hi = (m2', b2) →
  inject f m1 m2'
Proof
  intros. injection H0. intros NEXT MEM
  inversion H. constructor
/- inj -/
  eapply alloc_right_inj; eauto
/- freeblocks -/
  auto
/- mappedblocks -/
  eauto with mem
/- no overlap -/
  auto
/- representable -/
  auto
/- perm inv -/
  intros. eapply perm_alloc_inv in H2; eauto. destruct (eq_block b0 b2)
  subst b0. eelim fresh_block_alloc; eauto. 
  eapply mi_perm_inv0; eauto
Qed

theorem alloc_left_unmapped_inject :
  ∀ f m1 m2 lo hi m1' b1,
  inject f m1 m2 →
  alloc m1 lo hi = (m1', b1) →
  ∃ f',
     inject f' m1' m2
  ∧ inject_incr f f'
  ∧ f' b1 = none
  ∧ (∀ b, b ≠ b1 → f' b = f b)
Proof
  intros. inversion H
  set (f' := λ b := if eq_block b b1 then none else f b)
  assert (inject_incr f f')
    red; unfold f'; intros. destruct (eq_block b b1). subst b
    assert (f b1 = none). eauto with mem. congruence
    auto
  assert (mem_inj f' m1 m2)
    inversion mi_inj0; constructor; eauto with mem
    unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto
    unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto
    unfold f'; intros. destruct (eq_block b0 b1). congruence
    apply memval_inject_incr with f; auto
  ∃ f'; split. constructor
/- inj -/
  eapply alloc_left_unmapped_inj; eauto. unfold f'; apply dec_eq_true
/- freeblocks -/
  intros. unfold f'. destruct (eq_block b b1). auto
  apply mi_freeblocks0. red; intro; elim H3. eauto with mem
/- mappedblocks -/
  unfold f'; intros. destruct (eq_block b b1). congruence. eauto
/- no overlap -/
  unfold f'; red; intros
  destruct (eq_block b0 b1); destruct (eq_block b2 b1); try congruence
  eapply mi_no_overlap0. eexact H3. eauto. eauto
  exploit perm_alloc_inv. eauto. eexact H6. rewrite dec_eq_false; auto
  exploit perm_alloc_inv. eauto. eexact H7. rewrite dec_eq_false; auto
/- representable -/
  unfold f'; intros
  destruct (eq_block b b1); try discriminate
  eapply mi_representable0; try eassumption
  destruct H4; eauto using perm_alloc_4
/- perm inv -/
  intros. unfold f' in H3; destruct (eq_block b0 b1); try discriminate
  exploit mi_perm_inv0; eauto. 
  intuition eauto using perm_alloc_1, perm_alloc_4
/- incr -/
  split. auto
/- image -/
  split. unfold f'; apply dec_eq_true
/- incr -/
  intros; unfold f'; apply dec_eq_false; auto
Qed

theorem alloc_left_mapped_inject :
  ∀ f m1 m2 lo hi m1' b1 b2 delta,
  inject f m1 m2 →
  alloc m1 lo hi = (m1', b1) →
  valid_block m2 b2 →
  0 <= delta <= Ptrofs.max_unsigned →
  (∀ ofs k p, perm m2 b2 ofs k p → delta = 0 ∨ 0 <= ofs < Ptrofs.max_unsigned) →
  (∀ ofs k p, lo <= ofs < hi → perm m2 b2 (ofs + delta) k p) →
  inj_offset_aligned delta (hi-lo) →
  (∀ b delta' ofs k p,
   f b = some (b2, delta') →
   perm m1 b ofs k p →
   lo + delta <= ofs + delta' < hi + delta → false) →
  ∃ f',
     inject f' m1' m2
  ∧ inject_incr f f'
  ∧ f' b1 = some(b2, delta)
  ∧ (∀ b, b ≠ b1 → f' b = f b)
Proof
  intros. inversion H
  set (f' := λ b := if eq_block b b1 then some(b2, delta) else f b)
  assert (inject_incr f f')
    red; unfold f'; intros. destruct (eq_block b b1). subst b
    assert (f b1 = none). eauto with mem. congruence
    auto
  assert (mem_inj f' m1 m2)
    inversion mi_inj0; constructor; eauto with mem
    unfold f'; intros. destruct (eq_block b0 b1)
      inversion H8. subst b0 b3 delta0
      elim (fresh_block_alloc _ _ _ _ _ H0). eauto with mem
      eauto
    unfold f'; intros. destruct (eq_block b0 b1)
      inversion H8. subst b0 b3 delta0
      elim (fresh_block_alloc _ _ _ _ _ H0)
      eapply perm_valid_block with (ofs := ofs). apply H9. generalize (size_chunk_pos chunk); omega
      eauto
    unfold f'; intros. destruct (eq_block b0 b1)
      inversion H8. subst b0 b3 delta0
      elim (fresh_block_alloc _ _ _ _ _ H0). eauto with mem
      apply memval_inject_incr with f; auto
  ∃ f'. split. constructor
/- inj -/
  eapply alloc_left_mapped_inj; eauto. unfold f'; apply dec_eq_true
/- freeblocks -/
  unfold f'; intros. destruct (eq_block b b1). subst b
  elim H9. eauto with mem
  eauto with mem
/- mappedblocks -/
  unfold f'; intros. destruct (eq_block b b1). congruence. eauto
/- overlap -/
  unfold f'; red; intros
  exploit perm_alloc_inv. eauto. eexact H12. intros P1
  exploit perm_alloc_inv. eauto. eexact H13. intros P2
  destruct (eq_block b0 b1); destruct (eq_block b3 b1)
  congruence
  inversion H10; subst b0 b1' delta1
    destruct (eq_block b2 b2'); auto. subst b2'. right; red; intros
    eapply H6; eauto. omega
  inversion H11; subst b3 b2' delta2
    destruct (eq_block b1' b2); auto. subst b1'. right; red; intros
    eapply H6; eauto. omega
  eauto
/- representable -/
  unfold f'; intros
  destruct (eq_block b b1)
   subst. injection H9; intros; subst b' delta0. destruct H10
    exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro
    exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto
    generalize (Ptrofs.unsigned_range_2 ofs). omega
   exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro
   exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto
   generalize (Ptrofs.unsigned_range_2 ofs). omega
  eapply mi_representable0; try eassumption
  destruct H10; eauto using perm_alloc_4
/- perm inv -/
  intros. unfold f' in H9; destruct (eq_block b0 b1)
  inversion H9; clear H9; subst b0 b3 delta0
  assert (EITHER : lo <= ofs < hi ∨ ~(lo <= ofs < hi)) by omega
  destruct EITHER
  left. apply perm_implies with Freeable; auto with mem. eapply perm_alloc_2; eauto
  right; intros A. eapply perm_alloc_inv in A; eauto. rewrite dec_eq_true in A. tauto
  exploit mi_perm_inv0; eauto. intuition eauto using perm_alloc_1, perm_alloc_4
/- incr -/
  split. auto
/- image of b1 -/
  split. unfold f'; apply dec_eq_true
/- image of others -/
  intros. unfold f'; apply dec_eq_false; auto
Qed

theorem alloc_parallel_inject :
  ∀ f m1 m2 lo1 hi1 m1' b1 lo2 hi2,
  inject f m1 m2 →
  alloc m1 lo1 hi1 = (m1', b1) →
  lo2 <= lo1 → hi1 <= hi2 →
  ∃ f', ∃ m2', ∃ b2,
  alloc m2 lo2 hi2 = (m2', b2)
  ∧ inject f' m1' m2'
  ∧ inject_incr f f'
  ∧ f' b1 = some(b2, 0)
  ∧ (∀ b, b ≠ b1 → f' b = f b)
Proof
  intros
  case_eq (alloc m2 lo2 hi2). intros m2' b2 ALLOC
  exploit alloc_left_mapped_inject
  eapply alloc_right_inject; eauto
  eauto
  instantiate (1 := b2). eauto with mem
  instantiate (1 := 0). unfold Ptrofs.max_unsigned. generalize Ptrofs.modulus_pos; omega
  auto
  intros. apply perm_implies with Freeable; auto with mem
  eapply perm_alloc_2; eauto. omega
  red; intros. apply Zdivide_0
  intros. apply (valid_not_valid_diff m2 b2 b2); eauto with mem
  intros [f' [A [B [C D]]]]
  ∃ f'; ∃ m2'; ∃ b2; auto
Qed

/- Preservation of [free] operations -/

lemma free_left_inject :
  ∀ f m1 m2 b lo hi m1',
  inject f m1 m2 →
  free m1 b lo hi = some m1' →
  inject f m1' m2
Proof
  intros. inversion H. constructor
/- inj -/
  eapply free_left_inj; eauto
/- freeblocks -/
  eauto with mem
/- mappedblocks -/
  auto
/- no overlap -/
  red; intros. eauto with mem
/- representable -/
  intros. eapply mi_representable0; try eassumption
  destruct H2; eauto with mem
/- perm inv -/
  intros. exploit mi_perm_inv0; eauto. intuition eauto using perm_free_3
  eapply perm_free_inv in H4; eauto. destruct H4 as [[A B] | A]; auto
  subst b1. right; eapply perm_free_2; eauto. 
Qed

lemma free_list_left_inject :
  ∀ f m2 l m1 m1',
  inject f m1 m2 →
  free_list m1 l = some m1' →
  inject f m1' m2
Proof
  induction l; simpl; intros
  inv H0. auto
  destruct a as [[b lo] hi]
  destruct (free m1 b lo hi) as [m11|] eqn:E; try discriminate
  apply IHl with m11; auto. eapply free_left_inject; eauto
Qed

lemma free_right_inject :
  ∀ f m1 m2 b lo hi m2',
  inject f m1 m2 →
  free m2 b lo hi = some m2' →
  (∀ b1 delta ofs k p,
    f b1 = some(b, delta) → perm m1 b1 ofs k p →
    lo <= ofs + delta < hi → false) →
  inject f m1 m2'
Proof
  intros. inversion H. constructor
/- inj -/
  eapply free_right_inj; eauto
/- freeblocks -/
  auto
/- mappedblocks -/
  eauto with mem
/- no overlap -/
  auto
/- representable -/
  auto
/- perm inv -/
  intros. eauto using perm_free_3
Qed

lemma perm_free_list :
  ∀ l m m' b ofs k p,
  free_list m l = some m' →
  perm m' b ofs k p →
  perm m b ofs k p ∧
  (∀ lo hi, In (b, lo, hi) l → lo <= ofs < hi → false)
Proof
  induction l; simpl; intros
  inv H. auto
  destruct a as [[b1 lo1] hi1]
  destruct (free m b1 lo1 hi1) as [m1|] eqn:E; try discriminate
  exploit IHl; eauto. intros [A B]
  split. eauto with mem
  intros. destruct H1. inv H1
  elim (perm_free_2 _ _ _ _ _ E ofs k p). auto. auto
  eauto
Qed

theorem free_inject :
  ∀ f m1 l m1' m2 b lo hi m2',
  inject f m1 m2 →
  free_list m1 l = some m1' →
  free m2 b lo hi = some m2' →
  (∀ b1 delta ofs k p,
    f b1 = some(b, delta) →
    perm m1 b1 ofs k p → lo <= ofs + delta < hi →
    ∃ lo1, ∃ hi1, In (b1, lo1, hi1) l ∧ lo1 <= ofs < hi1) →
  inject f m1' m2'
Proof
  intros
  eapply free_right_inject; eauto
  eapply free_list_left_inject; eauto
  intros. exploit perm_free_list; eauto. intros [A B]
  exploit H2; eauto. intros [lo1 [hi1 [C D]]]. eauto
Qed

theorem free_parallel_inject :
  ∀ f m1 m2 b lo hi m1' b' delta,
  inject f m1 m2 →
  free m1 b lo hi = some m1' →
  f b = some(b', delta) →
  ∃ m2',
     free m2 b' (lo + delta) (hi + delta) = some m2'
  ∧ inject f m1' m2'
Proof
  intros
  destruct (range_perm_free m2 b' (lo + delta) (hi + delta)) as [m2' FREE]
  eapply range_perm_inject; eauto. eapply free_range_perm; eauto
  ∃ m2'; split; auto
  eapply free_inject with (m1 := m1) (l := (b,lo,hi)::nil); eauto
  simpl; rewrite H0; auto
  intros. destruct (eq_block b1 b)
  subst b1. rewrite H1 in H2; inv H2
  ∃ lo, hi; split; auto with coqlib. omega
  exploit mi_no_overlap. eexact H. eexact n. eauto. eauto
  eapply perm_max. eapply perm_implies. eauto. auto with mem
  instantiate (1 := ofs + delta0 - delta)
  apply perm_cur_max. apply perm_implies with Freeable; auto with mem
  eapply free_range_perm; eauto. omega
  intros [A|A]. congruence. omega
Qed

lemma drop_outside_inject : ∀ f m1 m2 b lo hi p m2',
  inject f m1 m2 →
  drop_perm m2 b lo hi p = some m2' →
  (∀ b' delta ofs k p,
    f b' = some(b, delta) →
    perm m1 b' ofs k p → lo <= ofs + delta < hi → false) →
  inject f m1 m2'
Proof
  intros. destruct H. constructor; eauto
  eapply drop_outside_inj; eauto
  intros. unfold valid_block in *. erewrite nextblock_drop; eauto
  intros. eapply mi_perm_inv0; eauto using perm_drop_4
Qed

/- Composing two memory injections. -/

lemma mem_inj_compose :
  ∀ f f' m1 m2 m3,
  mem_inj f m1 m2 → mem_inj f' m2 m3 → mem_inj (compose_meminj f f') m1 m3
Proof
  intros. unfold compose_meminj. inv H; inv H0; constructor; intros
  /- perm -/
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate
  destruct (f' b') as [[b'' delta''] |] eqn:?; inv H
  replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') by omega
  eauto
  /- align -/
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate
  destruct (f' b') as [[b'' delta''] |] eqn:?; inv H
  apply ℤ.divide_add_r
  eapply mi_align0; eauto
  eapply mi_align1 with (ofs := ofs + delta') (p := p); eauto
  red; intros. replace ofs0 with ((ofs0 - delta') + delta') by omega
  eapply mi_perm0; eauto. apply H0. omega
  /- memval -/
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate
  destruct (f' b') as [[b'' delta''] |] eqn:?; inv H
  replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') by omega
  eapply memval_inject_compose; eauto
Qed

theorem inject_compose :
  ∀ f f' m1 m2 m3,
  inject f m1 m2 → inject f' m2 m3 →
  inject (compose_meminj f f') m1 m3
Proof
  unfold compose_meminj; intros
  inv H; inv H0. constructor
/- inj -/
  eapply mem_inj_compose; eauto
/- unmapped -/
  intros. erewrite mi_freeblocks0; eauto
/- mapped -/
  intros
  destruct (f b) as [[b1 delta1] |] eqn:?; try discriminate
  destruct (f' b1) as [[b2 delta2] |] eqn:?; inv H
  eauto
/- no overlap -/
  red; intros
  destruct (f b1) as [[b1x delta1x] |] eqn:?; try discriminate
  destruct (f' b1x) as [[b1y delta1y] |] eqn:?; inv H0
  destruct (f b2) as [[b2x delta2x] |] eqn:?; try discriminate
  destruct (f' b2x) as [[b2y delta2y] |] eqn:?; inv H1
  exploit mi_no_overlap0; eauto. intros A
  destruct (eq_block b1x b2x)
  subst b1x. destruct A. congruence
  assert (delta1y = delta2y) by congruence. right; omega
  exploit mi_no_overlap1. eauto. eauto. eauto
    eapply perm_inj. eauto. eexact H2. eauto
    eapply perm_inj. eauto. eexact H3. eauto
  intuition omega
/- representable -/
  intros
  destruct (f b) as [[b1 delta1] |] eqn:?; try discriminate
  destruct (f' b1) as [[b2 delta2] |] eqn:?; inv H
  exploit mi_representable0; eauto. intros [A B]
  set (ofs' := Ptrofs.repr (Ptrofs.unsigned ofs + delta1))
  assert (Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs + delta1)
    unfold ofs'; apply Ptrofs.unsigned_repr. auto
  exploit mi_representable1. eauto. instantiate (1 := ofs')
  rewrite H
  replace (Ptrofs.unsigned ofs + delta1 - 1) with
    ((Ptrofs.unsigned ofs - 1) + delta1) by omega
  destruct H0; eauto using perm_inj
  rewrite H. omega
/- perm inv -/
  intros. 
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate
  destruct (f' b') as [[b'' delta''] |] eqn:?; try discriminate
  inversion H; clear H; subst b'' delta
  replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') in H0 by omega
  exploit mi_perm_inv1; eauto. intros [A|A]
  eapply mi_perm_inv0; eauto
  right; red; intros. elim A. eapply perm_inj; eauto
Qed

lemma val_lessdef_inject_compose :
  ∀ f v1 v2 v3,
  Val.lessdef v1 v2 → Val.inject f v2 v3 → Val.inject f v1 v3
Proof
  intros. inv H. auto. auto
Qed

lemma val_inject_lessdef_compose :
  ∀ f v1 v2 v3,
  Val.inject f v1 v2 → Val.lessdef v2 v3 → Val.inject f v1 v3
Proof
  intros. inv H0. auto. inv H. auto
Qed

lemma extends_inject_compose :
  ∀ f m1 m2 m3,
  extends m1 m2 → inject f m2 m3 → inject f m1 m3
Proof
  intros. inversion H; inv H0. constructor; intros
/- inj -/
  replace f with (compose_meminj inject_id f). eapply mem_inj_compose; eauto
  apply extensionality; intros. unfold compose_meminj, inject_id
  destruct (f x) as [[y delta] | ]; auto
/- unmapped -/
  eapply mi_freeblocks0. erewrite <- valid_block_extends; eauto
/- mapped -/
  eauto
/- no overlap -/
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_extends; eauto
/- representable -/
  eapply mi_representable0; eauto
  destruct H1; eauto using perm_extends
/- perm inv -/
  exploit mi_perm_inv0; eauto. intros [A|A]
  eapply mext_perm_inv0; eauto
  right; red; intros; elim A. eapply perm_extends; eauto
Qed

lemma inject_extends_compose :
  ∀ f m1 m2 m3,
  inject f m1 m2 → extends m2 m3 → inject f m1 m3
Proof
  intros. inv H; inversion H0. constructor; intros
/- inj -/
  replace f with (compose_meminj f inject_id). eapply mem_inj_compose; eauto
  apply extensionality; intros. unfold compose_meminj, inject_id
  destruct (f x) as [[y delta] | ]; auto. decEq. decEq. omega
/- unmapped -/
  eauto
/- mapped -/
  erewrite <- valid_block_extends; eauto
/- no overlap -/
  red; intros. eapply mi_no_overlap0; eauto
/- representable -/
  eapply mi_representable0; eauto
/- perm inv -/
  exploit mext_perm_inv0; eauto. intros [A|A]
  eapply mi_perm_inv0; eauto
  right; red; intros; elim A. eapply perm_inj; eauto
Qed

lemma extends_extends_compose :
  ∀ m1 m2 m3,
  extends m1 m2 → extends m2 m3 → extends m1 m3
Proof
  intros. inversion H; subst; inv H0; constructor; intros
  /- nextblock -/
  congruence
  /- meminj -/
  replace inject_id with (compose_meminj inject_id inject_id)
  eapply mem_inj_compose; eauto
  apply extensionality; intros. unfold compose_meminj, inject_id. auto
  /- perm inv -/
  exploit mext_perm_inv1; eauto. intros [A|A]. 
  eapply mext_perm_inv0; eauto
  right; red; intros; elim A. eapply perm_extends; eauto
Qed

/- Injecting a memory into itself. -/

def flat_inj (thr : block) : meminj :=
  λ (b : block) := if plt b thr then some(b, 0) else none

def inject_neutral (thr : block) (m : mem) :=
  mem_inj (flat_inj thr) m m

theorem flat_inj_no_overlap :
  ∀ thr m, meminj_no_overlap (flat_inj thr) m
Proof
  unfold flat_inj; intros; red; intros
  destruct (plt b1 thr); inversion H0; subst
  destruct (plt b2 thr); inversion H1; subst
  auto
Qed

theorem neutral_inject :
  ∀ m, inject_neutral (nextblock m) m → inject (flat_inj (nextblock m)) m m
Proof
  intros. constructor
/- meminj -/
  auto
/- freeblocks -/
  unfold flat_inj, valid_block; intros
  apply pred_dec_false. auto
/- mappedblocks -/
  unfold flat_inj, valid_block; intros
  destruct (plt b (nextblock m)); inversion H0; subst. auto
/- no overlap -/
  apply flat_inj_no_overlap
/- range -/
  unfold flat_inj; intros
  destruct (plt b (nextblock m)); inv H0. generalize (Ptrofs.unsigned_range_2 ofs); omega
/- perm inv -/
  unfold flat_inj; intros
  destruct (plt b1 (nextblock m)); inv H0
  rewrite Zplus_0_r in H1; auto
Qed

theorem empty_inject_neutral :
  ∀ thr, inject_neutral thr empty
Proof
  intros; red; constructor
/- perm -/
  unfold flat_inj; intros. destruct (plt b1 thr); inv H
  replace (ofs + 0) with ofs by omega; auto
/- align -/
  unfold flat_inj; intros. destruct (plt b1 thr); inv H. apply ℤ.divide_0_r
/- mem_contents -/
  intros; simpl. rewrite ! PTree.gi. rewrite ! ZMap.gi. constructor
Qed

theorem alloc_inject_neutral :
  ∀ thr m lo hi b m',
  alloc m lo hi = (m', b) →
  inject_neutral thr m →
  Plt (nextblock m) thr →
  inject_neutral thr m'
Proof
  intros; red
  eapply alloc_left_mapped_inj with (m1 := m) (b2 := b) (delta := 0)
  eapply alloc_right_inj; eauto. eauto. eauto with mem
  red. intros. apply Zdivide_0
  intros
  apply perm_implies with Freeable; auto with mem
  eapply perm_alloc_2; eauto. omega
  unfold flat_inj. apply pred_dec_true
  rewrite (alloc_result _ _ _ _ _ H). auto
Qed

theorem store_inject_neutral :
  ∀ chunk m b ofs v m' thr,
  store chunk m b ofs v = some m' →
  inject_neutral thr m →
  Plt b thr →
  Val.inject (flat_inj thr) v v →
  inject_neutral thr m'
Proof
  intros; red
  exploit store_mapped_inj. eauto. eauto. apply flat_inj_no_overlap
  unfold flat_inj. apply pred_dec_true; auto. eauto
  replace (ofs + 0) with ofs by omega
  intros [m'' [A B]]. congruence
Qed

theorem drop_inject_neutral :
  ∀ m b lo hi p m' thr,
  drop_perm m b lo hi p = some m' →
  inject_neutral thr m →
  Plt b thr →
  inject_neutral thr m'
Proof
  unfold inject_neutral; intros
  exploit drop_mapped_inj; eauto. apply flat_inj_no_overlap
  unfold flat_inj. apply pred_dec_true; eauto
  repeat rewrite Zplus_0_r. intros [m'' [A B]]. congruence
Qed

/- * Invariance properties between two memory states -/

section UNCHANGED_ON

parameter P : block → ℤ → Prop

structure unchanged_on (m_before m_after : mem) : Prop := mk_unchanged_on {
  unchanged_on_nextblock :
    Ple (nextblock m_before) (nextblock m_after);
  unchanged_on_perm :
    ∀ b ofs k p,
    P b ofs → valid_block m_before b →
    (perm m_before b ofs k p ↔ perm m_after b ofs k p);
  unchanged_on_contents :
    ∀ b ofs,
    P b ofs → perm m_before b ofs Cur Readable →
    ZMap.get ofs (PTree.get b m_after.(mem_contents)) =
    ZMap.get ofs (PTree.get b m_before.(mem_contents))
}

lemma unchanged_on_refl :
  ∀ m, unchanged_on m m
Proof
  intros; constructor. apply Ple_refl. tauto. tauto
Qed

lemma valid_block_unchanged_on :
  ∀ m m' b,
  unchanged_on m m' → valid_block m b → valid_block m' b
Proof
  unfold valid_block; intros. apply unchanged_on_nextblock in H. xomega
Qed

lemma perm_unchanged_on :
  ∀ m m' b ofs k p,
  unchanged_on m m' → P b ofs →
  perm m b ofs k p → perm m' b ofs k p
Proof
  intros. destruct H. apply unchanged_on_perm0; auto. eapply perm_valid_block; eauto. 
Qed

lemma perm_unchanged_on_2 :
  ∀ m m' b ofs k p,
  unchanged_on m m' → P b ofs → valid_block m b →
  perm m' b ofs k p → perm m b ofs k p
Proof
  intros. destruct H. apply unchanged_on_perm0; auto
Qed

lemma unchanged_on_trans :
  ∀ m1 m2 m3, unchanged_on m1 m2 → unchanged_on m2 m3 → unchanged_on m1 m3
Proof
  intros; constructor
- apply Ple_trans with (nextblock m2); apply unchanged_on_nextblock; auto
- intros. transitivity (perm m2 b ofs k p); apply unchanged_on_perm; auto
  eapply valid_block_unchanged_on; eauto
- intros. transitivity (ZMap.get ofs (mem_contents m2)#b); apply unchanged_on_contents; auto
  eapply perm_unchanged_on; eauto. 
Qed

lemma load_bytes_unchanged_on_1 :
  ∀ m m' b ofs n,
  unchanged_on m m' →
  valid_block m b →
  (∀ i, ofs <= i < ofs + n → P b i) →
  load_bytes m' b ofs n = load_bytes m b ofs n
Proof
  intros
  destruct (zle n 0)
+ erewrite ! load_bytes_empty by assumption. auto
+ unfold load_bytes. destruct H
  destruct (range_perm_dec m b ofs (ofs + n) Cur Readable)
  rewrite pred_dec_true. f_equal
  apply getN_exten. intros. rewrite nat_of_Z_eq in H by omega
  apply unchanged_on_contents0; auto
  red; intros. apply unchanged_on_perm0; auto
  rewrite pred_dec_false. auto
  red; intros; elim n0; red; intros. apply <- unchanged_on_perm0; auto
Qed

lemma load_bytes_unchanged_on :
  ∀ m m' b ofs n bytes,
  unchanged_on m m' →
  (∀ i, ofs <= i < ofs + n → P b i) →
  load_bytes m b ofs n = some bytes →
  load_bytes m' b ofs n = some bytes
Proof
  intros
  destruct (zle n 0)
+ erewrite load_bytes_empty in * by assumption. auto
+ rewrite <- H1. apply load_bytes_unchanged_on_1; auto
  exploit load_bytes_range_perm; eauto. instantiate (1 := ofs). omega
  intros. eauto with mem
Qed

lemma load_unchanged_on_1 :
  ∀ m m' chunk b ofs,
  unchanged_on m m' →
  valid_block m b →
  (∀ i, ofs <= i < ofs + size_chunk chunk → P b i) →
  load chunk m' b ofs = load chunk m b ofs
Proof
  intros. unfold load. destruct (valid_access_dec m chunk b ofs Readable)
  destruct v. rewrite pred_dec_true. f_equal. f_equal. apply getN_exten. intros
  rewrite <- size_chunk_conv in H4. eapply unchanged_on_contents; eauto
  split; auto. red; intros. eapply perm_unchanged_on; eauto
  rewrite pred_dec_false. auto
  red; intros [A B]; elim n; split; auto. red; intros; eapply perm_unchanged_on_2; eauto
Qed

lemma load_unchanged_on :
  ∀ m m' chunk b ofs v,
  unchanged_on m m' →
  (∀ i, ofs <= i < ofs + size_chunk chunk → P b i) →
  load chunk m b ofs = some v →
  load chunk m' b ofs = some v
Proof
  intros. rewrite <- H1. eapply load_unchanged_on_1; eauto with mem
Qed

lemma store_unchanged_on :
  ∀ chunk m b ofs v m',
  store chunk m b ofs v = some m' →
  (∀ i, ofs <= i < ofs + size_chunk chunk → ~ P b i) →
  unchanged_on m m'
Proof
  intros; constructor; intros
- rewrite (nextblock_store _ _ _ _ _ _ H). apply Ple_refl
- split; intros; eauto with mem
- erewrite store_mem_contents; eauto. rewrite PTree.gsspec
  destruct (peq b0 b); auto. subst b0. apply setN_outside
  rewrite encode_val_length. rewrite <- size_chunk_conv
  destruct (zlt ofs0 ofs); auto
  destruct (zlt ofs0 (ofs + size_chunk chunk)); auto
  elim (H0 ofs0). omega. auto
Qed

lemma store_bytes_unchanged_on :
  ∀ m b ofs bytes m',
  store_bytes m b ofs bytes = some m' →
  (∀ i, ofs <= i < ofs + Z_of_nat (length bytes) → ~ P b i) →
  unchanged_on m m'
Proof
  intros; constructor; intros
- rewrite (nextblock_store_bytes _ _ _ _ _ H). apply Ple_refl
- split; intros. eapply perm_store_bytes_1; eauto. eapply perm_store_bytes_2; eauto
- erewrite store_bytes_mem_contents; eauto. rewrite PTree.gsspec
  destruct (peq b0 b); auto. subst b0. apply setN_outside
  destruct (zlt ofs0 ofs); auto
  destruct (zlt ofs0 (ofs + Z_of_nat (length bytes))); auto
  elim (H0 ofs0). omega. auto
Qed

lemma alloc_unchanged_on :
  ∀ m lo hi m' b,
  alloc m lo hi = (m', b) →
  unchanged_on m m'
Proof
  intros; constructor; intros
- rewrite (nextblock_alloc _ _ _ _ _ H). apply Ple_succ
- split; intros
  eapply perm_alloc_1; eauto
  eapply perm_alloc_4; eauto
  eapply valid_not_valid_diff; eauto with mem
- injection H; intros A B. rewrite <- B; simpl
  rewrite PTree.gso; auto. rewrite A.  eapply valid_not_valid_diff; eauto with mem
Qed

lemma free_unchanged_on :
  ∀ m b lo hi m',
  free m b lo hi = some m' →
  (∀ i, lo <= i < hi → ~ P b i) →
  unchanged_on m m'
Proof
  intros; constructor; intros
- rewrite (nextblock_free _ _ _ _ _ H). apply Ple_refl
- split; intros
  eapply perm_free_1; eauto
  destruct (eq_block b0 b); auto. destruct (zlt ofs lo); auto. destruct (zle hi ofs); auto
  subst b0. elim (H0 ofs). omega. auto
  eapply perm_free_3; eauto
- unfold free in H. destruct (range_perm_dec m b lo hi Cur Freeable); inv H
  simpl. auto
Qed

lemma drop_perm_unchanged_on :
  ∀ m b lo hi p m',
  drop_perm m b lo hi p = some m' →
  (∀ i, lo <= i < hi → ~ P b i) →
  unchanged_on m m'
Proof
  intros; constructor; intros
- rewrite (nextblock_drop _ _ _ _ _ _ H). apply Ple_refl
- split; intros. eapply perm_drop_3; eauto
  destruct (eq_block b0 b); auto
  subst b0. 
  assert (~ (lo <= ofs < hi)). { red; intros; eelim H0; eauto. }
  right; omega
  eapply perm_drop_4; eauto. 
- unfold drop_perm in H. 
  destruct (range_perm_dec m b lo hi Cur Freeable); inv H; simpl. auto
Qed. 

end UNCHANGED_ON

lemma unchanged_on_implies :
  ∀ (P Q : block → ℤ → Prop) m m',
  unchanged_on P m m' →
  (∀ b ofs, Q b ofs → valid_block m b → P b ofs) →
  unchanged_on Q m m'
Proof
  intros. destruct H. constructor; intros
- auto
- apply unchanged_on_perm0; auto. 
- apply unchanged_on_contents0; auto. 
  apply H0; auto. eapply perm_valid_block; eauto. 
Qed

end Mem

Notation mem := Mem.mem

Global Opaque Mem.alloc Mem.free Mem.store Mem.load Mem.store_bytes Mem.load_bytes

end memory