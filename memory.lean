
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
  nextblock_noaccess := λ b ofs k (h : (_:ℕ)≤_), by {
    rw PTree.gsspec,
    rw pos_num.succ_to_nat at h,
    by_cases (b = m.nextblock) with h'; simp [h'],
    { note := @not_le_of_gt nat _ _ _ h,
      rw h' at this, exact absurd (le_refl _) this },
    { apply m.nextblock_noaccess,
      exact le_of_lt h } } }

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

def get1 : ℤ → PTree.t memval → memval
| (p : ℕ) c := (PTree.get (num.succ' p) c).get_or_else Undef
| _ c := Undef

def getN : ℕ → ℤ → PTree.t memval → list memval
| 0       p c := []
| (n + 1) p c := get1 p c :: getN n (p+1) c

/- [load chunk m b ofs] perform a read in memory state [m], at address
  [b] and offset [ofs].  It returns the value of the memory chunk
  at that address.  [None] is returned if the accessed bytes
  are not readable. -/

def load (chunk : memory_chunk) (m : mem) (b : block) (ofs : ℕ) : option val :=
if valid_access m chunk b ofs Readable
then some $ decode_val chunk $ getN chunk.size ofs (m.get_block b) else none

/- [loadv chunk m addr] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. -/

def loadv (chunk : memory_chunk) (m : mem) : val → option val
| (Vptr b ofs) := load chunk m b (unsigned ofs)
| _ := none

/- [load_bytes m b ofs n] reads [n] consecutive bytes starting at
  location [(b, ofs)].  Returns [None] if the accessed locations are
  not readable. -/

def load_bytes (m : mem) (b : block) (ofs n : ℕ) : option (list memval) :=
if range_perm m b ofs (ofs + n) Cur Readable then some $ getN n ofs (m.get_block b) else none

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

theorem getN_setN_same {vl p c} : getN (list.length vl) ↑p (setN vl p c) = vl := sorry

theorem getN.ext {c1 c2 n p} :
  (∀ i, p ≤ i → i < p + ↑n → get1 i c1 = get1 i c2) →
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

lemma setN_in {vl p q c} : p ≤ q → q < p + list.length vl → get1 q (setN vl p c) ∈ vl := sorry

lemma getN_in {c q n p} : p ≤ q → q < p + ↑n → get1 q c ∈ getN n p c := sorry

/- [store_bytes m b ofs bytes] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable. -/

def store_bytes.val (m : mem) (b : block) (ofs : ℕ) (bytes : list memval) : mem :=
{ mem_contents       := PTree.set b (setN bytes ofs (m.get_block b)) m.mem_contents,
  mem_access         := m.mem_access,
  nextblock          := m.nextblock,
  access_max         := m.access_max,
  nextblock_noaccess := m.nextblock_noaccess }

def store_bytes (m : mem) (b : block) (ofs : ℕ) (bytes : list memval) : option mem :=
bnot (range_perm m b ofs (ofs + bytes.length) Cur Writable) |> store_bytes.val m b ofs bytes

/- [store chunk m b ofs v] perform a write in memory state [m].
  Value [v] is stored at address [b] and offset [ofs].
  Return the updated memory store, or [None] if the accessed bytes
  are not writable. -/

def store (chunk : memory_chunk) (m : mem) (b : block) (ofs : ℕ) (v : val) : option mem :=
bnot (valid_access m chunk b ofs Writable) |> store_bytes.val m b ofs (encode_val chunk v)

/- [storev chunk m addr v] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. -/

def storev (chunk : memory_chunk) (m : mem) : val → val → option mem
| (Vptr b ofs) v := store chunk m b (unsigned ofs) v
| _            v := none

/- [drop_perm m b lo hi p] sets the max permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have current permissions
    [Freeable] in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions. -/

def drop_perm.val (m : mem) (b : block) (lo hi : ℕ) (p : permission)
  (rp : range_perm m b lo hi Cur Freeable) : mem :=
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

def drop_perm (m : mem) (b : block) (lo hi : ℕ) (p : permission) : option mem :=
if rp : range_perm m b lo hi Cur Freeable then some (drop_perm.val m b lo hi p rp) else none

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
by { simp [load, load_valid_access h] at h, injection h, exact h.symm }

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
     injection this with this }

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
by revert p; induction n; intro p; simph [getN]

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
  (∀ z < ch.size, get1 (ofs + z : ℕ) (m1.get_block b) = get1 (ofs + z) (m2.get_block b)) →
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
parameters {m1 m2 : mem} {b : block} {ofs : ℕ} {bytes : list memval}
parameter (STORE : store_bytes m1 b ofs bytes = some m2)
include STORE

lemma store_bytes_val_eq : m2 = store_bytes.val m1 b ofs bytes :=
by { unfold store_bytes at STORE,
     cases to_bool (range_perm m1 b ofs (ofs + bytes.length) Cur Writable); try {contradiction},
     simp [option.rhoare] at STORE, injection STORE, exact h.symm }

lemma store_bytes_access : m2.mem_access = m1.mem_access :=
by rw store_bytes_val_eq STORE; refl

lemma store_bytes_mem_contents :
  m2.mem_contents = PTree.set b (setN bytes ofs (m1.get_block b)) m1.mem_contents :=
by rw store_bytes_val_eq STORE; refl

theorem perm_store_bytes {b' ofs' k p} : perm m2 b' ofs' k p ↔ perm m1 b' ofs' k p :=
by unfold perm mem.access; rw store_bytes_access STORE; exact iff.rfl

theorem nextblock_store_bytes : m2.nextblock = m1.nextblock :=
by rw store_bytes_val_eq STORE; refl

theorem store_bytes_valid_block {b'} : valid_block m2 b' ↔ valid_block m1 b' :=
by unfold valid_block; rw nextblock_store_bytes STORE; exact iff.rfl

theorem store_bytes_range_perm {b' lo hi k p} :
  range_perm m2 b' lo hi k p ↔ range_perm m1 b' lo hi k p :=
forall_congr $ λ_, forall_congr $ λ_, forall_congr $ λ_, perm_store_bytes

theorem store_bytes_valid_access {chunk' b' ofs' p} :
  valid_access m2 chunk' b' ofs' p ↔ valid_access m1 chunk' b' ofs' p :=
and_congr store_bytes_range_perm iff.rfl

theorem store_bytes_range_perm_1 : range_perm m1 b ofs (ofs + bytes.length) Cur Writable :=
by unfold store_bytes at STORE; by_contradiction; rw to_bool_ff a at STORE; contradiction

theorem store_bytes_range_perm_2 : range_perm m2 b ofs (ofs + bytes.length) Cur Writable :=
store_bytes_range_perm.2 store_bytes_range_perm_1

theorem load_store_bytes_same : load_bytes m2 b ofs bytes.length = some bytes :=
by { unfold load_bytes mem.get_block,
     rw [if_pos, store_bytes_mem_contents STORE, PTree.gss],
     { simp [option.get_or_else], rw getN_setN_same },
     { apply range_perm_implies _ (store_bytes_range_perm_2 STORE),
       exact dec_trivial } }

theorem load_bytes_store_bytes_disjoint {b' ofs' len} :
  b' ≠ b ∨ interval_disjoint ofs' len ofs bytes.length →
  load_bytes m2 b' ofs' len = load_bytes m1 b' ofs' len := sorry

theorem load_bytes_store_bytes_other {b' ofs' len} :
  b' ≠ b ∨ ofs' + len ≤ ofs ∨ ofs + bytes.length ≤ ofs' →
  load_bytes m2 b' ofs' len = load_bytes m1 b' ofs' len := sorry
theorem load_store_bytes_other {chunk : memory_chunk} {b' ofs'} :
  b' ≠ b ∨ ofs' + chunk.size ≤ ofs ∨ ofs + bytes.length ≤ ofs' →
  load chunk m2 b' ofs' = load chunk m1 b' ofs' := sorry

end store_bytes

/- ** Properties related to [store] -/

def store_eq_store_bytes {m chunk b ofs v} (h : align chunk ∣ ofs) :
  store chunk m b ofs v = store_bytes m b ofs (encode_val chunk v) :=
by { unfold store store_bytes,
     rw to_bool_congr _,
     rw encode_val_length,
     apply and_iff_left h }

def valid_access_store {m1 chunk b ofs v}
  (h : valid_access m1 chunk b ofs Writable) : { m2 : mem // store chunk m1 b ofs v = some m2 } :=
⟨_, by unfold store; rw to_bool_tt h; refl⟩

section store
parameters {chunk : memory_chunk} {m1 m2 : mem} {b : block} {ofs : ℕ} {v : val}
parameter (STORE : store chunk m1 b ofs v = some m2)
include STORE

theorem store_valid_access' : valid_access m1 chunk b ofs Writable :=
by unfold store at STORE; by_contradiction; rw to_bool_ff a at STORE; contradiction

lemma store_bytes_of_store : store_bytes m1 b ofs (encode_val chunk v) = some m2 :=
(store_eq_store_bytes $ store_valid_access'.right).symm.trans STORE

lemma store_val_eq : m2 = store_bytes.val m1 b ofs (encode_val chunk v) :=
store_bytes_val_eq store_bytes_of_store
--by {unfold store at STORE, cases to_bool (valid_access m1 chunk b ofs Writable); try {contradiction},
  --  simp [option.rhoare] at STORE, injection STORE, exact h.symm}

lemma store_access : m2.mem_access = m1.mem_access :=
store_bytes_access store_bytes_of_store

lemma store_mem_contents :
  m2.mem_contents = PTree.set b (setN (encode_val chunk v) ofs (m1.get_block b)) m1.mem_contents :=
store_bytes_mem_contents store_bytes_of_store

theorem perm_store {b' ofs' k p} : perm m2 b' ofs' k p ↔ perm m1 b' ofs' k p :=
perm_store_bytes store_bytes_of_store

theorem nextblock_store : m2.nextblock = m1.nextblock :=
nextblock_store_bytes store_bytes_of_store

theorem store_valid_block {b'} : valid_block m2 b' ↔ valid_block m1 b' :=
store_bytes_valid_block store_bytes_of_store

theorem store_valid_access {chunk' b' ofs' p} :
  valid_access m2 chunk' b' ofs' p ↔ valid_access m1 chunk' b' ofs' p :=
store_bytes_valid_access store_bytes_of_store

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

theorem load_store_other {chunk' : memory_chunk} {b' ofs'}
  (h : b' ≠ b ∨ ofs' + chunk'.size ≤ ofs ∨ ofs + chunk.size ≤ ofs') :
  load chunk' m2 b' ofs' = load chunk' m1 b' ofs' :=
by { apply load_store_bytes_other (store_bytes_of_store STORE), rwa encode_val_length }

theorem load_bytes_store_same : load_bytes m2 b ofs chunk.size = some (encode_val chunk v) :=
by { rw -encode_val_length, exact load_store_bytes_same (store_bytes_of_store STORE) }

theorem load_bytes_store_other {b' ofs' n}
  (h : b' ≠ b ∨ ofs' + n ≤ ofs ∨ ofs + chunk.size ≤ ofs') :
  load_bytes m2 b' ofs' n = load_bytes m1 b' ofs' n :=
by { apply load_bytes_store_bytes_other (store_bytes_of_store STORE), rwa encode_val_length }

end store

lemma load_store_overlap {chunk m1 b ofs v m2 chunk' ofs' v'} :
  store chunk m1 b ofs v = some m2 → load chunk' m2 b ofs' = some v' →
  ofs' + chunk'.size > ofs → ofs + chunk.size > ofs' →
  ∃ mv1 mvl mv1' mvl',
    shape_encoding chunk v (mv1 :: mvl)
  ∧ shape_decoding chunk' (mv1' :: mvl') v'
  ∧ ((ofs' = ofs ∧ mv1' = mv1)
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

lemma setN_concat {bytes1 bytes2 ofs c} :
  setN (bytes1 ++ bytes2) ofs c = setN bytes2 (ofs + bytes1.length) (setN bytes1 ofs c) := sorry

theorem store_bytes_concat {m b ofs bytes1 m1 bytes2 m2} :
  store_bytes m b ofs bytes1 = some m1 →
  store_bytes m1 b (ofs + bytes1.length) bytes2 = some m2 →
  store_bytes m b ofs (bytes1 ++ bytes2) = some m2 := sorry

theorem store_bytes_split {m b ofs bytes1 bytes2 m2} :
  store_bytes m b ofs (bytes1 ++ bytes2) = some m2 →
  ∃ m1, store_bytes m b ofs bytes1 = some m1
      ∧ store_bytes m1 b (ofs + bytes1.length) bytes2 = some m2 := sorry

theorem store_int64_split {m b ofs v m'} :
  store Mint64 m b ofs v = some m' → ¬ archi.ptr64 →
  ∃ m1, store Mint32 m b ofs (if archi.big_endian then hiword v else loword v) = some m1
  ∧ store Mint32 m1 b (ofs + 4) (if archi.big_endian then loword v else hiword v) = some m' := sorry

theorem storev_int64_split {m a v m'} :
  storev Mint64 m a v = some m' → archi.ptr64 = ff →
  ∃ m1, storev Mint32 m a (if archi.big_endian then hiword v else loword v) = some m1
  ∧ storev Mint32 m1 (a + Vint (repr 4)) (if archi.big_endian then loword v else hiword v) = some m' := sorry

/- ** Properties related to [alloc]. -/

section alloc

parameters {m1 : mem} {lo hi : ℕ}

local notation `b` := m1.nextblock
private def m2 := m1.alloc lo hi

theorem nextblock_alloc : m2.nextblock = m1.nextblock.succ := rfl

theorem alloc_result : b = m1.nextblock := rfl

theorem valid_new_block : valid_block m2 b :=
show (_:ℕ)<_, by rw [nextblock_alloc, pos_num.succ_to_nat]; apply nat.lt_succ_self

theorem valid_block_alloc {b'} (h : valid_block m1 b') : valid_block m2 b' :=
lt_trans h valid_new_block

theorem fresh_block_alloc : ¬ valid_block m1 b := lt_irrefl _

theorem valid_block_alloc_inv {b'} (h : valid_block m2 b') : b' = b ∨ valid_block m1 b' :=
have (_:ℕ)<pos_num.succ _, from h,
or.symm $ lt_or_eq_of_le $ nat.le_of_lt_succ $ by rwa pos_num.succ_to_nat at this

theorem perm_alloc_1 {b' ofs k p} : perm m1 b' ofs k p → perm m2 b' ofs k p :=
begin
  dsimp[perm, mem.access, m2, mem.alloc], rw PTree.gsspec,
  by_cases (b' = m1.nextblock); simp [h],
  { simp [m1.nextblock_noaccess ofs k (le_refl _), perm_order'] },
  { exact id }
end

theorem perm_alloc_2 {ofs k} : lo ≤ ofs → ofs < hi → perm m2 b ofs k Freeable := sorry

theorem perm_alloc_inv {b' ofs k p} : perm m2 b' ofs k p →
  if b' = b then lo ≤ ofs ∧ ofs < hi else perm m1 b' ofs k p := sorry

theorem perm_alloc_3 {ofs k p} (h : perm m2 b ofs k p) : lo ≤ ofs ∧ ofs < hi :=
by note := perm_alloc_inv h; simp at this; exact this

theorem perm_alloc_4 {b' ofs k p} (h1 : perm m2 b' ofs k p)
  (h2 : b' ≠ b) : perm m1 b' ofs k p :=
by note := perm_alloc_inv h1; simp [h2] at this; exact this

theorem valid_access_alloc_other {chunk b' ofs p} :
  valid_access m1 chunk b' ofs p →
  valid_access m2 chunk b' ofs p :=
and_implies (λal ofs' h1 h2, perm_alloc_1 $ al h1 h2) id

theorem valid_access_alloc_same {chunk : memory_chunk} {ofs}
  (hl : lo ≤ ofs) (hh : ofs + chunk.size ≤ hi) (ha : chunk.align ∣ ofs) :
  valid_access m2 chunk b ofs Freeable :=
⟨λofs' h1 h2, perm_alloc_2 (le_trans hl h1) (lt_of_lt_of_le h2 hh), ha⟩

theorem valid_access_alloc_inv {chunk b' ofs p} (h : valid_access m2 chunk b' ofs p) :
  if b' = b
  then lo ≤ ofs ∧ ofs + chunk.size ≤ hi ∧ chunk.align ∣ ofs
  else valid_access m1 chunk b' ofs p := sorry

theorem load_alloc_unchanged (chunk b' ofs) (h : valid_block m1 b') :
  load chunk m2 b' ofs = load chunk m1 b' ofs := sorry

theorem load_alloc_other {chunk b' ofs v}
  (h : load chunk m1 b' ofs = some v) : load chunk m2 b' ofs = some v :=
by rwa -load_alloc_unchanged at h; exact sorry

theorem load_alloc_same {chunk ofs v} :
  load chunk m2 b ofs = some v → v = Vundef := sorry

theorem load_alloc_same' {chunk : memory_chunk} {ofs} :
  lo ≤ ofs → ofs + chunk.size ≤ hi → chunk.align ∣ ofs →
  load chunk m2 b ofs = some Vundef := sorry

theorem load_bytes_alloc_unchanged {b' ofs n} :
  valid_block m1 b' → load_bytes m2 b' ofs n = load_bytes m1 b' ofs n := sorry

theorem load_bytes_alloc_same {n ofs bytes byte} :
  load_bytes m2 b ofs n = some bytes →
  byte ∈ bytes → byte = Undef := sorry

end alloc

/- ** Properties related to [free]. -/

theorem range_perm_free {m1 b lo hi}
  (h : range_perm m1 b lo hi Cur Freeable) : { m2 // free m1 b lo hi = some m2 } :=
by unfold free; simp [h]; exact ⟨_, rfl⟩

section free

parameters {m1 m2 : mem} {bf : block} {lo hi : ℕ}
parameter (FREE : free m1 bf lo hi = some m2)
include FREE

theorem free_range_perm : range_perm m1 bf lo hi Cur Freeable :=
by by_contradiction; simp [free, a] at FREE; contradiction

lemma free_result : m2 = unchecked_free m1 bf lo hi :=
by simp [free, free_range_perm FREE] at FREE; symmetry; injection FREE

theorem nextblock_free : m2.nextblock = m1.nextblock :=
by rw free_result FREE; refl

theorem valid_block_free {b} : valid_block m1 b ↔ valid_block m2 b :=
by rw free_result FREE; refl

theorem perm_free_1 {b ofs k p} :
  b ≠ bf ∨ ofs < lo ∨ hi ≤ ofs →
  perm m1 b ofs k p → perm m2 b ofs k p := sorry

theorem perm_free_2 {ofs k p} : lo ≤ ofs → ofs < hi → ¬ perm m2 bf ofs k p := sorry

theorem perm_free_3 {b ofs k p} : perm m2 b ofs k p → perm m1 b ofs k p := sorry

theorem perm_free_inv {b ofs k p} :
  perm m1 b ofs k p → (b = bf ∧ lo ≤ ofs ∧ ofs < hi) ∨ perm m2 b ofs k p := sorry

theorem valid_access_free_1 {chunk b ofs p} :
  valid_access m1 chunk b ofs p →
  b ≠ bf ∨ lo ≥ hi ∨ ofs + chunk.size ≤ lo ∨ hi ≤ ofs →
  valid_access m2 chunk b ofs p := sorry

theorem valid_access_free_2 {chunk : memory_chunk} {ofs p} :
  lo < hi → ofs + chunk.size > lo → ofs < hi →
  ¬ valid_access m2 chunk bf ofs p := sorry

theorem valid_access_free_inv_1 {chunk b ofs p} :
  valid_access m2 chunk b ofs p → valid_access m1 chunk b ofs p :=
and_implies (λal ofs' h1 h2, perm_free_3 $ al h1 h2) id

theorem valid_access_free_inv_2 {chunk ofs p} :
  valid_access m2 chunk bf ofs p →
  lo ≥ hi ∨ ofs + chunk.size ≤ lo ∨ hi ≤ ofs := sorry

theorem load_free {chunk :memory_chunk} {b ofs} :
  b ≠ bf ∨ lo ≥ hi ∨ ofs + chunk.size ≤ lo ∨ hi ≤ ofs →
  load chunk m2 b ofs = load chunk m1 b ofs := sorry

theorem load_free_2 {chunk b ofs v} :
  load chunk m2 b ofs = some v → load chunk m1 b ofs = some v := sorry

theorem load_bytes_free {b ofs n} :
  b ≠ bf ∨ lo ≥ hi ∨ ofs + n ≤ lo ∨ hi ≤ ofs →
  load_bytes m2 b ofs n = load_bytes m1 b ofs n := sorry

theorem load_bytes_free_2 {b ofs n bytes} :
  load_bytes m2 b ofs n = some bytes → load_bytes m1 b ofs n = some bytes := sorry

end free

/- ** Properties related to [drop_perm] -/

theorem range_perm_drop_2 {m b lo hi p}
  (h : range_perm m b lo hi Cur Freeable) : {m' // drop_perm m b lo hi p = some m'} :=
by unfold drop_perm; rw [dif_pos h]; exact ⟨_, rfl⟩

section drop

parameters {m m' : mem} {b : block} {lo hi : ℕ} {p : permission}
parameter (DROP : drop_perm m b lo hi p = some m')
include DROP

theorem range_perm_drop_1 : range_perm m b lo hi Cur Freeable :=
by by_contradiction; unfold drop_perm at DROP; rw [dif_neg a] at DROP; contradiction

theorem drop_eq_val : m' = drop_perm.val m b lo hi p range_perm_drop_1 :=
by unfold drop_perm at DROP;
   rw [dif_pos (range_perm_drop_1 DROP)] at DROP; symmetry; injection DROP

theorem nextblock_drop : m'.nextblock = m.nextblock :=
by rw drop_eq_val DROP; refl

theorem drop_perm_valid_block {b'} : valid_block m' b' ↔ valid_block m b' :=
by rw drop_eq_val DROP; refl

theorem perm_mem_access {ofs k} (hl : lo ≤ ofs) (hh : ofs < hi) :
  mem.access m' b ofs k = some p :=
begin
  rw drop_eq_val DROP, dsimp [drop_perm.val],
  dsimp [mem.access]; ginduction m.mem_access#b with ma f,
  { note := range_perm_drop_1 DROP hl hh,
    dsimp [perm, mem.access] at this,
    rw ma at this,
    apply false.elim this },
  { rw PTree.gss, dsimp [option.get_or_else],
    rw if_pos (and.intro hl hh) }
end

theorem perm_drop_2 {ofs k p'} (hl : lo ≤ ofs) (hh : ofs < hi) :
  perm m' b ofs k p' ↔ perm_order p p' :=
by unfold perm; rw perm_mem_access DROP hl hh; refl

theorem perm_drop_1 {ofs k} (hl : lo ≤ ofs) (hh : ofs < hi) : perm m' b ofs k p :=
(perm_drop_2 hl hh).2 (perm_order.perm_refl _)

theorem perm_drop_3 {b' ofs k p'} : b' ≠ b ∨ ofs < lo ∨ hi ≤ ofs →
  perm m b' ofs k p' → perm m' b' ofs k p' := sorry

theorem perm_drop_4 {b' ofs k p'} : perm m' b' ofs k p' → perm m b' ofs k p' := sorry

lemma range_perm_drop_3 {b' lo' hi' k p'}
  (h : b' ≠ b ∨ hi' ≤ lo ∨ hi ≤ lo' ∨ perm_order p p') :
  range_perm m b' lo' hi' k p' → range_perm m' b' lo' hi' k p' :=
λal ofs' hl hh, begin
  by_cases b' ≠ b ∨ ofs' < lo ∨ hi ≤ ofs' with H,
  { exact perm_drop_3 DROP H (al hl hh) },
  note bb : b' = b := decidable.by_contradiction (λh, H $ or.inl h),
  note ol : lo ≤ ofs' := le_of_not_gt (λh, H $ or.inr $ or.inl h),
  note oh : ofs' < hi := lt_of_not_ge (λh, H $ or.inr $ or.inr h),
  rw bb, apply (perm_drop_2 DROP ol oh).2,
  exact ((h.resolve_left (λn, n bb))
   .resolve_left (λn, not_le_of_gt hh $ le_trans n ol))
   .resolve_left (λn, not_le_of_gt oh $ le_trans n hl)
end

lemma range_perm_drop_4 {b' lo' hi' k p'} :
  range_perm m' b' lo' hi' k p' → range_perm m b' lo' hi' k p' :=
λal ofs' hl hh, perm_drop_4 $ al hl hh

lemma valid_access_drop_1 {chunk : memory_chunk} {b' ofs p'}
  (h : b' ≠ b ∨ ofs + chunk.size ≤ lo ∨ hi ≤ ofs ∨ perm_order p p') :
  valid_access m chunk b' ofs p' → valid_access m' chunk b' ofs p' :=
and_implies (range_perm_drop_3 h) id

lemma valid_access_drop_2 {chunk b' ofs p'} :
  valid_access m' chunk b' ofs p' → valid_access m chunk b' ofs p' :=
and_implies range_perm_drop_4 id

theorem load_drop {chunk : memory_chunk} {b' ofs}
  (h : b' ≠ b ∨ ofs + chunk.size ≤ lo ∨ hi ≤ ofs ∨ perm_order p Readable) :
  load chunk m' b' ofs = load chunk m b' ofs :=
begin
  note := valid_access_drop_1 DROP h,  
  unfold load,
  by_cases valid_access m chunk b' ofs Readable with va; simp [va],
  { simp [valid_access_drop_1 DROP h va], rw drop_eq_val DROP, refl },
  { simp [mt (valid_access_drop_2 DROP) va] }
end

theorem load_bytes_drop {b' ofs n}
  (h : b' ≠ b ∨ ofs + n ≤ lo ∨ hi ≤ ofs ∨ perm_order p Readable) :
  load_bytes m' b' ofs n = load_bytes m b' ofs n :=
begin
  unfold load_bytes,
  unfold load,
  by_cases range_perm m' b' ofs (ofs + n) Cur Readable with va; simp [va],
  { simp [range_perm_drop_4 DROP va], rw drop_eq_val DROP, refl },
  { simp [mt (range_perm_drop_3 DROP h) va] }
end

end drop

/- * Generic injections -/

/- A memory state [m1] generically injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corresponding address.
-/

def perm_Z (m : mem) (b : block) (ofs : ℤ) (k : perm_kind) (p : permission) : Prop :=
ofs.ex_nat $ λ ofs', perm m b ofs' k p

def range_perm_Z (m b) (lo hi : ℤ) (k p) : Prop :=
lo.ex_nat $ λlo', hi.ex_nat $ λhi', range_perm m b lo' hi' k p

def valid_access_Z (m chunk b) (ofs : ℤ) (p) : Prop :=
ofs.ex_nat $ λ ofs', valid_access m chunk b ofs' p

#check λ (f : meminj) (m1 m2 : mem), ∀ b1 b2 delta ofs ofs' k p,
  f b1 = some (b2, delta) →
  perm_Z m1 b1 ofs k p →
  perm_Z m2 b2 (ofs + delta) k p

structure mem_inj (f : meminj) (m1 m2 : mem) : Prop :=
(mi_perm : ∀ b1 b2 delta ofs k p,
  f b1 = some (b2, delta) →
  perm_Z m1 b1 ofs k p →
  perm_Z m2 b2 (ofs + delta) k p)
(mi_align : ∀ b1 b2 delta (chunk : memory_chunk) ofs p,
  f b1 = some (b2, delta) →
  range_perm m1 b1 ofs (ofs + chunk.size) Max p →
  ↑chunk.align ∣ delta)
(mi_memval : ∀ b1 ofs b2 delta,
  f b1 = some (b2, delta) →
  perm m1 b1 ofs Cur Readable →
  (↑ofs + delta).ex_nat (λ ofs',
  memval_inject f (get1 ofs (m1.get_block b1)) (get1 ofs' (m2.get_block b2))))

/- Preservation of permissions -/

lemma range_perm_inj {f m1 m2 b1 lo hi k p b2 delta} :
  mem_inj f m1 m2 →
  range_perm_Z m1 b1 lo hi k p →
  f b1 = some (b2, delta) →
  range_perm_Z m2 b2 (lo + delta) (hi + delta) k p := sorry

lemma valid_access_inj {f m1 m2 b1 b2 delta chunk ofs p} :
  mem_inj f m1 m2 →
  f b1 = some (b2, delta) →
  valid_access_Z m1 chunk b1 ofs p →
  valid_access_Z m2 chunk b2 (ofs + delta) p := sorry

/- Preservation of loads. -/

lemma getN_inj {f m1 m2 b1 b2 delta} :
  mem_inj f m1 m2 →
  f b1 = some (b2, delta) →
  ∀ {n ofs},
  range_perm m1 b1 ofs (ofs + n) Cur Readable →
  (↑ofs + delta).ex_nat (λ ofs',
  list.forall2 (memval_inject f)
               (getN n ofs (m1.get_block b1))
               (getN n ofs' (m2.get_block b2))) := sorry

lemma load_inj {f m1 m2 chunk b1 ofs b2 delta v1} :
  mem_inj f m1 m2 →
  load chunk m1 b1 ofs = some v1 →
  f b1 = some (b2, delta) →
  (↑ofs + delta).ex_nat (λ ofs',
  ∃ v2, load chunk m2 b2 ofs' = some v2 ∧ inject f v1 v2) := sorry

lemma load_bytes_inj {f m1 m2 len b1 ofs b2 delta bytes1} :
  mem_inj f m1 m2 →
  load_bytes m1 b1 ofs len = some bytes1 →
  f b1 = some (b2, delta) →
  (↑ofs + delta).ex_nat (λ ofs',
  ∃ bytes2, load_bytes m2 b2 ofs' len = some bytes2
              ∧ list.forall2 (memval_inject f) bytes1 bytes2) := sorry

/- Preservation of stores. -/

lemma setN_inj (access : ℤ → Prop) {delta f vl1 vl2} :
  list.forall2 (memval_inject f) vl1 vl2 →
  ∀ p c1 c2,
  (∀ q, access q → memval_inject f (get1 q c1) (get1 (q + delta) c2)) →
  (∀ q, access q → (↑p + delta).all_nat (λp',
     memval_inject f (get1 q (setN vl1 p c1))
                     (get1 (q + delta) (setN vl2 p' c2)))) := sorry

def meminj_no_overlap (f : meminj) (m : mem) : Prop :=
  ∀ b1 b1' delta1 b2 b2' delta2 ofs1 ofs2,
  b1 ≠ b2 →
  f b1 = some (b1', delta1) →
  f b2 = some (b2', delta2) →
  perm m b1 ofs1 Max Nonempty →
  perm m b2 ofs2 Max Nonempty →
  b1' ≠ b2' ∨ ↑ofs1 + delta1 ≠ ofs2 + delta2

lemma store_mapped_inj {f chunk m1 b1 ofs v1 n1 m2 b2 delta v2} :
  mem_inj f m1 m2 →
  store chunk m1 b1 ofs v1 = some n1 →
  meminj_no_overlap f m1 →
  f b1 = some (b2, delta) →
  inject f v1 v2 →
  (↑ofs + delta).ex_nat (λ ofs',
  ∃ n2,
    store chunk m2 b2 ofs' v2 = some n2
    ∧ mem_inj f n1 n2) := sorry

lemma store_unmapped_inj {f chunk m1 b1 ofs v1 n1 m2} :
  mem_inj f m1 m2 →
  store chunk m1 b1 ofs v1 = some n1 →
  f b1 = none →
  mem_inj f n1 m2 := sorry

lemma store_outside_inj {f m1 m2 chunk b ofs v m2'} :
  mem_inj f m1 m2 →
  (∀ b' delta ofs',
    f b' = some (b, delta) →
    perm m1 b' ofs' Cur Readable →
    ↑ofs ≤ ↑ofs' + delta → ↑ofs' + delta < ↑ofs + memory_chunk.size chunk → false) →
  store chunk m2 b ofs v = some m2' →
  mem_inj f m1 m2' := sorry

lemma store_bytes_mapped_inj {f m1 b1 ofs bytes1 n1 m2 b2 delta bytes2} :
  mem_inj f m1 m2 →
  store_bytes m1 b1 ofs bytes1 = some n1 →
  meminj_no_overlap f m1 →
  f b1 = some (b2, delta) →
  list.forall2 (memval_inject f) bytes1 bytes2 →
  (↑ofs + delta).ex_nat (λ ofs',
  ∃ n2,
    store_bytes m2 b2 ofs' bytes2 = some n2
    ∧ mem_inj f n1 n2) := sorry

lemma store_bytes_unmapped_inj {f m1 b1 ofs bytes1 n1 m2} :
  mem_inj f m1 m2 →
  store_bytes m1 b1 ofs bytes1 = some n1 →
  f b1 = none →
  mem_inj f n1 m2 := sorry

lemma store_bytes_outside_inj {f m1 m2 b ofs bytes2 m2'} :
  mem_inj f m1 m2 →
  (∀ b' delta ofs',
    f b' = some (b, delta) →
    perm m1 b' ofs' Cur Readable →
    ↑ofs ≤ ↑ofs' + delta → ↑ofs' + delta < ↑ofs + list.length bytes2 → false) →
  store_bytes m2 b ofs bytes2 = some m2' →
  mem_inj f m1 m2' := sorry

lemma store_bytes_empty_inj {f m1 b1 ofs1 m1' m2 b2 ofs2 m2'} :
  mem_inj f m1 m2 →
  store_bytes m1 b1 ofs1 [] = some m1' →
  store_bytes m2 b2 ofs2 [] = some m2' →
  mem_inj f m1' m2' := sorry

/- Preservation of allocations -/

lemma alloc_right_inj {f m1 m2 lo hi} :
  mem_inj f m1 m2 →
  mem_inj f m1 (m2.alloc lo hi) := sorry

lemma alloc_left_unmapped_inj {f m1 m2 lo hi} :
  mem_inj f m1 m2 →
  f m1.nextblock = none →
  mem_inj f (m1.alloc lo hi) m2 := sorry

def inj_offset_aligned (delta : ℤ) (size : ℕ) : Prop :=
  ∀ chunk : memory_chunk, chunk.size ≤ size → ↑chunk.align ∣ delta

lemma alloc_left_mapped_inj {f m1 m2 lo hi b2 delta} :
  mem_inj f m1 m2 →
  valid_block m2 b2 →
  inj_offset_aligned delta (hi-lo) →
  (∀ ofs k p, lo ≤ ofs → ofs < hi → perm_Z m2 b2 (↑ofs + delta) k p) →
  f m1.nextblock = some (b2, delta) →
  mem_inj f (m1.alloc lo hi) m2 := sorry

lemma free_left_inj {f m1 m2 b lo hi m1'} :
  mem_inj f m1 m2 →
  free m1 b lo hi = some m1' →
  mem_inj f m1' m2 := sorry

lemma free_right_inj {f m1 m2 b lo hi m2'} :
  mem_inj f m1 m2 →
  free m2 b lo hi = some m2' →
  (∀ b' delta ofs k p,
    f b' = some (b, delta) →
    perm m1 b' ofs k p → ↑lo ≤ ↑ofs + delta → ↑ofs + delta < hi → false) →
  mem_inj f m1 m2' := sorry

/- Preservation of [drop_perm] operations. -/

lemma drop_unmapped_inj {f m1 m2 b lo hi p m1'} :
  mem_inj f m1 m2 →
  drop_perm m1 b lo hi p = some m1' →
  f b = none →
  mem_inj f m1' m2 := sorry

lemma drop_mapped_inj {f m1 m2 b1 b2 delta lo hi p m1'} :
  mem_inj f m1 m2 →
  drop_perm m1 b1 lo hi p = some m1' →
  meminj_no_overlap f m1 →
  f b1 = some (b2, delta) →
  (↑lo + delta).all_nat (λlo', (↑hi + delta).all_nat $ λhi',
  ∃ m2', drop_perm m2 b2 lo' hi' p = some m2'
   ∧ mem_inj f m1' m2') := sorry

lemma drop_outside_inj {f m1 m2 b lo hi p m2'} :
  mem_inj f m1 m2 →
  drop_perm m2 b lo hi p = some m2' →
  (∀ b' delta ofs' k p,
    f b' = some (b, delta) →
    perm m1 b' ofs' k p →
    ↑lo ≤ ↑ofs' + delta → ↑ofs' + delta < hi → false) →
  mem_inj f m1 m2' := sorry

/- * Memory extensions -/

/-  A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by increasing the sizes of the memory blocks of [m1] (decreasing
  the low bounds, increasing the high bounds), and replacing some of
  the [Vundef] values stored in [m1] by more defined values stored
  in [m2] at the same locations. -/

structure extends' (m1 m2 : mem) : Prop :=
(next : m1.nextblock = m2.nextblock)
(inj :  mem_inj inject_id m1 m2)
(perm_inv : ∀ b ofs k p, perm m1 b ofs Max Nonempty →
      perm m2 b ofs k p → perm m1 b ofs k p)

theorem extends_refl (m) : extends' m m := sorry

theorem load_extends {chunk m1 m2 b ofs v1} :
  extends' m1 m2 →
  load chunk m1 b ofs = some v1 →
  ∃ v2, load chunk m2 b ofs = some v2 ∧ v1.lessdef v2 := sorry

theorem loadv_extends {chunk m1 m2 addr1 addr2 v1} :
  extends' m1 m2 →
  loadv chunk m1 addr1 = some v1 →
  addr1.lessdef addr2 →
  ∃ v2, loadv chunk m2 addr2 = some v2 ∧ v1.lessdef v2 := sorry

theorem load_bytes_extends {m1 m2 b ofs len bytes1} :
  extends' m1 m2 →
  load_bytes m1 b ofs len = some bytes1 →
  ∃ bytes2, load_bytes m2 b ofs len = some bytes2
              ∧ list.forall2 memval_lessdef bytes1 bytes2 := sorry

theorem store_within_extends {chunk m1 m2 b ofs v1 m1' v2} :
  extends' m1 m2 →
  store chunk m1 b ofs v1 = some m1' →
  v1.lessdef v2 →
  ∃ m2',
     store chunk m2 b ofs v2 = some m2'
  ∧ extends' m1' m2' := sorry

theorem store_outside_extends {chunk m1 m2 b ofs v m2'} :
  extends' m1 m2 →
  store chunk m2 b ofs v = some m2' →
  (∀ ofs', perm m1 b ofs' Cur Readable → ofs ≤ ofs' → ofs' < ofs + chunk.size → false) →
  extends' m1 m2' := sorry

theorem storev_extends {chunk m1 m2 addr1 v1 m1' addr2 v2} :
  extends' m1 m2 →
  storev chunk m1 addr1 v1 = some m1' →
  addr1.lessdef addr2 →
  v1.lessdef v2 →
  ∃ m2',
     storev chunk m2 addr2 v2 = some m2'
  ∧ extends' m1' m2' := sorry

theorem store_bytes_within_extends {m1 m2 b ofs bytes1 m1' bytes2} :
  extends' m1 m2 →
  store_bytes m1 b ofs bytes1 = some m1' →
  list.forall2 memval_lessdef bytes1 bytes2 →
  ∃ m2',
     store_bytes m2 b ofs bytes2 = some m2'
  ∧ extends' m1' m2' := sorry

theorem store_bytes_outside_extends {m1 m2 b ofs bytes2 m2'} :
  extends' m1 m2 →
  store_bytes m2 b ofs bytes2 = some m2' →
  (∀ ofs', perm m1 b ofs' Cur Readable → ofs ≤ ofs' → ofs' < ofs + bytes2.length → false) →
  extends' m1 m2' := sorry

theorem alloc_extends {m1 m2 lo1 hi1 lo2 hi2} :
  extends' m1 m2 →
  lo2 ≤ lo1 → hi1 ≤ hi2 →
  extends' (m1.alloc lo1 hi1) (m2.alloc lo2 hi2) := sorry

theorem free_left_extends {m1 m2 b lo hi m1'} :
  extends' m1 m2 →
  free m1 b lo hi = some m1' →
  extends' m1' m2 := sorry

theorem free_right_extends {m1 m2 b lo hi m2'} :
  extends' m1 m2 →
  free m2 b lo hi = some m2' →
  (∀ ofs k p, perm m1 b ofs k p → lo ≤ ofs → ofs < hi → false) →
  extends' m1 m2' := sorry

theorem free_parallel_extends {m1 m2 b lo hi m1'} :
  extends' m1 m2 →
  free m1 b lo hi = some m1' →
  ∃ m2',
     free m2 b lo hi = some m2'
  ∧ extends' m1' m2' := sorry

theorem valid_block_extends {m1 m2 b} :
  extends' m1 m2 →
  (valid_block m1 b ↔ valid_block m2 b) := sorry

theorem perm_extends {m1 m2 b ofs k p} :
  extends' m1 m2 → perm m1 b ofs k p → perm m2 b ofs k p := sorry

theorem perm_extends_inv {m1 m2 b ofs k p} :
  extends' m1 m2 → perm m1 b ofs Max Nonempty →
    perm m2 b ofs k p → perm m1 b ofs k p := sorry

theorem valid_access_extends {m1 m2 chunk b ofs p} :
  extends' m1 m2 → valid_access m1 chunk b ofs p → valid_access m2 chunk b ofs p := sorry

theorem valid_pointer_extends {m1 m2 b ofs} :
  extends' m1 m2 → valid_pointer m1 b ofs → valid_pointer m2 b ofs := sorry

theorem weak_valid_pointer_extends {m1 m2 b ofs} :
  extends' m1 m2 →
  weak_valid_pointer m1 b ofs → weak_valid_pointer m2 b ofs := sorry

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

structure inject (f : meminj) (m1 m2 : mem) : Prop :=
(mi_inj : mem_inj f m1 m2)
(mi_freeblocks : ∀ b, ¬ valid_block m1 b → f b = none)
(mi_mappedblocks : ∀ b b' delta, f b = some (b', delta) → valid_block m2 b')
(mi_no_overlap : meminj_no_overlap f m1)
(mi_representable : ∀ b b' delta (ofs : ptrofs),
  f b = some (b', delta) →
  perm m1 b (unsigned ofs) Max Nonempty ∨ perm m1 b (unsigned ofs - 1) Max Nonempty →
  delta.ex_nat (λd, unsigned ofs + d ≤ max_unsigned ptrofs.wordsize))
(mi_perm_inv : ∀ b1 ofs b2 delta k p,
  f b1 = some (b2, delta) →
  perm m1 b1 ofs Max Nonempty → 
  perm_Z m2 b2 (ofs + delta) k p → perm m1 b1 ofs k p)

/- Preservation of access validity and pointer validity -/

theorem valid_block_inject_1 {f : meminj} {m1 m2 b1 b2 delta} :
  f b1 = some (b2, delta) →
  inject f m1 m2 →
  valid_block m1 b1 := sorry

theorem valid_block_inject_2 {f : meminj} {m1 m2 b1 b2 delta} :
  f b1 = some (b2, delta) →
  inject f m1 m2 →
  valid_block m2 b2 := sorry

theorem perm_inject {f : meminj} {m1 m2 b1 b2 delta ofs k p} :
  f b1 = some (b2, delta) →
  inject f m1 m2 →
  perm m1 b1 ofs k p → perm_Z m2 b2 (ofs + delta) k p := sorry

theorem perm_inject_inv {f m1 m2 b1 ofs b2 delta k p} :
  inject f m1 m2 →
  f b1 = some (b2, delta) →
  perm m1 b1 ofs Max Nonempty →
  perm_Z m2 b2 (ofs + delta) k p →
  perm m1 b1 ofs k p := sorry

theorem range_perm_inject {f : meminj} {m1 m2 b1 b2 delta lo hi k p} :
  f b1 = some (b2, delta) →
  inject f m1 m2 →
  range_perm m1 b1 lo hi k p → range_perm_Z m2 b2 (lo + delta) (hi + delta) k p := sorry

theorem valid_access_inject {f : meminj} {m1 m2 chunk b1 ofs b2 delta p} :
  f b1 = some (b2, delta) →
  inject f m1 m2 →
  valid_access m1 chunk b1 ofs p →
  valid_access_Z m2 chunk b2 (ofs + delta) p := sorry

theorem valid_pointer_inject {f : meminj} {m1 m2 b1 ofs b2 delta} :
  f b1 = some (b2, delta) →
  inject f m1 m2 →
  valid_pointer m1 b1 ofs →
  (↑ofs + delta).ex_nat (λofs', valid_pointer m2 b2 ofs') := sorry

theorem weak_valid_pointer_inject {f : meminj} {m1 m2 b1 ofs b2 delta} :
  f b1 = some (b2, delta) →
  inject f m1 m2 →
  weak_valid_pointer m1 b1 ofs →
  (↑ofs + delta).ex_nat (λofs', weak_valid_pointer m2 b2 ofs') := sorry

/- The following lemmas establish the absence of machine integer overflow
  during address computations. -/

lemma address_inject {f m1 m2 b1} {ofs1 : ptrofs} {b2 delta p} :
  inject f m1 m2 →
  perm m1 b1 (unsigned ofs1) Cur p →
  f b1 = some (b2, delta) →
  ↑(unsigned (ofs1 + repr delta)) = ↑(unsigned ofs1) + delta := sorry

lemma address_inject' {f m1 m2 chunk b1} {ofs1 : ptrofs} {b2 delta} :
  inject f m1 m2 →
  valid_access m1 chunk b1 (unsigned ofs1) Nonempty →
  f b1 = some (b2, delta) →
  ↑(unsigned (ofs1 + repr delta)) = ↑(unsigned ofs1) + delta := sorry

theorem weak_valid_pointer_inject_no_overflow {f m1 m2 b} {ofs : ptrofs} {b' delta} :
  inject f m1 m2 →
  weak_valid_pointer m1 b (unsigned ofs) →
  f b = some (b', delta) →
  unsigned ofs + unsigned (repr delta : ptrofs) ≤ max_unsigned ptrofs.wordsize := sorry

theorem valid_pointer_inject_no_overflow {f m1 m2 b} {ofs : ptrofs} {b' delta} :
  inject f m1 m2 →
  valid_pointer m1 b (unsigned ofs) →
  f b = some (b', delta) →
  unsigned ofs + unsigned (repr delta : ptrofs) ≤ max_unsigned ptrofs.wordsize := sorry

theorem valid_pointer_inject_val {f m1 m2 b ofs b' ofs'} :
  inject f m1 m2 →
  valid_pointer m1 b (unsigned ofs) →
  val.inject f (Vptr b ofs) (Vptr b' ofs') →
  valid_pointer m2 b' (unsigned ofs') := sorry

theorem weak_valid_pointer_inject_val {f m1 m2 b ofs b' ofs'} :
  inject f m1 m2 →
  weak_valid_pointer m1 b (unsigned ofs) →
  val.inject f (Vptr b ofs) (Vptr b' ofs') →
  weak_valid_pointer m2 b' (unsigned ofs') := sorry

theorem inject_no_overlap {f m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2} :
  inject f m1 m2 →
  b1 ≠ b2 →
  f b1 = some (b1', delta1) →
  f b2 = some (b2', delta2) →
  perm m1 b1 ofs1 Max Nonempty →
  perm m1 b2 ofs2 Max Nonempty →
  b1' ≠ b2' ∨ ↑ofs1 + delta1 ≠ ofs2 + delta2 := sorry

theorem different_pointers_inject {f m m' b1 b2} {ofs1 ofs2 : ptrofs} {b1' delta1 b2' delta2} :
  inject f m m' →
  b1 ≠ b2 →
  valid_pointer m b1 (unsigned ofs1) →
  valid_pointer m b2 (unsigned ofs2) →
  f b1 = some (b1', delta1) →
  f b2 = some (b2', delta2) →
  b1' ≠ b2' ∨
  unsigned (ofs1 + repr delta1) ≠
  unsigned (ofs2 + repr delta2) := sorry

theorem disjoint_or_equal_inject {f m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz} :
  inject f m m' →
  f b1 = some (b1', delta1) →
  f b2 = some (b2', delta2) →
  range_perm m b1 ofs1 (ofs1 + sz) Max Nonempty →
  range_perm m b2 ofs2 (ofs2 + sz) Max Nonempty →
  sz > 0 →
  b1 ≠ b2 ∨ ofs1 = ofs2 ∨ ofs1 + sz ≤ ofs2 ∨ ofs2 + sz ≤ ofs1 →
  b1' ≠ b2' ∨ ↑ofs1 + delta1 = ofs2 + delta2
             ∨ ↑ofs1 + delta1 + sz ≤ ofs2 + delta2
             ∨ ↑ofs2 + delta2 + sz ≤ ofs1 + delta1 := sorry

theorem aligned_area_inject {f m m' b ofs al sz b' delta} :
  inject f m m' →
  al = 1 ∨ al = 2 ∨ al = 4 ∨ al = 8 → sz > 0 →
  al ∣ sz →
  range_perm m b ofs (ofs + sz) Cur Nonempty →
  al ∣ ofs →
  f b = some (b', delta) →
  ↑al ∣ ↑ofs + delta := sorry

/- Preservation of loads -/

theorem load_inject {f m1 m2 chunk b1 ofs b2 delta v1} :
  inject f m1 m2 →
  load chunk m1 b1 ofs = some v1 →
  f b1 = some (b2, delta) →
  (↑ofs + delta).ex_nat (λ ofs',
    ∃ v2, load chunk m2 b2 ofs' = some v2 ∧ val.inject f v1 v2) := sorry

theorem loadv_inject {f m1 m2 chunk a1 a2 v1} :
  inject f m1 m2 →
  loadv chunk m1 a1 = some v1 →
  val.inject f a1 a2 →
  ∃ v2, loadv chunk m2 a2 = some v2 ∧ val.inject f v1 v2 := sorry

theorem load_bytes_inject {f m1 m2 b1 ofs len b2 delta bytes1} :
  inject f m1 m2 →
  load_bytes m1 b1 ofs len = some bytes1 →
  f b1 = some (b2, delta) →
  (↑ofs + delta).ex_nat (λofs',
  ∃ bytes2, load_bytes m2 b2 ofs' len = some bytes2
              ∧ list.forall2 (memval_inject f) bytes1 bytes2) := sorry

/- Preservation of stores -/

theorem store_mapped_inject {f chunk m1 b1 ofs v1 n1 m2 b2 delta v2} :
  inject f m1 m2 →
  store chunk m1 b1 ofs v1 = some n1 →
  f b1 = some (b2, delta) →
  val.inject f v1 v2 →
  (↑ofs + delta).ex_nat (λofs', ∃ n2,
    store chunk m2 b2 ofs' v2 = some n2
    ∧ inject f n1 n2) := sorry

theorem store_unmapped_inject {f chunk m1 b1 ofs v1 n1 m2} :
  inject f m1 m2 →
  store chunk m1 b1 ofs v1 = some n1 →
  f b1 = none →
  inject f n1 m2 := sorry

theorem store_outside_inject {f m1 m2} {chunk : memory_chunk} {b ofs v m2'} :
  inject f m1 m2 →
  (∀ b' delta ofs',
    f b' = some (b, delta) →
    perm m1 b' ofs' Cur Readable →
    ↑ofs ≤ ↑ofs' + delta → ↑ofs' + delta < ↑ofs + chunk.size → false) →
  store chunk m2 b ofs v = some m2' →
  inject f m1 m2' := sorry

theorem storev_mapped_inject {f chunk m1 a1 v1 n1 m2 a2 v2} :
  inject f m1 m2 →
  storev chunk m1 a1 v1 = some n1 →
  val.inject f a1 a2 →
  val.inject f v1 v2 →
  ∃ n2, storev chunk m2 a2 v2 = some n2 ∧ inject f n1 n2 := sorry

theorem store_bytes_mapped_inject {f m1 b1 ofs bytes1 n1 m2 b2 delta bytes2} :
  inject f m1 m2 →
  store_bytes m1 b1 ofs bytes1 = some n1 →
  f b1 = some (b2, delta) →
  list.forall2 (memval_inject f) bytes1 bytes2 →
  (↑ofs + delta).ex_nat (λofs',
  ∃ n2,
    store_bytes m2 b2 ofs' bytes2 = some n2
    ∧ inject f n1 n2) := sorry

theorem store_bytes_unmapped_inject {f m1 b1 ofs bytes1 n1 m2} :
  inject f m1 m2 →
  store_bytes m1 b1 ofs bytes1 = some n1 →
  f b1 = none →
  inject f n1 m2 := sorry

theorem store_bytes_outside_inject {f m1 m2 b ofs bytes2 m2'} :
  inject f m1 m2 →
  (∀ b' delta ofs',
    f b' = some (b, delta) →
    perm m1 b' ofs' Cur Readable →
    ↑ofs ≤ ↑ofs' + delta → ↑ofs' + delta < ↑ofs + bytes2.length → false) →
  store_bytes m2 b ofs bytes2 = some m2' →
  inject f m1 m2' := sorry

theorem store_bytes_empty_inject {f m1 b1 ofs1 m1' m2 b2 ofs2 m2'} :
  inject f m1 m2 →
  store_bytes m1 b1 ofs1 [] = some m1' →
  store_bytes m2 b2 ofs2 [] = some m2' →
  inject f m1' m2' := sorry

/- Preservation of allocations -/

theorem alloc_right_inject {f m1 m2 lo hi} :
  inject f m1 m2 →
  inject f m1 (m2.alloc lo hi) := sorry

theorem alloc_left_unmapped_inject {f m1 m2 lo hi} :
  inject f m1 m2 →
  ∃ f',
     inject f' (m1.alloc lo hi) m2
  ∧ inject_incr f f'
  ∧ f' m1.nextblock = none
  ∧ (∀ b, b ≠ m1.nextblock → f' b = f b) := sorry

theorem alloc_left_mapped_inject {f m1 m2 lo hi b2 delta} :
  inject f m1 m2 →
  valid_block m2 b2 →
  delta ≤ max_unsigned ptrofs.wordsize →
  (∀ ofs k p, perm m2 b2 ofs k p → delta = 0 ∨ ofs < max_unsigned ptrofs.wordsize) →
  (∀ ofs k p, lo ≤ ofs → ofs < hi → perm m2 b2 (ofs + delta) k p) →
  inj_offset_aligned delta (hi-lo) →
  (∀ b delta' ofs k p,
   f b = some (b2, delta') →
   perm m1 b ofs k p →
   (lo + delta : ℤ) ≤ ofs + delta' → ↑ofs + delta' < hi + delta → false) →
  ∃ f',
     inject f' (m1.alloc lo hi) m2
  ∧ inject_incr f f'
  ∧ f' m1.nextblock = some (b2, delta)
  ∧ (∀ b, b ≠ m1.nextblock → f' b = f b) := sorry

theorem alloc_parallel_inject {f m1 m2 lo1 hi1 lo2 hi2} :
  inject f m1 m2 →
  lo2 ≤ lo1 → hi1 ≤ hi2 →
  ∃ f', 
    inject f' (m1.alloc lo1 hi1) (m2.alloc lo2 hi2)
  ∧ inject_incr f f'
  ∧ f' m1.nextblock = some (m2.nextblock, 0)
  ∧ (∀ b, b ≠ m1.nextblock → f' b = f b) := sorry

/- Preservation of [free] operations -/

lemma free_left_inject {f m1 m2 b lo hi m1'} :
  inject f m1 m2 →
  free m1 b lo hi = some m1' →
  inject f m1' m2 := sorry

lemma free_list_left_inject {f m2 l m1 m1'} :
  inject f m1 m2 →
  free_list m1 l = some m1' →
  inject f m1' m2 := sorry

lemma free_right_inject {f m1 m2 b lo hi m2'} :
  inject f m1 m2 →
  free m2 b lo hi = some m2' →
  (∀ b1 delta ofs k p,
    f b1 = some (b, delta) → perm m1 b1 ofs k p →
    ↑lo ≤ ↑ofs + delta → ↑ofs + delta < hi → false) →
  inject f m1 m2' := sorry

lemma perm_free_list {l m m' b ofs k p} :
  free_list m l = some m' →
  perm m' b ofs k p →
  perm m b ofs k p ∧
  (∀ lo hi, (b, lo, hi) ∈ l → lo ≤ ofs → ofs < hi → false) := sorry

theorem free_inject {f m1 l m1' m2 b lo hi m2'} :
  inject f m1 m2 →
  free_list m1 l = some m1' →
  free m2 b lo hi = some m2' →
  (∀ b1 delta ofs k p,
    f b1 = some (b, delta) →
    perm m1 b1 ofs k p → ↑lo ≤ ↑ofs + delta → ↑ofs + delta < hi →
    ∃ lo1, ∃ hi1, (b1, lo1, hi1) ∈ l ∧ lo1 ≤ ofs ∧ ofs < hi1) →
  inject f m1' m2' := sorry

theorem free_parallel_inject {f m1 m2 b lo hi m1' b' delta} :
  inject f m1 m2 →
  free m1 b lo hi = some m1' →
  f b = some (b', delta) →
  (↑lo + delta).ex_nat (λ lo',
  (↑hi + delta).ex_nat (λ hi',
  ∃ m2', free m2 b' lo' hi' = some m2' ∧ inject f m1' m2')) := sorry

lemma drop_outside_inject : ∀ f m1 m2 b lo hi p m2',
  inject f m1 m2 →
  drop_perm m2 b lo hi p = some m2' →
  (∀ b' delta ofs k p,
    f b' = some (b, delta) →
    perm m1 b' ofs k p → ↑lo ≤ ↑ofs + delta → ↑ofs + delta < hi → false) →
  inject f m1 m2' := sorry

/- Composing two memory injections. -/

lemma mem_inj_compose {f f' m1 m2 m3} :
  mem_inj f m1 m2 → mem_inj f' m2 m3 → mem_inj (f.comp f') m1 m3 := sorry

theorem inject_compose {f f' m1 m2 m3} :
  inject f m1 m2 → inject f' m2 m3 →
  inject (f.comp f') m1 m3 := sorry

lemma val_lessdef_inject_compose {f v1 v2 v3} :
  val.lessdef v1 v2 → val.inject f v2 v3 → val.inject f v1 v3 := sorry

lemma val_inject_lessdef_compose {f v1 v2 v3} :
  val.inject f v1 v2 → val.lessdef v2 v3 → val.inject f v1 v3 := sorry

lemma extends_inject_compose {f m1 m2 m3} :
  extends' m1 m2 → inject f m2 m3 → inject f m1 m3 := sorry

lemma inject_extends_compose {f m1 m2 m3} :
  inject f m1 m2 → extends' m2 m3 → inject f m1 m3 := sorry

lemma extends_extends_compose {m1 m2 m3} :
  extends' m1 m2 → extends' m2 m3 → extends' m1 m3 := sorry

/- Injecting a memory into itself. -/

def flat_inj (thr : block) : meminj :=
  λ (b : block), if b < thr then some (b, 0) else none

def inject_neutral (thr : block) (m : mem) :=
  mem_inj (flat_inj thr) m m

theorem flat_inj_no_overlap {thr m} : meminj_no_overlap (flat_inj thr) m := sorry

theorem neutral_inject {m : mem} :
  inject_neutral m.nextblock m → inject (flat_inj m.nextblock) m m := sorry

theorem empty_inject_neutral {thr} : inject_neutral thr ∅ := sorry

theorem alloc_inject_neutral {thr m lo hi} :
  inject_neutral thr m →
  m.nextblock < thr →
  inject_neutral thr (m.alloc lo hi) := sorry

theorem store_inject_neutral {chunk m b ofs v m' thr} :
  store chunk m b ofs v = some m' →
  inject_neutral thr m →
  b < thr →
  val.inject (flat_inj thr) v v →
  inject_neutral thr m' := sorry

theorem drop_inject_neutral {m b lo hi p m' thr} :
  drop_perm m b lo hi p = some m' →
  inject_neutral thr m →
  b < thr →
  inject_neutral thr m' := sorry

/- * Invariance properties between two memory states -/

section unchanged_on

parameter P : block → ℕ → Prop

structure unchanged_on (m_before m_after : mem) : Prop :=
(nextblock : m_before.nextblock ≤ m_after.nextblock)
(perm : ∀ b ofs k p,
  P b ofs → valid_block m_before b →
  (perm m_before b ofs k p ↔ perm m_after b ofs k p))
(unchanged_on_contents : ∀ b ofs,
  P b ofs → memory.perm m_before b ofs Cur Readable →
  get1 ofs (m_after.get_block b) =
  get1 ofs (m_before.get_block b))

lemma unchanged_on_refl {m} : unchanged_on m m := sorry

lemma valid_block_unchanged_on {m m' b} :
  unchanged_on m m' → valid_block m b → valid_block m' b := sorry

lemma perm_unchanged_on {m m' b ofs k p} :
  unchanged_on m m' → P b ofs →
  perm m b ofs k p → perm m' b ofs k p := sorry

lemma perm_unchanged_on_2 {m m' b ofs k p} :
  unchanged_on m m' → P b ofs → valid_block m b →
  perm m' b ofs k p → perm m b ofs k p := sorry

lemma unchanged_on_trans {m1 m2 m3} : unchanged_on m1 m2 → unchanged_on m2 m3 → unchanged_on m1 m3 := sorry

lemma load_bytes_unchanged_on_1 {m m' b ofs n} :
  unchanged_on m m' →
  valid_block m b →
  (∀ i, ofs ≤ i → i < ofs + n → P b i) →
  load_bytes m' b ofs n = load_bytes m b ofs n := sorry

lemma load_bytes_unchanged_on {m m' b ofs n bytes} :
  unchanged_on m m' →
  (∀ i, ofs ≤ i → i < ofs + n → P b i) →
  load_bytes m b ofs n = some bytes →
  load_bytes m' b ofs n = some bytes := sorry

lemma load_unchanged_on_1 {m m' b ofs} {chunk : memory_chunk} :
  unchanged_on m m' →
  valid_block m b →
  (∀ i, ofs ≤ i → i < ofs + chunk.size → P b i) →
  load chunk m' b ofs = load chunk m b ofs := sorry

lemma load_unchanged_on {m m' b ofs v} {chunk : memory_chunk}  :
  unchanged_on m m' →
  (∀ i, ofs ≤ i → i < ofs + chunk.size → P b i) →
  load chunk m b ofs = some v →
  load chunk m' b ofs = some v := sorry

lemma store_unchanged_on {chunk m b ofs v m'} :
  store chunk m b ofs v = some m' →
  (∀ i, ofs ≤ i → i < ofs + chunk.size → ¬ P b i) →
  unchanged_on m m' := sorry

lemma store_bytes_unchanged_on {m b ofs bytes m'} :
  store_bytes m b ofs bytes = some m' →
  (∀ i, ofs ≤ i → i < ofs + bytes.length → ¬ P b i) →
  unchanged_on m m' := sorry

lemma alloc_unchanged_on {m lo hi} :
  unchanged_on m (m.alloc lo hi) := sorry

lemma free_unchanged_on {m b lo hi m'} :
  free m b lo hi = some m' →
  (∀ i, lo ≤ i → i < hi → ¬ P b i) →
  unchanged_on m m' := sorry

lemma drop_perm_unchanged_on {m b lo hi p m'} :
  drop_perm m b lo hi p = some m' →
  (∀ i, lo ≤ i → i < hi → ¬ P b i) →
  unchanged_on m m' := sorry

end unchanged_on

lemma unchanged_on_implies (P Q : block → ℕ → Prop) {m m'} :
  (∀ b ofs, Q b ofs → valid_block m b → P b ofs) →
  unchanged_on P m m' → unchanged_on Q m m' := sorry

end memory