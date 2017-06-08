
/- Global environments are a component of the dynamic semantics of
  all languages involved in the compiler.  A global environment
  maps symbol names (names of functions and of global variables)
  to the corresponding memory addresses.  It also maps memory addresses
  of functions to the corresponding function descriptions.

  Global environments, along with the initial memory state at the beginning
  of program execution, are built from the program of interest, as follows:
- A distinct memory address is assigned to each function of the program.
  These function addresses use negative numbers to distinguish them from
  addresses of memory blocks.  The associations of function name to function
  address and function address to function description are recorded in
  the global environment.
- For each global variable, a memory block is allocated and associated to
  the name of the variable.

  These operations reflect (at a high level of abstraction) what takes
  place during program linking and program loading in a real operating
  system. -/

import .memory .linking

namespace globalenvs
open memdata memory values ast integers maps linking errors
     memdata.memval word floats memdata.quantity memory.perm_kind
     ast.memory_chunk

/- Auxiliary function for initialization of global variables. -/

def store_zeros : mem → block → ℕ → ℕ → option mem
| m b p 0     := some m
| m b p (n+1) := do m' ← store Mint8unsigned m b p Vzero, store_zeros m' b (p + 1) n

/- * Symbol environments -/

/- Symbol environments are a restricted view of global environments,
  focusing on symbol names and their associated blocks.  They do not
  contain mappings from blocks to function or variable definitions. -/

structure senv : Type :=
(find_symbol : ident → option block)
(public_symbol : ident → bool)
(invert_symbol : block → option ident)
(block_is_volatile : block → bool)
(nextblock : block)
  /- Properties -/
(find_symbol_injective : ∀ {id1 id2 b}, find_symbol id1 = some b → find_symbol id2 = some b → id1 = id2)
(invert_find_symbol : ∀ {id b}, invert_symbol b = some id → find_symbol id = some b)
(find_invert_symbol : ∀ {id b}, find_symbol id = some b → invert_symbol b = some id)
(public_symbol_exists : ∀ {id}, public_symbol id → ∃ b, find_symbol id = some b)
(find_symbol_below : ∀ {id b}, find_symbol id = some b → b < nextblock)
(block_is_volatile_below : ∀ {b}, block_is_volatile b → b < nextblock)

namespace senv

def symbol_address (ge : senv) (id : ident) (ofs : ptrofs) : val :=
  match find_symbol ge id with
| some b := Vptr b ofs
| none := Vundef
  end

theorem shift_symbol_address {ge id ofs delta} :
  symbol_address ge id (ofs + delta) = val.offset_ptr (symbol_address ge id ofs) delta := sorry'

theorem shift_symbol_address_32 {ge id ofs n} : ¬ archi.ptr64 →
  symbol_address ge id (ofs + ptrofs.of_int n) = symbol_address ge id ofs + n := sorry'

theorem shift_symbol_address_64 {ge id ofs n} : archi.ptr64 →
  symbol_address ge id (ofs + ptrofs.of_int64 n) = (symbol_address ge id ofs).addl n := sorry'

def equiv (se1 se2 : senv) : Prop :=
     (∀ id, find_symbol se2 id = find_symbol se1 id)
  ∧ (∀ id, public_symbol se2 id = public_symbol se1 id)
  ∧ (∀ b, block_is_volatile se2 b = block_is_volatile se1 b)

end senv

/- * Global environments -/

/- The type of global environments. -/

structure genv (F V : Type) : Type :=
(public : list ident)              /- which symbol names are public -/
(symb : PTree block)             /- mapping symbol -> block -/
(defs : PTree (globdef F V))     /- mapping block -> definition -/
(next : block)                     /- next symbol pointer -/
(symb_range : ∀ {id b}, PTree.get id symb = some b → b < next)
(defs_range : ∀ {b g}, PTree.get b defs = some g → b < next)
(vars_inj : ∀ {id1 id2 b},
    PTree.get id1 symb = some b → PTree.get id2 symb = some b → id1 = id2)

namespace genv
section

variable {F : Type}  /- The type of function descriptions -/
variable {V : Type}  /- The type of information attached to variables -/

/- ** Lookup functions -/

/- [find_symbol ge id] returns the block associated with the given name, if any -/

def find_symbol (ge : genv F V) (id : ident) : option block :=
  PTree.get id ge.symb

/- [symbol_address ge id ofs] returns a pointer into the block associated
  with [id], at byte offset [ofs].  [Vundef] is returned if no block is associated
  to [id]. -/

def symbol_address (ge : genv F V) (id : ident) (ofs : ptrofs) : val :=
  match find_symbol ge id with
| some b := Vptr b ofs
| none := Vundef
  end

/- [public_symbol ge id] says whether the name [id] is public and defined. -/

def public_symbol (ge : genv F V) (id : ident) : bool :=
(find_symbol ge id).is_some && (id ∈ ge.public)

/- [find_def ge b] returns the global definition associated with the given address. -/

def find_def (ge : genv F V) (b : block) : option (globdef F V) :=
PTree.get b ge.defs

/- [find_funct_ptr ge b] returns the function description associated with
    the given address. -/

def find_funct_ptr (ge : genv F V) (b : block) : option F :=
match find_def ge b with some (Gfun f) := some f | _ := none end

/- [find_funct] is similar to [find_funct_ptr], but the function address
    is given as a value, which must be a pointer with offset 0. -/

def find_funct (ge : genv F V) : val → option F
| (Vptr b ofs) := if ofs = 0 then find_funct_ptr ge b else none
| _ := none

/- [invert_symbol ge b] returns the name associated with the given block, if any -/

def invert_symbol (ge : genv F V) (b : block) : option ident :=
PTree.fold
  (λ res id b', if b = b' then some id else res)
  ge.symb none

/- [find_var_info ge b] returns the information attached to the variable
   at address [b]. -/

def find_var_info (ge : genv F V) (b : block) : option (globvar V) :=
match find_def ge b with some (Gvar v) := some v | _ := none end

/- [block_is_volatile ge b] returns [true] if [b] points to a global variable
  of volatile type, [false] otherwise. -/

def block_is_volatile (ge : genv F V) (b : block) : bool :=
match find_var_info ge b with
| none := ff
| some gv := gv.volatile
end

/- ** Constructing the global environment -/

def add_global (ge : genv F V) : ident × globdef F V → genv F V | (id, g) :=
{ public := ge.public,
  symb := PTree.set id ge.next ge.symb,
  defs := PTree.set ge.next g ge.defs,
  next := ge.next.succ,
  symb_range := λid' b h, show (_:ℕ)<_, begin
    rw pos_num.succ_to_nat,
    apply nat.lt_succ_of_le,
    rw PTree.gsspec at h,
    by_cases id' = id with ii; simp [ii] at h,
    { injection h, rw h },
    { exact le_of_lt (ge.symb_range h) }
  end,
  defs_range := λb g' h, show (_:ℕ)<_, begin
    rw pos_num.succ_to_nat,
    apply nat.lt_succ_of_le,
    rw PTree.gsspec at h,
    by_cases b = ge.next with bb,
    { rw bb },
    { simp [bb] at h, exact le_of_lt (ge.defs_range h) }
  end,
  vars_inj := λid1 id2 b h1 h2, begin
    rw PTree.gsspec at h1 h2,
    by_cases id1 = id with i1; simp [i1] at h1;
    by_cases id2 = id with i2; simp [i2] at h2; try {simp [i1, i2]},
    { rw -h1 at h2, exact absurd (ge.symb_range h2) (lt_irrefl _) },
    { rw -h2 at h1, exact absurd (ge.symb_range h1) (lt_irrefl _) },
    { exact ge.vars_inj h1 h2 },
  end }

def add_globals (ge : genv F V) (gl : list (ident × globdef F V)) : genv F V :=
gl.foldl add_global ge

lemma add_globals_app (ge : genv F V) (gl2 gl1) :
  add_globals ge (gl1 ++ gl2) = add_globals (add_globals ge gl1) gl2 := sorry'

def empty (pub : list ident) : genv F V :=
{ public := pub,
  symb := ∅,
  defs := ∅,
  next := 1,
  symb_range := λid' b h, by rw PTree.gempty at h; contradiction,
  defs_range := λb g' h, by rw PTree.gempty at h; contradiction,
  vars_inj := λid1 id2 b h, by rw PTree.gempty at h; contradiction }

def globalenv (p : program F V) : genv F V := add_globals (empty p.public) p.defs

/- Proof principles -/

section globalenv_principles

variable P : genv F V → Prop
include P

lemma add_globals_preserves {gl ge} :
  (∀ ge id g, P ge → (id, g) ∈ gl → P (add_global ge (id, g))) →
  P ge → P (add_globals ge gl) := sorry'

lemma add_globals_ensures {id g gl ge} :
  (∀ ge id g, P ge → (id, g) ∈ gl → P (add_global ge (id, g))) →
  (∀ ge, P (add_global ge (id, g))) →
  (id, g) ∈ gl → P (add_globals ge gl) := sorry'

lemma add_globals_unique_preserves {id gl ge} :
  (∀ ge id1 g, P ge → (id1, g) ∈ gl → id1 ≠ id → P (add_global ge (id1, g))) →
  id ∉ list.map prod.fst gl → P ge → P (add_globals ge gl) := sorry'

lemma add_globals_unique_ensures {gl1 id g gl2 ge} :
  (∀ ge id1 g1, P ge → (id1, g1) ∈ gl2 → id1 ≠ id → P (add_global ge (id1, g1))) →
  (∀ ge, P (add_global ge (id, g))) →
  id ∉ list.map prod.fst gl2 → P (add_globals ge (gl1 ++ (id, g) :: gl2)) := sorry'

theorem in_norepet_unique {id g} {gl : list (ident × globdef F V)} :
  (id, g) ∈ gl → (gl.map prod.fst).nodup →
  ∃ gl1 gl2, gl = gl1 ++ (id, g) :: gl2 ∧ id ∈ gl2.map prod.fst := sorry'

lemma add_globals_norepet_ensures {id g gl ge} :
  (∀ ge id1 g1, P ge → (id1, g1) ∈ gl → id1 ≠ id → P (add_global ge (id1, g1))) →
  (∀ ge, P (add_global ge (id, g))) →
  (id, g) ∈ gl → (list.map prod.fst gl).nodup → P (add_globals ge gl) := sorry'

end globalenv_principles

/- ** Properties of the operations over global environments -/

theorem public_symbol_exists {ge : genv F V} {id} :
  public_symbol ge id → ∃ b, find_symbol ge id = some b := sorry'

theorem shift_symbol_address {ge : genv F V} {id ofs delta} :
  symbol_address ge id (ofs + delta) = (symbol_address ge id ofs).offset_ptr delta := sorry'

theorem shift_symbol_address_32 {ge : genv F V} {id ofs n} :
  ¬ archi.ptr64 →
  symbol_address ge id (ofs + ptrofs.of_int n) = symbol_address ge id ofs + n := sorry'

theorem shift_symbol_address_64 {ge : genv F V} {id ofs n} :
  archi.ptr64 →
  symbol_address ge id (ofs + ptrofs.of_int64 n) = (symbol_address ge id ofs).addl n := sorry'

theorem find_funct_inv {ge : genv F V} {v f} :
  find_funct ge v = some f → ∃ b, v = Vptr b 0 := sorry'

theorem find_funct_find_funct_ptr {ge : genv F V} {b} :
  find_funct ge (Vptr b 0) = find_funct_ptr ge b := sorry'

theorem find_funct_ptr_iff {ge : genv F V} {b f} :
  find_funct_ptr ge b = some f ↔ find_def ge b = some (Gfun f) := sorry'

theorem find_var_info_iff {ge : genv F V} {b v} :
  find_var_info ge b = some v ↔ find_def ge b = some (Gvar v) := sorry'

theorem find_def_symbol {p : program F V} {id g} :
  (prog_defmap p^!id) = some g ↔
  ∃ b, find_symbol (globalenv p) id = some b ∧
       find_def (globalenv p) b = some g := sorry'

theorem find_symbol_exists {p : program F V} {id g} :
  (id, g) ∈ p.defs →
  ∃ b, find_symbol (globalenv p) id = some b := sorry'

theorem find_symbol_inversion {p : program F V} {x b} :
  find_symbol (globalenv p) x = some b →
  x ∈ p.defs_names := sorry'

theorem find_def_inversion {p : program F V} {b g} :
  find_def (globalenv p) b = some g →
  ∃ id, (id, g) ∈ p.defs := sorry'

theorem find_funct_ptr_inversion {p : program F V} {b f} :
  find_funct_ptr (globalenv p) b = some f →
  ∃ id, (id, Gfun f) ∈ p.defs := sorry'

theorem find_funct_inversion {p : program F V} {v f} :
  find_funct (globalenv p) v = some f →
  ∃ id, (id, Gfun f) ∈ p.defs := sorry'

theorem find_funct_ptr_prop (P : F → Prop) {p : program F V} {b f} :
  (∀ id f, (id, Gfun f) ∈ p.defs → P f) →
  find_funct_ptr (globalenv p) b = some f →
  P f := sorry'

theorem find_funct_prop (P : F → Prop) {p : program F V} {v f} :
  (∀ id f, (id, Gfun f) ∈ p.defs → P f) →
  find_funct (globalenv p) v = some f →
  P f := sorry'

theorem global_addresses_distinct {ge : genv F V} {id1 id2 b1 b2} :
  id1 ≠ id2 →
  find_symbol ge id1 = some b1 →
  find_symbol ge id2 = some b2 →
  b1 ≠ b2 := sorry'

theorem invert_find_symbol {ge : genv F V} {id b} :
  invert_symbol ge b = some id → find_symbol ge id = some b := sorry'

theorem find_invert_symbol {ge : genv F V} {id b} :
  find_symbol ge id = some b → invert_symbol ge b = some id := sorry'

def advance_next (gl : list (ident × globdef F V)) (x : pos_num) :=
gl.foldl (λ n g, pos_num.succ n) x

theorem genv_next_add_globals (gl) (ge : genv F V) :
  (add_globals ge gl).next = advance_next gl ge.next := sorry'

theorem genv_public_add_globals (gl) (ge : genv F V) :
  (add_globals ge gl).public = ge.public := sorry'

theorem globalenv_public (p : program F V) :
  (globalenv p).public = p.public := sorry'

theorem block_is_volatile_below {ge : genv F V} {b} :
  block_is_volatile ge b → b < ge.next := sorry'

/- ** Coercing a global environment into a symbol environment -/

def to_senv (ge : genv F V) : senv :=
{ find_symbol := ge.find_symbol,
  public_symbol := ge.public_symbol,
  invert_symbol := ge.invert_symbol,
  block_is_volatile := ge.block_is_volatile,
  nextblock := ge.next,
  find_symbol_injective := ge.vars_inj,
  invert_find_symbol := ge.invert_find_symbol,
  find_invert_symbol := ge.find_invert_symbol,
  public_symbol_exists := ge.public_symbol_exists,
  find_symbol_below := ge.symb_range,
  block_is_volatile_below := ge.block_is_volatile_below }

instance : has_coe (genv F V) senv := ⟨to_senv⟩

/- * Construction of the initial memory state -/

section init_mem

variable ge : genv F V

def store_init_data (m : mem) (b : block) (p : ℕ) : init_data → option mem
| (init_data.int8 n) := store Mint8unsigned m b p (Vint n)
| (init_data.int16 n) := store Mint16unsigned m b p (Vint n)
| (init_data.int32 n) := store Mint32 m b p (Vint n)
| (init_data.int64 n) := store Mint64 m b p (Vlong n)
| (init_data.float32 n) := store Mfloat32 m b p (Vsingle n)
| (init_data.float64 n) := store Mfloat64 m b p (Vfloat n)
| (init_data.addrof symb ofs) :=
  do b' ← find_symbol ge symb, store Mptr m b p (Vptr b' ofs)
| (init_data.space n) := some m

def store_init_data_list : mem → block → ℕ → list init_data → option mem
| m b p [] := some m
| m b p (id :: idl') :=
  do m' ← store_init_data ge m b p id,
     store_init_data_list m' b (p + id.size) idl'

def perm_globvar (gv : globvar V) : permission :=
  if gv.volatile then Nonempty
  else if gv.readonly then Readable
  else Writable

def alloc_global (m : mem) : ident × globdef F V → option mem
| (id, Gfun f) :=
  drop_perm (m.alloc 0 1) m.nextblock 0 1 Nonempty
| (id, Gvar v) := do
  let init := v.init,
  let sz := init_data.list_size init,
  let b := m.nextblock,
  let m1 := m.alloc 0 sz,
  m2 ← store_zeros m1 b 0 sz,
  m3 ← store_init_data_list ge m2 b 0 init,
  drop_perm m3 b 0 sz (perm_globvar v)

def alloc_globals : mem → list (ident × globdef F V) → option mem :=
mfoldl (alloc_global ge)

lemma alloc_globals_app {gl1 gl2 m m1} :
  alloc_globals ge m gl1 = some m1 →
  alloc_globals ge m1 gl2 = alloc_globals ge m (gl1 ++ gl2) := sorry'

/- Next-block properties -/

theorem store_zeros_nextblock {m b p n m'} : store_zeros m b p n = some m' →
  m'.nextblock = m.nextblock := sorry'

theorem store_init_data_list_nextblock {idl b m p m'} :
  store_init_data_list ge m b p idl = some m' →
  m'.nextblock = m.nextblock := sorry'

theorem alloc_global_nextblock {g m m'} :
  alloc_global ge m g = some m' →
  m'.nextblock = m.nextblock.succ := sorry'

theorem alloc_globals_nextblock {gl m m'} :
  alloc_globals ge m gl = some m' →
  m'.nextblock = advance_next gl m.nextblock := sorry'

/- Permissions -/

theorem store_zeros_perm {k prm b' q m b p n m'} :
  store_zeros m b p n = some m' →
  (perm m b' q k prm ↔ perm m' b' q k prm) := sorry'

theorem store_init_data_perm {k prm b' q i b m p m'} :
  store_init_data ge m b p i = some m' →
  (perm m b' q k prm ↔ perm m' b' q k prm) := sorry'

theorem store_init_data_list_perm {k prm b' q idl b m p m'} :
  store_init_data_list ge m b p idl = some m' →
  (perm m b' q k prm ↔ perm m' b' q k prm) := sorry'

theorem alloc_global_perm {k prm b' q idg m m'} :
  alloc_global ge m idg = some m' →
  valid_block m b' →
  (perm m b' q k prm ↔ perm m' b' q k prm) := sorry'

theorem alloc_globals_perm {k prm b' q gl m m'} :
  alloc_globals ge m gl = some m' →
  valid_block m b' →
  (perm m b' q k prm ↔ perm m' b' q k prm) := sorry'

/- Data preservation properties -/

theorem store_zeros_unchanged {P : block → ℕ → Prop} {m b p n m'} :
  store_zeros m b p n = some m' →
  (∀ i, p ≤ i → i < p + n → ¬ P b i) →
  unchanged_on P m m' := sorry'

theorem store_init_data_unchanged {P : block → ℕ → Prop} {b i m p m'} :
  store_init_data ge m b p i = some m' →
  (∀ ofs, p ≤ ofs → ofs < p + i.size → ¬ P b ofs) →
  unchanged_on P m m' := sorry'

theorem store_init_data_list_unchanged {P : block → ℕ → Prop} {b il m p m'} :
  store_init_data_list ge m b p il = some m' →
  (∀ ofs, p ≤ ofs → ¬ P b ofs) →
  unchanged_on P m m' := sorry'

/- Properties related to [load_bytes] -/

def readbytes_as_zero (m : mem) (b : block) (ofs len : ℕ) : Prop :=
  ∀ p n,
  ofs ≤ p → p + n ≤ ofs + len →
  load_bytes m b p n = some (list.repeat (Byte 0) n)

lemma store_zeros_load_bytes {m b p n m'} :
  store_zeros m b p n = some m' →
  readbytes_as_zero m' b p n := sorry'

def bytes_of_init_data (i : init_data) : list memval :=
  match i with
| (init_data.int8 n) := inj_bytes (encode_int 1 (unsigned n))
| (init_data.int16 n) := inj_bytes (encode_int 2 (unsigned n))
| (init_data.int32 n) := inj_bytes (encode_int 4 (unsigned n))
| (init_data.int64 n) := inj_bytes (encode_int 8 (unsigned n))
| (init_data.float32 n) := inj_bytes (encode_int 4 (unsigned (float32.to_bits n)))
| (init_data.float64 n) := inj_bytes (encode_int 8 (unsigned (float.to_bits n)))
| (init_data.space n) := list.repeat (Byte 0) n
| (init_data.addrof id ofs) :=
      match find_symbol ge id with
      | some b := inj_value (if archi.ptr64 then Q64 else Q32) (Vptr b ofs)
      | none   := list.repeat Undef (if archi.ptr64 then 8 else 4)
      end
  end

theorem init_data_size_addrof {id ofs} :
  (init_data.addrof id ofs).size = (Mptr).size := sorry'

lemma store_init_data_load_bytes {m b p i m'} :
  store_init_data ge m b p i = some m' →
  readbytes_as_zero m b p i.size →
  load_bytes m' b p i.size = some (bytes_of_init_data ge i) := sorry'

def bytes_of_init_data_list (il : list init_data) : list memval :=
il >>= bytes_of_init_data ge

lemma store_init_data_list_load_bytes {b il m p m'} :
  store_init_data_list ge m b p il = some m' →
  readbytes_as_zero m b p (init_data.list_size il) →
  load_bytes m' b p (init_data.list_size il) =
    some (bytes_of_init_data_list ge il) := sorry'

/- Properties related to [load] -/

def chunk_zero_val : memory_chunk → val
| Mint8unsigned  := Vint 0
| Mint8signed    := Vint 0
| Mint16unsigned := Vint 0
| Mint16signed   := Vint 0
| Mint32         := Vint 0
| Mint64         := Vlong 0
| Mfloat32       := Vsingle 0
| Mfloat64       := Vfloat 0
| Many32         := Vundef
| Many64         := Vundef

def read_as_zero (m : mem) (b : block) (ofs len : ℕ) : Prop :=
∀ (chunk : memory_chunk) p,
  ofs ≤ p → p + chunk.size ≤ ofs + len →
  chunk.align ∣ p →
  load chunk m b p =
  some (chunk_zero_val chunk)

theorem read_as_zero_unchanged {P : block → ℕ → Prop} {m b ofs len m'} :
  read_as_zero m b ofs len →
  unchanged_on P m m' →
  (∀ i, ofs ≤ i → i < ofs + len → P b i) →
  read_as_zero m' b ofs len := sorry'

lemma store_zeros_read_as_zero {m b p n m'} :
  store_zeros m b p n = some m' →
  read_as_zero m' b p n := sorry'

def load_store_init_data (m : mem) (b : block) : ℕ → list init_data → Prop
| p [] := true
| p (init_data.int8 n :: il') :=
  load Mint8unsigned m b p = some (Vint (zero_ext 8 n))
  ∧ load_store_init_data (p + 1) il'
| p (init_data.int16 n :: il') :=
  load Mint16unsigned m b p = some (Vint (zero_ext 16 n))
  ∧ load_store_init_data (p + 2) il'
| p (init_data.int32 n :: il') :=
  load Mint32 m b p = some (Vint n)
  ∧ load_store_init_data (p + 4) il'
| p (init_data.int64 n :: il') :=
  load Mint64 m b p = some (Vlong n)
  ∧ load_store_init_data (p + 8) il'
| p (init_data.float32 n :: il') :=
  load Mfloat32 m b p = some (Vsingle n)
  ∧ load_store_init_data (p + 4) il'
| p (init_data.float64 n :: il') :=
  load Mfloat64 m b p = some (Vfloat n)
  ∧ load_store_init_data (p + 8) il'
| p (init_data.addrof symb ofs :: il') :=
  (∃ b', find_symbol ge symb = some b' ∧ load Mptr m b p = some (Vptr b' ofs))
  ∧ load_store_init_data (p + (Mptr).size) il'
| p (init_data.space n :: il') :=
  read_as_zero m b p n
  ∧ load_store_init_data (p + n) il'

lemma store_init_data_list_charact {b il m p m'} :
  store_init_data_list ge m b p il = some m' →
  read_as_zero m b p (init_data.list_size il) →
  load_store_init_data ge m' b p il := sorry'

theorem alloc_global_unchanged {P : block → ℕ → Prop} {m id g m'} :
  alloc_global ge m (id, g) = some m' →
  unchanged_on P m m' := sorry'

theorem alloc_globals_unchanged {P : block → ℕ → Prop} {gl m m'} :
  alloc_globals ge m gl = some m' →
  unchanged_on P m m' := sorry'

theorem load_store_init_data_invariant {m m' b} :
  (∀ chunk ofs, load chunk m' b ofs = load chunk m b ofs) →
  ∀ il p,
  load_store_init_data ge m b p il → load_store_init_data ge m' b p il := sorry'

def globdef_initialized (m : mem) (b : block) : globdef F V → Prop
| (Gfun f) :=
         perm m b 0 Cur Nonempty
      ∧ (∀ ofs k p, perm m b ofs k p → ofs = 0 ∧ p = Nonempty)
| (Gvar v) :=
         range_perm m b 0 (init_data.list_size v.init) Cur (perm_globvar v)
      ∧ (∀ ofs k p, perm m b ofs k p →
            ofs < init_data.list_size v.init ∧ perm_order (perm_globvar v) p)
      ∧ (¬ v.volatile → load_store_init_data ge m b 0 v.init)
      ∧ (¬ v.volatile → load_bytes m b 0 (init_data.list_size v.init) =
                        some (bytes_of_init_data_list ge v.init))

def globals_initialized (g : genv F V) (m : mem) :=
∀ b gd, find_def g b = some gd → globdef_initialized ge m b gd

lemma alloc_global_initialized {g : genv F V} {m : mem} {id gd m'} :
  g.next = m.nextblock →
  alloc_global ge m (id, gd) = some m' →
  globals_initialized ge g m →
     globals_initialized ge (add_global g (id, gd)) m'
  ∧ (add_global g (id, gd)).next = m'.nextblock := sorry'

lemma alloc_globals_initialized {gl} {g : genv F V} {m m'} :
  alloc_globals g m gl = some m' →
  g.next = m.nextblock →
  globals_initialized ge g m →
  globals_initialized ge (add_globals g gl) m' := sorry'

end init_mem

def init_mem (p : program F V) :=
alloc_globals (globalenv p) ∅ p.defs

lemma init_mem_genv_next {p : program F V} {m} :
  init_mem p = some m →
  (globalenv p).next = m.nextblock := sorry'

theorem find_symbol_not_fresh {p : program F V} {id b m} :
  init_mem p = some m →
  find_symbol (globalenv p) id = some b → valid_block m b := sorry'

theorem find_def_not_fresh {p : program F V} {b g m} :
  init_mem p = some m →
  find_def (globalenv p) b = some g → valid_block m b := sorry'

theorem find_funct_ptr_not_fresh {p : program F V} {b f m} :
  init_mem p = some m →
  find_funct_ptr (globalenv p) b = some f → valid_block m b := sorry'

theorem find_var_info_not_fresh {p : program F V} {b gv m} :
  init_mem p = some m →
  find_var_info (globalenv p) b = some gv → valid_block m b := sorry'

lemma init_mem_characterization_gen {p : program F V} {m} :
  init_mem p = some m →
  globals_initialized (globalenv p) (globalenv p) m := sorry'

theorem init_mem_characterization {p : program F V} {b gv m} :
  find_var_info (globalenv p) b = some gv →
  init_mem p = some m →
  range_perm m b 0 (init_data.list_size gv.init) Cur (perm_globvar gv)
  ∧ (∀ ofs k p, perm m b ofs k p →
        ofs < init_data.list_size gv.init ∧ perm_order (perm_globvar gv) p)
  ∧ (¬ gv.volatile →
      load_store_init_data (globalenv p) m b 0 gv.init)
  ∧ (¬ gv.volatile →
      load_bytes m b 0 (init_data.list_size gv.init) =
      some (bytes_of_init_data_list (globalenv p) gv.init)) := sorry'

theorem init_mem_characterization_2 {p : program F V} {b fd m} :
  find_funct_ptr (globalenv p) b = some fd →
  init_mem p = some m →
  perm m b 0 Cur Nonempty
  ∧ (∀ ofs k p, perm m b ofs k p → ofs = 0 ∧ p = Nonempty) := sorry'

/- ** Compatibility with memory injections -/

section init_mem_inj

variable {ge : genv F V}
variable {thr : block}
variable (symb_inject : ∀ id b, find_symbol ge id = some b → b < thr)
include symb_inject

lemma store_zeros_neutral {m b p n m'} :
  inject_neutral thr m →
  b < thr →
  store_zeros m b p n = some m' →
  inject_neutral thr m' := sorry'

lemma store_init_data_neutral {m b p id m'} :
  inject_neutral thr m →
  b < thr →
  store_init_data ge m b p id = some m' →
  inject_neutral thr m' := sorry'

lemma store_init_data_list_neutral {b idl m p m'} :
  inject_neutral thr m →
  b < thr →
  store_init_data_list ge m b p idl = some m' →
  inject_neutral thr m' := sorry'

lemma alloc_global_neutral {idg m m'} :
  alloc_global ge m idg = some m' →
  inject_neutral thr m →
  m.nextblock < thr →
  inject_neutral thr m' := sorry'

theorem advance_next_le : ∀ gl x, x ≤ @advance_next F V gl x := sorry'

lemma alloc_globals_neutral {gl m m'} :
  alloc_globals ge m gl = some m' →
  inject_neutral thr m →
  m'.nextblock ≤ thr →
  inject_neutral thr m' := sorry'

end init_mem_inj

theorem initmem_inject {p : program F V} {m} :
  init_mem p = some m →
  inject (flat_inj m.nextblock) m m := sorry'

/- ** Sufficient and necessary conditions for the initial memory to exist. -/

/- Alignment properties -/

section init_mem_inversion

variable (ge : genv F V)

lemma store_init_data_aligned {m b p i m'} :
  store_init_data ge m b p i = some m' →
  i.align ∣ p := sorry'

lemma store_init_data_list_aligned {b il m p m'} :
  store_init_data_list ge m b p il = some m' →
  init_data.list_aligned p il := sorry'

lemma store_init_data_list_free_idents {b i o il m p m'} :
  store_init_data_list ge m b p il = some m' →
  init_data.addrof i o ∈ il →
  ∃ b', find_symbol ge i = some b' := sorry'

end init_mem_inversion

theorem init_mem_inversion {p : program F V} {m id v} :
  init_mem p = some m →
  (id, Gvar v) ∈ p.defs →
  init_data.list_aligned 0 v.init
  ∧ ∀ i o, init_data.addrof i o ∈ v.init →
    ∃ b, find_symbol (globalenv p) i = some b := sorry'

section init_mem_exists

variable (ge : genv F V)

lemma store_zeros_exists {m b p n} :
  range_perm m b p (p + n) Cur Writable →
  ∃ m', store_zeros m b p n = some m' := sorry'

lemma store_init_data_exists {m b p} {i : init_data} :
  range_perm m b p (p + i.size) Cur Writable →
  i.align ∣ p →
  (∀ id ofs, i = init_data.addrof id ofs → ∃ b, find_symbol ge id = some b) →
  ∃ m', store_init_data ge m b p i = some m' := sorry'

lemma store_init_data_list_exists {b il m p} :
  range_perm m b p (p + init_data.list_size il) Cur Writable →
  init_data.list_aligned p il →
  (∀ id ofs, init_data.addrof id ofs ∈ il → ∃ b, find_symbol ge id = some b) →
  ∃ m', store_init_data_list ge m b p il = some m' := sorry'

def alloc_global_exists_ty : globdef F V → Prop
| (Gfun f) := true
| (Gvar v) := init_data.list_aligned 0 v.init
     ∧ ∀ i o, init_data.addrof i o ∈ v.init → ∃ b, find_symbol ge i = some b

lemma alloc_global_exists {m id g} :
  alloc_global_exists_ty ge g →
  ∃ m', alloc_global ge m (id, g) = some m' := sorry'

end init_mem_exists

theorem init_mem_exists {p : program F V} :
  (∀ id v, (id, Gvar v) ∈ p.defs →
        init_data.list_aligned 0 v.init
     ∧ ∀ i o, init_data.addrof i o ∈ v.init →
        ∃ b, find_symbol (globalenv p) i = some b) →
  ∃ m, init_mem p = some m := sorry' 

end

/- * Commutation with program transformations -/

section match_genvs

parameters {A B V W : Type} (R : globdef A V → globdef B W → Prop)

structure match_genvs (ge1 : genv A V) (ge2 : genv B W) : Prop :=
(next : ge2.next = ge1.next)
(symb : ∀ id, PTree.get id ge2.symb = PTree.get id ge1.symb)
(defs : ∀ b, option.rel R (PTree.get b ge1.defs) (PTree.get b ge2.defs))

lemma add_global_match {ge1 ge2 id g1 g2} :
  match_genvs ge1 ge2 →
  R g1 g2 →
  match_genvs (ge1.add_global (id, g1)) (ge2.add_global (id, g2)) := sorry'

lemma add_globals_match {gl1 gl2} :
  list.forall2 (λ ⟨id1, g1⟩ ⟨id2, g2⟩, id1 = id2 ∧ R g1 g2 :
    (ident × globdef A V) → (ident × globdef B W) → Prop) gl1 gl2 →
  ∀ {ge1 ge2}, match_genvs ge1 ge2 →
  match_genvs (ge1.add_globals gl1) (ge2.add_globals gl2) := sorry'

end match_genvs

section match_programs

parameters {C F1 V1 F2 V2 : Type} [linker C] [linker F1] [linker V1]
parameter {match_fundef : C → F1 → F2 → Prop}
parameter {match_varinfo : V1 → V2 → Prop}
parameter {ctx : C}
parameter {p : program F1 V1}
parameter {tp : program F2 V2}
parameter (progmatch : match_program_gen match_fundef match_varinfo ctx p tp)

lemma globalenvs_match : match_genvs (match_globdef match_fundef match_varinfo ctx)
  (globalenv p) (globalenv tp) := sorry'

theorem find_def_match_2 {b} : option.rel (match_globdef match_fundef match_varinfo ctx)
  (find_def (globalenv p) b) (find_def (globalenv tp) b) := sorry'

theorem find_funct_ptr_match {b f} : find_funct_ptr (globalenv p) b = some f →
  ∃ cunit tf, find_funct_ptr (globalenv tp) b = some tf ∧ match_fundef cunit f tf ∧
    linkorder cunit ctx := sorry'

theorem find_funct_match {v f} : find_funct (globalenv p) v = some f →
  ∃ cunit tf, find_funct (globalenv tp) v = some tf ∧ match_fundef cunit f tf ∧
    linkorder cunit ctx := sorry'

theorem find_var_info_match {b v} : find_var_info (globalenv p) b = some v →
  ∃ tv, find_var_info (globalenv tp) b = some tv ∧ match_globvar match_varinfo v tv := sorry'

theorem find_symbol_match {s : ident} :
  find_symbol (globalenv tp) s = find_symbol (globalenv p) s := sorry'

theorem senv_match : senv.equiv (globalenv p) (globalenv tp) := sorry'

lemma store_init_data_list_match {idl m b ofs m'} :
  store_init_data_list (globalenv p) m b ofs idl = some m' →
  store_init_data_list (globalenv tp) m b ofs idl = some m' := sorry'

lemma alloc_globals_match {gl1 gl2} :
  list.forall2 (match_ident_globdef match_fundef match_varinfo ctx) gl1 gl2 →
  ∀ m m', alloc_globals (globalenv p) m gl1 = some m' →
  alloc_globals (globalenv tp) m gl2 = some m' := sorry'

theorem init_mem_match {m} : init_mem p = some m → init_mem tp = some m := sorry'

end match_programs

/- Special case for partial transformations that do not depend on the compilation unit -/

section transform_partial

parameters {A B V : Type} [linker A] [linker V]
parameters {transf : A → res B} {p : program A V} {tp : program B V}
parameter (progmatch : match_program (λ cu f tf, transf f = OK tf) eq p tp)

theorem find_funct_ptr_transf_partial {b f} : find_funct_ptr (globalenv p) b = some f →
  ∃ tf, find_funct_ptr (globalenv tp) b = some tf ∧ transf f = OK tf := sorry'

theorem find_funct_transf_partial {v f} : find_funct (globalenv p) v = some f →
  ∃ tf, find_funct (globalenv tp) v = some tf ∧ transf f = OK tf := sorry'

theorem find_symbol_transf_partial {s : ident} :
  find_symbol (globalenv tp) s = find_symbol (globalenv p) s := sorry'

theorem senv_transf_partial : senv.equiv (globalenv p) (globalenv tp) := sorry'

theorem init_mem_transf_partial {m} : init_mem p = some m → init_mem tp = some m := sorry'

end transform_partial

/- Special case for total transformations that do not depend on the compilation unit -/

section transform_total

parameters {A B V : Type} [linker A] [linker V]
parameters {transf : A → B} {p : program A V} {tp : program B V}
parameter (progmatch : match_program (λ cu f tf, tf = transf f) eq p tp)

theorem find_funct_ptr_transf {b f} :
  find_funct_ptr (globalenv p) b = some f →
  find_funct_ptr (globalenv tp) b = some (transf f) := sorry'

theorem find_funct_transf {v f} :
  find_funct (globalenv p) v = some f →
  find_funct (globalenv tp) v = some (transf f) := sorry'

theorem find_symbol_transf {s : ident} :
  find_symbol (globalenv tp) s = find_symbol (globalenv p) s := sorry'

theorem senv_transf : senv.equiv (globalenv p) (globalenv tp) := sorry'

theorem init_mem_transf {m} : init_mem p = some m → init_mem tp = some m := sorry'

end transform_total

end genv

end globalenvs