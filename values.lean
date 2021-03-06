
/- This module defines the type of values that is used in the dynamic
  semantics of all our intermediate languages. -/

import .lib .integers .floats .ast

namespace values
open integers word floats ast ast.typ ast.memory_chunk

def block : Type := pos_num
instance eq_block : decidable_eq block := by tactic.mk_dec_eq_instance
instance coe_block : has_coe block ℕ := ⟨λp, num.pos p⟩
instance dlo_block : decidable_linear_order block := pos_num.decidable_linear_order
instance block_one : has_one block := ⟨(1 : pos_num)⟩

/- A value is either:
- a machine integer;
- a floating-point number;
- a pointer: a pair of a memory address and an integer offset with respect
  to this address;
- the [Vundef] value denoting an arbitrary bit pattern, such as the
  value of an uninitialized variable.
-/

inductive val : Type
| Vundef  : val
| Vint    : int32 → val
| Vlong   : int64 → val
| Vfloat  : float → val
| Vsingle : float32 → val
| Vptr    : block → ptrofs → val
export val
instance coe_int32_val : has_coe int32 val := ⟨Vint⟩
instance coe_int64_val : has_coe int64 val := ⟨Vlong⟩
instance coe_Int32_val : has_coe (@word W32) val := ⟨Vint⟩
instance coe_Int64_val : has_coe (@word W64) val := ⟨Vlong⟩
instance coe_float_val : has_coe float val := ⟨Vfloat⟩
instance coe_single_val : has_coe float32 val := ⟨Vsingle⟩
instance inhabited_val : inhabited val := ⟨Vundef⟩

def Vzero  : val := Vint 0
def Vone   : val := Vint 1
def Vmone  : val := Vint (-1)
instance val_zero : has_zero val := ⟨Vzero⟩
instance val_one : has_one val := ⟨Vone⟩

def Vtrue  : val := 1
def Vfalse : val := 0

def Vnullptr := if archi.ptr64 then Vlong 0 else Vint 0

def Vptrofs (n : ptrofs) : val :=
if archi.ptr64 then ptrofs.to_int64 n else ptrofs.to_int n

/- * Operations over values -/

/- The module [val] defines a number of arithmetic and logical operations
  over type [val].  Most of these operations are straightforward extensions
  of the corresponding integer or floating-point operations. -/

namespace val

instance val_eq : decidable_eq val := by tactic.mk_dec_eq_instance

def has_type : val → typ → Prop
| Vundef      _       := true
| (Vint _)    Tint    := true
| (Vlong _)   Tlong   := true
| (Vfloat _)  Tfloat  := true
| (Vsingle _) Tsingle := true
| (Vptr _ _)  Tint    := ¬ archi.ptr64
| (Vptr _ _)  Tlong   := archi.ptr64
| (Vint _)    Tany32  := true
| (Vsingle _) Tany32  := true
| (Vptr _ _)  Tany32  := ¬ archi.ptr64
| _           Tany64  := true
| _           _       := false

def has_type_list : list val → list typ → Prop
| []         []         := true
| (v1 :: vs) (t1 :: ts) := has_type v1 t1 ∧ has_type_list vs ts
| _          _          := false

def has_opttype (v : val) : option typ → Prop
| none     := v = Vundef
| (some t) := has_type v t

lemma Vptr_has_type (b ofs) : has_type (Vptr b ofs) Tptr :=
begin
  delta Tptr,
  ginduction archi.ptr64 with h,
  { intro h2, note := h.symm.trans h2, contradiction },
  { exact h }
end

lemma Vnullptr_has_type : has_type Vnullptr Tptr :=
by delta Tptr Vnullptr; cases archi.ptr64; trivial

lemma has_subtype (ty1 ty2 v) : subtype ty1 ty2 → has_type v ty1 → has_type v ty2 := sorry'

lemma has_subtype_list (tyl1 tyl2 vl) :
  subtype_list tyl1 tyl2 → has_type_list vl tyl1 → has_type_list vl tyl2 := sorry'

/- Truth values.  Non-zero integers are treated as [True].
  The integer 0 (also used to represent the null pointer) is [False].
  Other values are neither true nor false. -/

def to_bool : val → option bool
| (Vint n) := some (n ≠ 0)
| _ := none

/- Arithmetic operations -/

protected def neg : val → val
| (Vint n) := word.neg n
| _        := Vundef
instance : has_neg val := ⟨val.neg⟩

def negf : val → val
| (Vfloat f) := float.neg f
| _          := Vundef

def absf : val → val
| (Vfloat f) := float.abs f
| _          := Vundef

def negfs : val → val
| (Vsingle f) := float32.neg f
| _           := Vundef

def absfs : val → val
| (Vsingle f) := float32.abs f
| _           := Vundef

def make_total (ov : option val) : val :=
ov.get_or_else Vundef

def int_of_float : val → option val
| (Vfloat f) := Vint <$> float.to_int f
| _          := none

def intu_of_float : val → option val
| (Vfloat f) := Vint <$> float.to_intu f
| _          := none

def float_of_int : val → option val
| (Vint n) := float.of_int n
| _        := none

def float_of_intu : val → option val
| (Vint n) := float.of_intu n
| _        := none

def int_of_single : val → option val
| (Vsingle f) := Vint <$> float32.to_int f
| _           := none

def intu_of_single : val → option val
| (Vsingle f) := Vint <$> float32.to_intu f
| _           := none

def single_of_int : val → option val
| (Vint n) := float32.of_int n
| _        := none

def single_of_intu : val → option val
| (Vint n) := float32.of_intu n
| _        := none

def negint : val → val
| (Vint n) := word.neg n
| _        := Vundef

def notint : val → val
| (Vint n) := word.not n
| _        := Vundef

def of_bool (b : bool) : val := if b then Vtrue else Vfalse
instance : has_coe bool val := ⟨of_bool⟩

def boolval : val → val
| (Vint n)     := of_bool (n ≠ 0)
| (Vptr b ofs) := Vtrue
| _            := Vundef

def notbool : val → val
| (Vint n)     := of_bool (n = 0)
| (Vptr b ofs) := Vfalse
| _            := Vundef

def zero_ext (nbits : ℕ) : val → val
| (Vint n) := word.zero_ext nbits n
| _        := Vundef

def sign_ext (nbits : ℕ+) : val → val
| (Vint n) := word.sign_ext nbits n
| _        := Vundef

def single_of_float : val → val
| (Vfloat f) := float.to_single f
| _          := Vundef

def float_of_single : val → val
| (Vsingle f) := float.of_single f
| _           := Vundef

protected def add : val → val → val
| (Vint m)       (Vint n)       := Vint $ m + n
| (Vptr b1 ofs1) (Vint n)       := if archi.ptr64 then Vundef else Vptr b1 (ofs1 + ptrofs.of_int n)
| (Vint m)       (Vptr b2 ofs2) := if archi.ptr64 then Vundef else Vptr b2 (ofs2 + ptrofs.of_int m)
| _              _              := Vundef
instance : has_add val := ⟨val.add⟩

protected def sub : val → val → val
| (Vint m)       (Vint n)       := Vint $ m - n
| (Vptr b1 ofs1) (Vint n)       := if archi.ptr64 then Vundef else Vptr b1 (ofs1 - ptrofs.of_int n)
| (Vptr b1 ofs1) (Vptr b2 ofs2) := if archi.ptr64 ∨ b1 ≠ b2 then Vundef else ptrofs.to_int (ofs1 - ofs2)
| _              _              := Vundef
instance : has_sub val := ⟨val.sub⟩

protected def mul : val → val → val
| (Vint m) (Vint n) := Vint (m * n)
| _        _        := Vundef
instance : has_mul val := ⟨val.mul⟩

def mulhs : val → val → val
| (Vint m) (Vint n) := word.mulhs m n
| _        _        := Vundef

def mulhu : val → val → val
| (Vint m) (Vint n) := word.mulhu m n
| _        _        := Vundef

def divs : val → val → option val
| (Vint m) (Vint n) := if n = 0 ∨ m = repr (word.min_signed W32) ∧ n = -1
                       then none else some (m / n : word _)
| _        _        := none

def mods : val → val → option val
| (Vint m) (Vint n) := if n = 0 ∨ m = repr (@min_signed W32) ∧ n = -1
                       then none else some (m % n : word _)
| _        _        := none

def divu : val → val → option val
| (Vint m) (Vint n) := if n = 0 then none else word.divu m n
| _        _        := none

def modu : val → val → option val
| (Vint m) (Vint n) := if n = 0 then none else word.modu m n
| _        _        := none

def add_carry : val → val → val → val
| (Vint m) (Vint n) (Vint c) := word.add_carry m n c
| _        _        _        := Vundef

def sub_overflow : val → val → val
| (Vint m) (Vint n) := word.sub_overflow m n 0
| _        _        := Vundef

def negative : val → val
| (Vint n) := word.negative n
| _        := Vundef

protected def and : val → val → val
| (Vint m) (Vint n) := word.and m n
| _        _        := Vundef

protected def or : val → val → val
| (Vint m) (Vint n) := word.or m n
| _        _        := Vundef

protected def xor : val → val → val
| (Vint m) (Vint n) := word.xor m n
| _        _        := Vundef

def shl : val → val → val
| (Vint m) (Vint n) := if word.ltu n iwordsize
                       then word.shl m n else Vundef
| _        _        := Vundef

def shr : val → val → val
| (Vint m) (Vint n) := if word.ltu n iwordsize
                       then word.shr m n else Vundef
| _        _        := Vundef

def shr_carry : val → val → val
| (Vint m) (Vint n) := if word.ltu n iwordsize
                       then word.shr_carry m n else Vundef
| _        _        := Vundef

def shrx : val → val → option val
| (Vint m) (Vint n) := if word.ltu n (repr 31)
                       then word.shrx m n else none
| _        _        := none

def shru : val → val → val
| (Vint m) (Vint n) := if word.ltu n iwordsize
                       then word.shru m n else Vundef
| _        _        := Vundef

def rol : val → val → val
| (Vint m) (Vint n) := word.rol m n
| _        _        := Vundef

def rolm : val → int32 → int32 → val
| (Vint n) amount mask := word.rolm n amount mask
| _        amount mask := Vundef

def ror : val → val → val
| (Vint m) (Vint n) := word.ror m n
| _        _        := Vundef

def addf : val → val → val
| (Vfloat x) (Vfloat y) := Vfloat $ x + y
| _          _          := Vundef

def subf : val → val → val
| (Vfloat x) (Vfloat y) := Vfloat $ x - y
| _          _          := Vundef

def mulf : val → val → val
| (Vfloat x) (Vfloat y) := Vfloat $ x * y
| _          _          := Vundef

def divf : val → val → val
| (Vfloat x) (Vfloat y) := Vfloat $ x / y
| _          _          := Vundef

def float_of_words : val → val → val
| (Vint m) (Vint n) := float.from_words m n
| _        _        := Vundef

def addfs : val → val → val
| (Vsingle x) (Vsingle y) := float32.add x y
| _           _           := Vundef

def subfs : val → val → val
| (Vsingle x) (Vsingle y) := float32.sub x y
| _           _           := Vundef

def mulfs : val → val → val
| (Vsingle x) (Vsingle y) := float32.mul x y
| _           _           := Vundef

def divfs : val → val → val
| (Vsingle x) (Vsingle y) := float32.div x y
| _           _           := Vundef

/- Operations on 64-bit integers -/

def long_of_words : val → val → val
| (Vint m) (Vint n) := int64.ofwords m n
| _        _        := Vundef

def loword : val → val
| (Vlong n) := int64.loword n
| _         := Vundef

def hiword : val → val
| (Vlong n)  := int64.hiword n
| _ := Vundef

def negl : val → val
| (Vlong n) := Vlong $ -n
| _         := Vundef

def notl : val → val
| (Vlong n) := word.not n
| _ := Vundef

def long_of_int : val → val
| (Vint n) := Vlong $ scoe n
| _        := Vundef

def long_of_intu : val → val
| (Vint n) := Vlong $ ucoe n
| _        := Vundef

def long_of_float : val → option val
| (Vfloat f) := Vlong <$> float.to_long f
| _          := none

def longu_of_float : val → option val
| (Vfloat f) := Vlong <$> float.to_longu f
| _          := none

def long_of_single : val → option val
| (Vsingle f) := Vlong <$> float32.to_long f
| _           := none

def longu_of_single : val → option val
| (Vsingle f) := Vlong <$> float32.to_longu f
| _           := none

def float_of_long : val → option val
| (Vlong n) := float.of_long n
| _         := none

def float_of_longu : val → option val
| (Vlong n) := float.of_longu n
| _         := none

def single_of_long : val → option val
| (Vlong n) := float32.of_long n
| _         := none

def single_of_longu : val → option val
| (Vlong n) := float32.of_longu n
| _         := none

def addl : val → val → val
| (Vlong n1)     (Vlong n2)     := Vlong (n1 + n2)
| (Vptr b1 ofs1) (Vlong n2)     := if archi.ptr64 then Vptr b1 (ofs1 + ptrofs.of_int64 n2) else Vundef
| (Vlong n1)     (Vptr b2 ofs2) := if archi.ptr64 then Vptr b2 (ofs2 + ptrofs.of_int64 n1) else Vundef
| _              _              := Vundef

def subl : val → val → val
| (Vlong n1)     (Vlong n2)     := Vlong (n1 - n2)
| (Vptr b1 ofs1) (Vlong n2)     := if archi.ptr64 then Vptr b1 (ofs1 - ptrofs.of_int64 n2) else Vundef
| (Vptr b1 ofs1) (Vptr b2 ofs2) := if archi.ptr64 ∨ b1 ≠ b2 then Vundef else ptrofs.to_int64 (ofs1 - ofs2)
| _              _              := Vundef

def mull : val → val → val
| (Vlong m) (Vlong n) := Vlong (m * n)
| _         _         := Vundef

def mull' : val → val → val
| (Vint m) (Vint n) := Vlong (ucoe m * ucoe n)
| _        _        := Vundef

def mullhs : val → val → val
| (Vlong m) (Vlong n) := word.mulhs m n
| _         _         := Vundef

def mullhu : val → val → val
| (Vlong m) (Vlong n) := word.mulhu m n
| _         _         := Vundef

def divls : val → val → option val
| (Vlong m) (Vlong n) := if n = 0 ∨ m = repr (min_signed 64) ∧ n = -1
                         then none else some (m / n : word _)
| _         _         := none

def modls : val → val → option val
| (Vlong m) (Vlong n) := if n = 0 ∨ m = repr (min_signed 64) ∧ n = -1
                         then none else some (m % n : word _)
| _         _         := none

def divlu : val → val → option val
| (Vlong m) (Vlong n) := if n = 0 then none else word.divu m n
| _         _         := none

def modlu : val → val → option val
| (Vlong m) (Vlong n) := if n = 0 then none else word.modu m n
| _         _         := none

def subl_overflow : val → val → val
| (Vlong m) (Vlong n) := Vint $ ucoe $ word.sub_overflow m n 0
| _         _         := Vundef

def negativel : val → val
| (Vlong n) := Vint $ ucoe $ word.negative n
| _         := Vundef

def andl : val → val → val
| (Vlong m) (Vlong n) := word.and m n
| _         _         := Vundef

def orl : val → val → val
| (Vlong m) (Vlong n) := word.or m n
| _         _         := Vundef

def xorl : val → val → val
| (Vlong m) (Vlong n) := word.xor m n
| _         _         := Vundef

def shll : val → val → val
| (Vlong m) (Vint n) := if word.ltu n 64 then word.shl m (ucoe n) else Vundef
| _         _        := Vundef

def shrl : val → val → val
| (Vlong m) (Vint n) := if word.ltu n 64 then word.shr m (ucoe n) else Vundef
| _         _        := Vundef

def shrlu : val → val → val
| (Vlong m) (Vint n) := if word.ltu n 64 then word.shru m (ucoe n) else Vundef
| _         _        := Vundef

def shrxl : val → val → option val
| (Vlong m) (Vint n) := if word.ltu n 63 then word.shrx m (ucoe n) else none
| _         _        := none

def roll : val → val → val
| (Vlong m) (Vint n) := word.rol m (ucoe n)
| _         _        := Vundef

def rorl : val → val → val
| (Vlong m) (Vint n) := word.ror m (ucoe n)
| _         _        := Vundef

def rolml : val → int64 → int64 → val
| (Vlong n) amount mask := word.rolm n amount mask
| _         amount mask := Vundef

/- Comparisons -/

section comparisons

parameter valid_ptr : block → ℕ → bool
def weak_valid_ptr (b : block) (ofs : ℕ) := valid_ptr b ofs || valid_ptr b (ofs - 1)

def cmp_bool (c : comparison) : val → val → option bool
| (Vint m) (Vint n) := cmp c m n
| _        _        := none

def cmp_different_blocks : comparison → option bool
| Ceq := some ff
| Cne := some tt
| _   := none

def cmpu_bool (c : comparison) : val → val → option bool
| (Vint m) (Vint n) := some $ cmpu c m n
| (Vint m) (Vptr b2 ofs2) :=
  if archi.ptr64 then none else
  if m = 0 ∧ weak_valid_ptr b2 (unsigned ofs2)
  then cmp_different_blocks c
  else none
| (Vptr b1 ofs1) (Vptr b2 ofs2) :=
  if archi.ptr64 then none else
  if b1 = b2 then
    if weak_valid_ptr b1 (unsigned ofs1) ∧ weak_valid_ptr b2 (unsigned ofs2)
    then cmpu c ofs1 ofs2
    else none
  else
    if valid_ptr b1 (unsigned ofs1) ∧ valid_ptr b2 (unsigned ofs2)
    then cmp_different_blocks c
    else none
| (Vptr b1 ofs1) (Vint n) :=
  if archi.ptr64 then none else
  if n = 0 ∧ weak_valid_ptr b1 (unsigned ofs1)
  then cmp_different_blocks c
  else none
| _ _ := none

def cmpf_bool (c : comparison) : val → val → option bool
| (Vfloat x) (Vfloat y) := float.cmp c x y
| _          _          := none

def cmpfs_bool (c : comparison) : val → val → option bool
| (Vsingle x) (Vsingle y) := float32.cmp c x y
| _           _           := none

def cmpl_bool (c : comparison) : val → val → option bool
| (Vlong m) (Vlong n) := cmp c m n
| _         _         := none

def cmplu_bool (c : comparison) : val → val → option bool
| (Vlong n1) (Vlong n2) := some $ cmpu c n1 n2
| (Vlong n1) (Vptr b2 ofs2) :=
  if archi.ptr64 ∧ n1 = 0 ∧ weak_valid_ptr b2 (unsigned ofs2)
  then cmp_different_blocks c
  else none
| (Vptr b1 ofs1) (Vptr b2 ofs2) :=
  if ¬ archi.ptr64 then none else
  if b1 = b2 then
    if weak_valid_ptr b1 (unsigned ofs1) && weak_valid_ptr b2 (unsigned ofs2)
    then some (cmpu c ofs1 ofs2)
    else none
  else
    if valid_ptr b1 (unsigned ofs1) && valid_ptr b2 (unsigned ofs2)
    then cmp_different_blocks c
    else none
| (Vptr b1 ofs1) (Vlong n2) :=
  if archi.ptr64 ∧ n2 = 0 ∧ weak_valid_ptr b1 (unsigned ofs1)
  then cmp_different_blocks c
  else none
| _ _ := none

def of_optbool : option bool → val
| (some tt) := Vtrue
| (some ff) := Vfalse
| none := Vundef

def cmp (c : comparison) (v1 v2 : val) : val :=
of_optbool $ cmp_bool c v1 v2

def cmpu (c : comparison) (v1 v2 : val) : val :=
of_optbool $ cmpu_bool c v1 v2

def cmpf (c : comparison) (v1 v2 : val) : val :=
of_optbool $ cmpf_bool c v1 v2

def cmpfs (c : comparison) (v1 v2 : val) : val :=
of_optbool $ cmpfs_bool c v1 v2

def cmpl (c : comparison) (v1 v2 : val) : option val :=
of_bool <$> cmpl_bool c v1 v2

def cmplu (c : comparison) (v1 v2 : val) : option val :=
of_bool <$> cmplu_bool c v1 v2

def maskzero_bool : val → int32 → option bool
| (Vint n) mask := some $ word.and n mask = 0
| _        mask := none

end comparisons

/- Add the given offset to the given pointer. -/

def offset_ptr : val → ptrofs → val
| (Vptr b ofs) delta := Vptr b (ofs + delta)
| _            delta := Vundef

/- [load_result] reflects the effect of storing a value with a given
  memory chunk, then reading it back with the same chunk.  Depending
  on the chunk and the type of the value, some normalization occurs.
  For instance, consider storing the integer value [0xFFF] on 1 byte
  at a given address, and reading it back.  If it is read back with
  chunk [Mint8unsigned], zero-extension must be performed, resulting
  in [0xFF].  If it is read back as a [Mint8signed], sign-extension is
  performed and [0xFFFFFFFF] is returned. -/

def load_result : memory_chunk → val → val
| Mint8signed    (Vint n)     := word.sign_ext W8 n
| Mint8unsigned  (Vint n)     := word.zero_ext 8 n
| Mint16signed   (Vint n)     := word.sign_ext W16 n
| Mint16unsigned (Vint n)     := word.zero_ext 16 n
| Mint32         (Vint n)     := Vint n
| Mint32         (Vptr b ofs) := if archi.ptr64 then Vundef else Vptr b ofs
| Mint64         (Vlong n)    := Vlong n
| Mint64         (Vptr b ofs) := if archi.ptr64 then Vptr b ofs else Vundef
| Mfloat32       (Vsingle f)  := Vsingle f
| Mfloat64       (Vfloat f)   := Vfloat f
| Many32         (Vint n)     := Vint n
| Many32         (Vsingle f)  := Vsingle f
| Many32         (Vptr b ofs) := if archi.ptr64 then Vundef else Vptr b ofs
| Many64         v            := v
| _              _            := Vundef

lemma load_result_type (chunk v) : has_type (load_result chunk v) chunk.type := sorry'

lemma load_result_same {v ty} : has_type v ty → load_result (chunk_of_type ty) v = v := sorry'

/- Theorems on arithmetic operations. -/

theorem cast8unsigned_and (x) : zero_ext 8 x = val.and x (0xFF : int32) := sorry'

theorem cast16unsigned_and (x) : zero_ext 16 x = val.and x (0xFFFF : int32) := sorry'

theorem to_bool_of_bool (b1 b2) : (of_bool b1).to_bool = some b2 → b1 = b2 := sorry'

theorem to_bool_of_optbool (ob) : (of_optbool ob).to_bool = ob := sorry'

theorem notbool_negb_1 (b) : of_bool (bnot b) = notbool (of_bool b) := sorry'

theorem notbool_negb_2 (b) : of_bool b = notbool (of_bool (bnot b)) := sorry'

theorem notbool_negb_3 (ob) : of_optbool (bnot <$> ob) = notbool (of_optbool ob) := sorry'

set_option type_context.unfold_lemmas true
theorem notbool_idem2 (b) : notbool (notbool (of_bool b)) = of_bool b :=
by cases b; refl

theorem notbool_idem3 (x) : notbool (notbool (notbool x)) = notbool x := sorry'

theorem notbool_idem4 (ob) : notbool (notbool (of_optbool ob)) = of_optbool ob := sorry'

theorem add_comm (x y : val) : x + y = y + x := sorry'

theorem add_assoc (x y z : val) : (x + y) + z = x + (y + z) := sorry'

theorem neg_zero : (-0 : val) = 0 := sorry'

theorem neg_add (x y : val) : -(x + y) = -x + -y := sorry'

theorem zero_sub (x : val) : 0 - x = -x := sorry'

theorem sub_eq_add_neg (x y) : x - Vint y = x + Vint (-y) := sorry'

theorem sub_neg_eq_add (x y) : x - Vint (-y) = x + Vint y := sorry'

theorem sub_add_eq_add_sub (v1 v2 i) : v1 + Vint i - v2 = v1 - v2 + Vint i := sorry' 

theorem sub_add_eq_sub_add_neg (v1 v2 i) : v1 - (v2 + Vint i) = v1 - v2 + Vint (-i) := sorry'

theorem mul_comm (x y : val) : x * y = y * x := sorry'

theorem mul_assoc (x y z : val) : (x * y) * z = x * (y * z) := sorry'

theorem right_distrib (x y z : val) : (x + y) * z = x * z + y * z := sorry'

theorem left_distrib (x y z : val) : x * (y + z) = x * y + x * z := sorry'

theorem mul_pow2 (x n logn) : is_power2 n = some logn →
  x * Vint n = shl x (Vint logn) := sorry'

theorem mods_divs (x y z) : mods x y = some z → ∃ v, divs x y = some v ∧ z = x - v * y := sorry'

theorem modu_divu (x y z) : modu x y = some z → ∃ v, divu x y = some v ∧ z = x - v * y := sorry'

theorem divs_pow2 (x n logn y) : is_power2 n = some logn → word.ltu logn 31 →
  divs x (Vint n) = some y → shrx x (Vint logn) = some y := sorry'

theorem divu_pow2 (x n logn y) : is_power2 n = some logn →
  divu x (Vint n) = some y → shru x (Vint logn) = y := sorry'

theorem modu_pow2 (x n logn y) : is_power2 n = some logn →
  modu x (Vint n) = some y → val.and x (Vint (n - 1)) = y := sorry'

theorem and_comm (x y) : val.and x y = val.and y x := sorry'

theorem and_assoc (x y z) : val.and (val.and x y) z = val.and x (val.and y z) := sorry'

theorem or_comm (x y) : val.or x y = val.or y x := sorry'

theorem or_assoc (x y z) : val.or (val.or x y) z = val.or x (val.or y z) := sorry'

theorem xor_commut (x y) : val.xor x y = val.xor y x := sorry'

theorem xor_assoc (x y z) : val.xor (val.xor x y) z = val.xor x (val.xor y z) := sorry'

theorem not_xor (x) : notint x = val.xor x (Vint (-1)) := sorry'

theorem shl_rolm (x n) : word.ltu n 32 → shl x (Vint n) = rolm x n (word.shl (-1) n) := sorry'

theorem shru_rolm (x n) : word.ltu n 32 →
  shru x (Vint n) = rolm x (32 - n) (word.shru (-1) n) := sorry'

theorem shrx_carry (x y z) : shrx x y = some z →
  shr x y + shr_carry x y = z := sorry'

theorem shrx_shr (x y z) : shrx x y = some z →
  ∃ p, ∃ q, x = Vint p ∧ y = Vint q ∧
    z = shr (if p < 0 then x + Vint (word.shl 1 q - 1) else x) (Vint q) := sorry'

theorem shrx_shr_2 (n x z) : shrx x (Vint n) = some z →
  z = if n = 0 then x else shr (x + shru (shr x 31) (Vint (32 - n))) (Vint n) := sorry'

theorem or_rolm (x n m1 m2) : val.or (rolm x n m1) (rolm x n m2) = rolm x n (word.or m1 m2) := sorry'

theorem rolm_rolm (x n1 m1 n2 m2) : rolm (rolm x n1 m1) n2 m2 =
  rolm x (word.modu (n1 + n2) 32) (word.and (word.rol m1 n2) m2) := sorry'

theorem rolm_zero (x m) : rolm x 0 m = val.and x (Vint m) := sorry'

theorem addl_comm (x y) : addl x y = addl y x := sorry'

theorem addl_assoc (x y z) : addl (addl x y) z = addl x (addl y z) := sorry'

theorem negl_addl_distr (x y) : negl (addl x y) = addl (negl x) (negl y) := sorry'

theorem subl_addl_opp (x y) : subl x (Vlong y) = addl x (Vlong (-y)) := sorry'

theorem subl_opp_addl : ∀ x y, subl x (Vlong (-y)) = addl x (Vlong y) := sorry'

theorem subl_addl_l (v1 v2 i) : subl (addl v1 (Vlong i)) v2 = addl (subl v1 v2) (Vlong i) := sorry'

theorem subl_addl_r (v1 v2 i) : subl v1 (addl v2 (Vlong i)) = addl (subl v1 v2) (Vlong (-i)) := sorry'

theorem mull_comm (x y) : mull x y = mull y x := sorry'

theorem mull_assoc (x y z) : mull (mull x y) z = mull x (mull y z) := sorry'

theorem mull_addl_distr_l (x y z) : mull (addl x y) z = addl (mull x z) (mull y z) := sorry'

theorem mull_addl_distr_r (x y z) : mull x (addl y z) = addl (mull x y) (mull x z) := sorry'

theorem andl_comm (x y) : andl x y = andl y x := sorry'

theorem andl_assoc (x y z) : andl (andl x y) z = andl x (andl y z) := sorry'

theorem orl_comm (x y) : orl x y = orl y x := sorry'

theorem orl_assoc (x y z) : orl (orl x y) z = orl x (orl y z) := sorry'

theorem xorl_commut (x y) : xorl x y = xorl y x := sorry'

theorem xorl_assoc (x y z) : xorl (xorl x y) z = xorl x (xorl y z) := sorry'

theorem notl_xorl (x) : notl x = xorl x (Vlong (-1)) := sorry'

theorem divls_pow2 (x n logn y) : int64.is_power2 n = some logn → word.ltu logn 63 →
  divls x (Vlong n) = some y →
  shrxl x (Vint logn) = some y := sorry'

theorem divlu_pow2 (x n logn y) : int64.is_power2 n = some logn →
  divlu x (Vlong n) = some y →
  shrlu x (Vint logn) = y := sorry'

theorem modlu_pow2 (x n logn y) : int64.is_power2 n = some logn →
  modlu x (Vlong n) = some y →
  andl x (Vlong (n - 1)) = y := sorry'

theorem shrxl_shrl_2 (n x z) : shrxl x (Vint n) = some z →
  z = if n = 0 then x else
    shrl (addl x (shrlu (shrl x (Vint 63)) (Vint (64 - n)))) (Vint n) := sorry'

theorem negate_cmp_bool (c x y) : cmp_bool (negate_comparison c) x y = bnot <$> cmp_bool c x y := sorry'

theorem negate_cmpu_bool (valid_ptr c x y) :
  cmpu_bool valid_ptr (negate_comparison c) x y = bnot <$> cmpu_bool valid_ptr c x y := sorry'

theorem negate_cmpl_bool (c x y) : cmpl_bool (negate_comparison c) x y = bnot <$> cmpl_bool c x y := sorry'

theorem negate_cmplu_bool (valid_ptr c x y) :
  cmplu_bool valid_ptr (negate_comparison c) x y = bnot <$> cmplu_bool valid_ptr c x y := sorry'

lemma not_of_optbool (ob) : of_optbool (bnot <$> ob) = notbool (of_optbool ob) := sorry'

theorem negate_cmp (c x y) : cmp (negate_comparison c) x y = notbool (cmp c x y) := sorry'

theorem negate_cmpu (valid_ptr c x y) :
  cmpu valid_ptr (negate_comparison c) x y =
    notbool (cmpu valid_ptr c x y) := sorry'

theorem swap_cmp_bool (c x y) : cmp_bool (swap_comparison c) x y = cmp_bool c y x := sorry'

theorem swap_cmpu_bool (valid_ptr c x y) :
  cmpu_bool valid_ptr (swap_comparison c) x y = cmpu_bool valid_ptr c y x := sorry'

theorem swap_cmpl_bool (c x y) : cmpl_bool (swap_comparison c) x y = cmpl_bool c y x := sorry'

theorem swap_cmplu_bool (valid_ptr c x y) :
  cmplu_bool valid_ptr (swap_comparison c) x y = cmplu_bool valid_ptr c y x := sorry'

theorem negate_cmpf_eq (v1 v2) : notbool (cmpf Cne v1 v2) = cmpf Ceq v1 v2 := sorry'

theorem negate_cmpf_ne (v1 v2) : notbool (cmpf Ceq v1 v2) = cmpf Cne v1 v2 := sorry'

theorem cmpf_le (v1 v2) : cmpf Cle v1 v2 = val.or (cmpf Clt v1 v2) (cmpf Ceq v1 v2) := sorry'

theorem cmpf_ge (v1 v2) : cmpf Cge v1 v2 = val.or (cmpf Cgt v1 v2) (cmpf Ceq v1 v2) := sorry'

theorem cmp_ne_0_optbool (ob) : cmp Cne (of_optbool ob) 0 = of_optbool ob := sorry'

theorem cmp_eq_1_optbool (ob) : cmp Ceq (of_optbool ob) 1 = of_optbool ob := sorry'

theorem cmp_eq_0_optbool (ob) : cmp Ceq (of_optbool ob) 0 = of_optbool (bnot <$> ob) := sorry'

theorem cmp_ne_1_optbool (ob) : cmp Cne (of_optbool ob) 1 = of_optbool (bnot <$> ob) := sorry'

theorem cmpu_ne_0_optbool (valid_ptr ob) :
  cmpu valid_ptr Cne (of_optbool ob) 0 = of_optbool ob := sorry'

theorem cmpu_eq_1_optbool (valid_ptr ob) :
  cmpu valid_ptr Ceq (of_optbool ob) 1 = of_optbool ob := sorry'

theorem cmpu_eq_0_optbool (valid_ptr ob) :
  cmpu valid_ptr Ceq (of_optbool ob) 0 = of_optbool (bnot <$> ob) := sorry'

theorem cmpu_ne_1_optbool (valid_ptr ob) :
  cmpu valid_ptr Cne (of_optbool ob) 1 = of_optbool (bnot <$> ob) := sorry'

lemma zero_ext_and (n v) : 0 < n → n < 32 →
  val.zero_ext n v = val.and v (Vint (repr (2^n - 1))) := sorry'

lemma rolm_lt_zero (v) : rolm v 1 1 = cmp Clt v 0 := sorry'

lemma rolm_ge_zero (v) : val.xor (rolm v 1 1) 1 = cmp Cge v 0 := sorry'

/- The ``is less defined'' relation between values.
    A value is less defined than itself, and [Vundef] is
    less defined than any value. -/

inductive lessdef : val → val → Prop
| refl (v) : lessdef v v
| undef (v) : lessdef Vundef v

lemma lessdef_of_eq : Π {v1 v2}, v1 = v2 → lessdef v1 v2
| v ._ rfl := lessdef.refl v

lemma lessdef_trans {v1 v2 v3} : lessdef v1 v2 → lessdef v2 v3 → lessdef v1 v3 :=
by intros h1 h2; cases h1; try {assumption}; cases h2; assumption

lemma lessdef_list_inv {vl1 vl2} : list.forall2 lessdef vl1 vl2 → vl1 = vl2 ∨ Vundef ∈ vl1 := sorry'

lemma lessdef_list_trans {vl1 vl2 vl3} :
  list.forall2 lessdef vl1 vl2 → list.forall2 lessdef vl2 vl3 → list.forall2 lessdef vl1 vl3 :=
@list.forall2.trans _ _ @lessdef_trans _ _ _

/- Compatibility of operations with the [lessdef] relation. -/

lemma load_result_lessdef (chunk v1 v2) :
  lessdef v1 v2 → lessdef (load_result chunk v1) (load_result chunk v2) := sorry'

lemma zero_ext_lessdef (n v1 v2) :
  lessdef v1 v2 → lessdef (zero_ext n v1) (zero_ext n v2) := sorry'

lemma sign_ext_lessdef (n v1 v2) :
  lessdef v1 v2 → lessdef (sign_ext n v1) (sign_ext n v2) := sorry'

lemma singleoffloat_lessdef (v1 v2) :
  lessdef v1 v2 → lessdef (single_of_float v1) (single_of_float v2) := sorry'

lemma add_lessdef (v1 v1' v2 v2') :
  lessdef v1 v1' → lessdef v2 v2' → lessdef (v1 + v2) (v1' + v2') := sorry'

lemma addl_lessdef (v1 v1' v2 v2') :
  lessdef v1 v1' → lessdef v2 v2' → lessdef (addl v1 v2) (addl v1' v2') := sorry'

lemma cmpu_bool_lessdef {valid_ptr valid_ptr' : block → ℕ → bool} {c v1 v1' v2 v2' b} :
  (∀ b ofs, valid_ptr b ofs → valid_ptr' b ofs) →
  lessdef v1 v1' → lessdef v2 v2' →
  cmpu_bool valid_ptr c v1 v2 = some b →
  cmpu_bool valid_ptr' c v1' v2' = some b := sorry'

lemma cmplu_bool_lessdef {valid_ptr valid_ptr' : block → ℕ → bool} {c v1 v1' v2 v2' b} :
  (∀ b ofs, valid_ptr b ofs → valid_ptr' b ofs) →
  lessdef v1 v1' → lessdef v2 v2' →
  cmplu_bool valid_ptr c v1 v2 = some b →
  cmplu_bool valid_ptr' c v1' v2' = some b := sorry'

lemma of_optbool_lessdef {ob ob'} :
  (∀ b, ob = some b → ob' = some b) →
  lessdef (of_optbool ob) (of_optbool ob') := sorry'

lemma long_of_words_lessdef {v1 v2 v1' v2'} :
  lessdef v1 v1' → lessdef v2 v2' → lessdef (long_of_words v1 v2) (long_of_words v1' v2') := sorry'

lemma loword_lessdef {v v'} : lessdef v v' → lessdef (loword v) (loword v') := sorry'

lemma hiword_lessdef {v v'} : lessdef v v' → lessdef (hiword v) (hiword v') := sorry'

lemma offset_ptr_zero (v) : lessdef (offset_ptr v 0) v := sorry'

lemma offset_ptr_assoc (v d1 d2) : offset_ptr (offset_ptr v d1) d2 = offset_ptr v (d1 + d2) := sorry'

/- * Values and memory injections -/

/- A memory injection [f] is a function from addresses to either [none]
  or [some] of an address and an offset.  It defines a correspondence
  between the blocks of two memory states [m1] and [m2]:
- if [f b = none], the block [b] of [m1] has no equivalent in [m2];
- if [f b = some (b', ofs)], the block [b] of [m2] corresponds to
  a sub-block at offset [ofs] of the block [b'] in [m2].
-/

def meminj : Type := block → option (block × ℤ)

/- A memory injection defines a relation between values that is the
  identity relation, except for pointer values which are shifted
  as prescribed by the memory injection.  Moreover, [Vundef] values
  inject into any other value. -/

inductive inject (mi : meminj) : val → val → Prop
| int (i) : inject (Vint i) (Vint i)
| long (i) : inject (Vlong i) (Vlong i)
| float (f) : inject (Vfloat f) (Vfloat f)
| single (f) : inject (Vsingle f) (Vsingle f)
| ptr (b1 ofs1 b2 ofs2 delta) :
      mi b1 = some (b2, delta) →
      (ofs2 : ptrofs) = ofs1 + repr delta →
      inject (Vptr b1 ofs1) (Vptr b2 ofs2)
| undef (v) : inject Vundef v

lemma inject_ptrofs (mi i) : inject mi (Vptrofs i) (Vptrofs i) := sorry'

section val_inj_ops

parameter f : meminj

lemma load_result_inject (chunk v1 v2) :
  inject f v1 v2 →
  inject f (load_result chunk v1) (load_result chunk v2) := sorry'

theorem add_inject {v1 v1' v2 v2'} :
  inject f v1 v1' → inject f v2 v2' →
  inject f (v1 + v2) (v1' + v2') := sorry'

theorem sub_inject {v1 v1' v2 v2'} :
  inject f v1 v1' → inject f v2 v2' →
  inject f (v1 - v2) (v1' - v2') := sorry'

theorem addl_inject {v1 v1' v2 v2'} :
  inject f v1 v1' → inject f v2 v2' →
  inject f (addl v1 v2) (addl v1' v2') := sorry'

theorem subl_inject {v1 v1' v2 v2'} :
  inject f v1 v1' → inject f v2 v2' →
  inject f (subl v1 v2) (subl v1' v2') := sorry'

lemma offset_ptr_inject {v v'} (ofs) : inject f v v' →
  inject f (offset_ptr v ofs) (offset_ptr v' ofs) := sorry'

lemma cmp_bool_inject {c v1 v2 v1' v2' b} :
  inject f v1 v1' → inject f v2 v2' →
  cmp_bool c v1 v2 = some b → cmp_bool c v1' v2' = some b := sorry'

parameters (valid_ptr1 valid_ptr2 : block → ℕ → bool)

def weak_valid_ptr1 := weak_valid_ptr valid_ptr1
def weak_valid_ptr2 := weak_valid_ptr valid_ptr2

parameter valid_ptr_inj : ∀ b1 ofs b2 delta, f b1 = some (b2, delta) →
  valid_ptr1 b1 (unsigned (ofs : ptrofs)) →
  valid_ptr2 b2 (unsigned (ofs + repr delta))

parameter weak_valid_ptr_inj : ∀ b1 ofs b2 delta, f b1 = some (b2, delta) →
  weak_valid_ptr1 b1 (unsigned (ofs : ptrofs)) →
  weak_valid_ptr2 b2 (unsigned (ofs + repr delta))

parameter weak_valid_ptr_no_overflow : ∀ b1 ofs b2 delta, f b1 = some (b2, delta) →
  weak_valid_ptr1 b1 (unsigned (ofs : ptrofs)) →
  unsigned ofs + unsigned (repr delta : ptrofs) ≤ @max_unsigned ptrofs.wordsize

parameter valid_different_ptrs_inj : ∀ b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 ≠ b2 →
  valid_ptr1 b1 (unsigned (ofs1 : ptrofs)) →
  valid_ptr1 b2 (unsigned (ofs2 : ptrofs)) →
  f b1 = some (b1', delta1) →
  f b2 = some (b2', delta2) →
  b1' = b2' → unsigned (ofs1 + repr delta1) ≠ unsigned (ofs2 + repr delta2)

lemma cmpu_bool_inject {c v1 v2 v1' v2' b} :
  inject f v1 v1' → inject f v2 v2' →
  cmpu_bool valid_ptr1 c v1 v2 = some b →
  cmpu_bool valid_ptr2 c v1' v2' = some b := sorry'

lemma cmplu_bool_inject {c v1 v2 v1' v2' b} :
  inject f v1 v1' → inject f v2 v2' →
  cmplu_bool valid_ptr1 c v1 v2 = some b →
  cmplu_bool valid_ptr2 c v1' v2' = some b := sorry'

lemma long_of_words_inject {v1 v2 v1' v2'} :
  inject f v1 v1' → inject f v2 v2' →
  inject f (long_of_words v1 v2) (long_of_words v1' v2') := sorry'

lemma loword_inject {v v'} : inject f v v' → inject f (loword v) (loword v') := sorry'

lemma hiword_inject {v v'} : inject f v v' → inject f (hiword v) (hiword v') := sorry'

end val_inj_ops

end val

export val (meminj)

/- Monotone evolution of a memory injection. -/

def inject_incr (f1 f2 : meminj) : Prop :=
∀ ⦃b b' delta⦄, f1 b = some (b', delta) → f2 b = some (b', delta)

lemma inject_incr.refl (f) : inject_incr f f := λ _ _ _, id

lemma inject_incr.trans {f1 f2 f3}
  (i1 : inject_incr f1 f2) (i2 : inject_incr f2 f3) : inject_incr f1 f3 :=
λ b b' d h, i2 (i1 h)

lemma val_inject_incr {f1 f2 v v'} :
  inject_incr f1 f2 → inject f1 v v' → inject f2 v v' := sorry'

lemma val_inject_list_incr {f1 f2 vl vl'}
  (i : inject_incr f1 f2) (il : list.forall2 (inject f1) vl vl') :
  list.forall2 (inject f2) vl vl' :=
il.imp (λ x y, val_inject_incr i)

/- The identity injection gives rise to the "less defined than" relation. -/

def inject_id : meminj := λ b, some (b, 0)

lemma val_inject_id {v1 v2} :
  inject inject_id v1 v2 ↔ val.lessdef v1 v2 := sorry'

lemma val_inject_id_list {vl1 vl2} :
  list.forall2 (inject inject_id) vl1 vl2 ↔ list.forall2 val.lessdef vl1 vl2 :=
list.forall2.iff @val_inject_id

/- Composing two memory injections -/

def val.meminj.comp (f f' : meminj) : meminj := λ b,
do ⟨b', delta⟩ ← f b,
   ⟨b'', delta'⟩ ← f' b',
   return (b'', delta + delta')

lemma inject.comp {f f' v1 v2 v3} :
  inject f v1 v2 → inject f' v2 v3 →
  inject (f.comp f') v1 v3 := sorry'

end values