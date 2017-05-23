import .archi .lib

namespace integers

/- * Comparisons -/

inductive comparison : Type
| Ceq : comparison    /- same -/
| Cne : comparison    /- different -/
| Clt : comparison    /- less than -/
| Cle : comparison    /- less than or equal -/
| Cgt : comparison    /- greater than -/
| Cge : comparison    /- greater than or equal -/
export comparison

def negate_comparison : comparison → comparison
| Ceq := Cne
| Cne := Ceq
| Clt := Cge
| Cle := Cgt
| Cgt := Cle
| Cge := Clt

def swap_comparison : comparison → comparison
| Ceq := Ceq
| Cne := Cne
| Clt := Cgt
| Cle := Cge
| Cgt := Clt
| Cge := Cle

/- * Parameterization by the word size, in bits. -/

section Int

parameter {wordsize_pnat : ℕ+}

def wordsize : ℕ := wordsize_pnat
theorem wordsize_pos : wordsize > 0 := wordsize_pnat.2

def modulus : ℕ := 2^wordsize
def half_modulus : ℕ := modulus / 2
def max_unsigned : ℕ := modulus - 1
def max_signed : ℕ := half_modulus - 1
def min_signed : ℤ := - half_modulus

theorem wordsize_pos : (wordsize:ℤ) > 0 := int.coe_nat_lt_coe_nat_of_lt wordsize_pos

theorem modulus_pos : modulus > 0 := nat.pos_pow_of_pos _ dec_trivial

theorem succ_max_unsigned : nat.succ max_unsigned = modulus :=
nat.succ_pred_eq_of_pos modulus_pos


/- * Representation of machine integers -/

/- A machine integer (type [int]) is represented as a Coq arbitrary-precision
  integer (type [Z]) plus a proof that it is in the range 0 (included) to
  [modulus] (excluded). -/

def Int := fin modulus

/- The [unsigned] and [signed] functions return the Coq integer corresponding
  to the given machine integer, interpreted as unsigned or signed
  respectively. -/

def unsigned (n : Int) : ℕ := n.1

def signed (n : Int) : ℤ :=
let x := unsigned n in    
if x < half_modulus then x else x - modulus
instance coe_Int_int : has_coe Int ℤ := ⟨signed⟩

/- Conversely, [repr] takes a Coq integer and returns the corresponding
  machine integer.  The argument is treated modulo [modulus]. -/

def repr (x : ℤ) : Int :=
show fin modulus, by rw -succ_max_unsigned; exact fin.of_int x

def in_srange (x : ℤ) : bool := min_signed ≤ x ∧ x < half_modulus
def in_urange (x : ℤ) : bool := 0 ≤ x ∧ x < modulus

def iwordsize := repr wordsize

instance : has_zero Int := ⟨repr 0⟩
instance : has_one Int := ⟨repr 1⟩

instance eq_dec : decidable_eq Int := by tactic.mk_dec_eq_instance

/- * Arithmetic and logical operations over machine integers -/

def Int.ltu (x y : Int) : Prop := unsigned x < unsigned y
instance : has_lt Int := ⟨λx y, signed x < signed y⟩
instance : has_le Int := ⟨λx y, signed x ≤ signed y⟩

protected def Int.neg (x : Int) : Int := repr (-unsigned x)
instance : has_neg Int := ⟨Int.neg⟩

protected def Int.add (x y : Int) : Int := repr (unsigned x + unsigned y)
-- Use group subtraction
--protected def Int.sub (x y : Int) : Int := repr (unsigned x - unsigned y)
protected def Int.mul (x y : Int) : Int := repr (unsigned x * unsigned y)
instance : has_add Int := ⟨Int.add⟩
--instance : has_sub Int := ⟨Int.sub⟩
instance : has_mul Int := ⟨Int.mul⟩

def Int.divs (x y : Int) : Int := repr (int.quot (signed x) (signed y))
def Int.mods (x y : Int) : Int := repr (int.rem  (signed x) (signed y))
instance : has_div Int := ⟨Int.divs⟩
instance : has_mod Int := ⟨Int.mods⟩

def Int.divu (x y : Int) : Int := repr (unsigned x / unsigned y : ℕ)
def Int.modu (x y : Int) : Int := repr (unsigned x % unsigned y : ℕ)

/- Bitwise boolean operations. -/

protected def Int.and (x y : Int) : Int := repr (int.land (unsigned x) (unsigned y))
protected def Int.or  (x y : Int) : Int := repr (int.lor  (unsigned x) (unsigned y))
protected def Int.xor (x y : Int) : Int := repr (int.lxor (unsigned x) (unsigned y))

protected def Int.not (x : Int) : Int := repr (int.lnot (unsigned x))

/- Shifts and rotates. -/

def Int.shl  (x y : Int) : Int := repr (int.shiftl (unsigned x) (unsigned y))
def Int.shru (x y : Int) : Int := repr (int.shiftr (unsigned x) (unsigned y))
def Int.shr  (x y : Int) : Int := repr (int.shiftr (signed x)   (unsigned y))

def Int.rol (x y : Int) : Int :=
let n := unsigned y % wordsize in
repr (int.lor (int.shiftl (unsigned x) n) (int.shiftr (unsigned x) (wordsize - n)))
def Int.ror (x y : Int) : Int :=
let n := unsigned y % wordsize in
repr (int.lor (int.shiftr (unsigned x) n) (int.shiftl (unsigned x) (wordsize - n)))

def Int.rolm (x a m : Int) : Int := Int.and (Int.rol x a) m

/- Viewed as signed divisions by powers of two, [shrx] rounds towards
  zero, while [shr] rounds towards minus infinity. -/

def Int.shrx (x y : Int) : Int := x / Int.shl 1 y

/- High half of full multiply. -/

def Int.mulhu (x y : Int) : Int := repr ((unsigned x * unsigned y) / modulus)
def Int.mulhs (x y : Int) : Int := repr ((signed x * signed y) / modulus)

open Int

instance coe_bool_Int : has_coe bool Int := ⟨λb, cond b 1 0⟩

/- Condition flags -/

def negative (x : Int) : Int := to_bool (x < 0)

def add_carry (x y cin : Int) : Int :=
to_bool (unsigned x + unsigned y + unsigned cin ≥ modulus)

def add_overflow (x y cin : Int) : Int :=
bnot $ in_srange (signed x + signed y + signed cin)

def sub_borrow (x y bin : Int) : Int :=
to_bool (unsigned x - unsigned y - unsigned bin < 0)

def sub_overflow (x y bin : Int) : Int :=
bnot $ in_srange (signed x - signed y - signed bin)

/- [shr_carry x y] is 1 if [x] is negative and at least one 1 bit is shifted away. -/

def shr_carry (x y : Int) : Int :=
to_bool (x < 0 ∧ Int.and x (shl 1 y + -1) ≠ 0)

/- Zero and sign extensions -/

def zero_ext (n : ℕ) (x : Int) : Int := repr (unsigned x % 2^n)

def sign_ext (n : ℕ+) (x : Int) : Int :=
let modulus' := 2^n.1, y := unsigned x % modulus' in    
repr (if y < modulus'/2 then y else y - modulus')

/- Decomposition of a number as a sum of powers of two. -/

def one_bits (x : Int) : list Int :=
(num.one_bits (unsigned x)).map (λx:ℕ, repr x) 

/- Recognition of powers of two. -/

def is_power2 (x : Int) : option Int :=
match num.one_bits (unsigned x) with
| [i] := some (repr i)
| _ := none
end

/- Comparisons. -/

instance decidable_lt : @decidable_rel Int (<) := by apply_instance
instance decidable_le : @decidable_rel Int (≤) := by apply_instance
instance decidable_ltu : decidable_rel Int.ltu := by delta ltu; apply_instance

def cmp : comparison → Int → Int → bool
| Ceq x y := x = y
| Cne x y := x ≠ y
| Clt x y := x < y
| Cle x y := x ≤ y
| Cgt x y := y < x
| Cge x y := y ≤ x

def cmpu : comparison → Int → Int → bool
| Ceq x y := x = y
| Cne x y := x ≠ y
| Clt x y := ltu x y
| Cle x y := bnot (ltu y x)
| Cgt x y := ltu y x
| Cge x y := bnot (ltu x y)

def is_false (x : Int) : Prop := x = 0
def is_true  (x : Int) : Prop := x ≠ 0
def notbool  (x : Int) : Int  := to_bool (x = 0)

/- x86-style extended division and modulus -/

def divmodu2 (nhi nlo : Int) (d : Int) : option (Int × Int) :=
if d = 0 then none else
  let q := unsigned nhi * modulus + unsigned nlo / unsigned d in
  if q < modulus then
    some (repr q, repr (unsigned nhi * modulus + unsigned nlo % unsigned d))
  else none

def divmods2 (nhi nlo : Int) (d : Int) : option (Int × Int) :=
if d = 0 then none else
  let q := int.quot (signed nhi * modulus + unsigned nlo) (signed d) in
  if in_srange q then
    some (repr q, repr (int.rem (signed nhi * modulus + unsigned nlo) (signed d)))
  else none

/- * Properties of integers and integer arithmetic -/

/- ** Properties of [modulus], [max_unsigned], etc. -/

theorem half_modulus_power : half_modulus = 2^(wordsize - 1) := sorry

theorem half_modulus_modulus : modulus = 2 * half_modulus := sorry

/- Relative positions, from greatest to smallest:
<<
      max_unsigned
      max_signed
      2*wordsize-1
      wordsize
      0
      min_signed
>>
-/

theorem half_modulus_pos : half_modulus > 0 := sorry

theorem min_signed_neg : min_signed < 0 := sorry

theorem max_signed_pos : max_signed ≥ 0 := sorry

theorem two_wordsize_max_unsigned : 2 * wordsize - 1 ≤ max_unsigned := sorry

theorem max_signed_unsigned : max_signed < max_unsigned := sorry

lemma unsigned_repr_eq (x) : (unsigned (repr x) : ℤ) = x % modulus := sorry

lemma signed_repr_eq (x) : signed (repr x) =
  if x % modulus < half_modulus then x % modulus else x % modulus - modulus := sorry

theorem unsigned_range (i) : unsigned i < modulus := sorry

theorem unsigned_range_2 (i) : unsigned i ≤ max_unsigned := sorry

theorem min_signed_range (i) : min_signed ≤ signed i := sorry

theorem max_signed_range (i) : signed i ≤ max_signed := sorry

theorem repr_unsigned (i) : repr (unsigned i) = i := sorry

lemma repr_signed (i) : repr (signed i) = i := sorry

theorem unsigned_repr (z) : z ≤ max_unsigned → unsigned (repr z) = z := sorry

theorem signed_repr (z) : min_signed ≤ z → z ≤ max_signed → signed (repr z) = z := sorry

theorem signed_eq_unsigned (x) : unsigned x ≤ max_signed → signed x = unsigned x := sorry

theorem signed_positive (x) : 0 ≤ signed x ↔ unsigned x ≤ max_signed := sorry

/- ** Properties of zero, one, minus one -/

theorem unsigned_zero : unsigned 0 = 0 := sorry

theorem unsigned_one : unsigned 1 = 1 := sorry

theorem unsigned_mone : unsigned (-1) = modulus - 1 := sorry

theorem signed_zero : signed 0 = 0 := sorry

theorem signed_mone : signed (-1) = -1 := sorry

theorem one_ne_zero : (1:Int) ≠ 0 := sorry

theorem unsigned_repr_wordsize : unsigned iwordsize = wordsize := sorry

/- ** Properties of equality -/

theorem eq_signed (x y) : x = y ↔ signed x = signed y := sorry

theorem eq_unsigned (x y) : x = y ↔ unsigned x = unsigned y := sorry

/- ** Properties of addition -/

theorem add_unsigned (x y) : x + y = repr (unsigned x + unsigned y) := sorry

theorem add_signed (x y) : x + y = repr (signed x + signed y) := sorry

theorem add_comm (x y : Int) : x + y = y + x := sorry

theorem add_zero (x : Int) : x + 0 = x := sorry

theorem add_assoc (x y z : Int) : (x + y) + z = x + (y + z) := sorry

theorem add_left_neg (x : Int) : -x + x = 0 := sorry

theorem unsigned_add_carry (x y) :
  unsigned (x + y) = unsigned x + unsigned y - unsigned (add_carry x y 0) * modulus := sorry

theorem unsigned_add_either (x y) :
  unsigned (x + y) = unsigned x + unsigned y
  ∨ (unsigned (x + y) : ℤ) = unsigned x + unsigned y - modulus := sorry

/- ** Properties of negation -/

theorem neg_repr (z) : -(repr z) = repr (-z) := sorry

/- ** Properties of multiplication -/

theorem mul_comm (x y : Int) : x * y = y * x := sorry

theorem mul_one (x : Int) : x * 1 = x := sorry

theorem mul_assoc (x y z : Int) : (x * y) * z = x * (y * z) := sorry

theorem right_distrib (x y z : Int) : (x + y) * z = x * z + y * z := sorry

theorem mul_signed (x y) : x * y = repr (signed x * signed y) := sorry

instance : comm_ring Int :=
{ add            := Int.add,
  add_assoc      := add_assoc,
  zero           := 0,
  zero_add       := λx, by rw [add_comm, add_zero],
  add_zero       := add_zero,
  neg            := Int.neg,
  add_left_neg   := add_left_neg,
  add_comm       := add_comm,
  mul            := Int.mul,
  mul_assoc      := mul_assoc,
  one            := 1,
  one_mul        := λx, by rw [mul_comm, mul_one],
  mul_one        := mul_one,
  left_distrib   := λx y z,
    by rw [mul_comm, right_distrib, mul_comm y x, mul_comm z x]; refl,
  right_distrib  := right_distrib,
  mul_comm       := mul_comm }

/- ** Properties of subtraction -/

theorem sub_unsigned (x y) : x - y = repr (unsigned x - unsigned y) := sorry

theorem sub_signed (x y) : x - y = repr (signed x - signed y) := sorry

theorem unsigned_sub_borrow (x y) : unsigned (x - y) =
  unsigned x - unsigned y + unsigned (sub_borrow x y 0) * modulus := sorry

/- ** Properties of division and modulus -/

lemma divu_add_modu (x y) : y ≠ 0 → divu x y * y + modu x y = x := sorry

theorem modu_divu (x y) : y ≠ 0 → modu x y = x - divu x y * y := sorry

lemma mods_divs_Euclid (x y : Int) : x / y * y + x % y = x := sorry

theorem mods_divs (x y : Int) : x % y = x - x / y * y := sorry

theorem divu_one (x) : divu x 1 = x := sorry

theorem modu_one (x) : modu x 1 = 0 := sorry

theorem divs_mone (x : Int) : x / (-1) = -x := sorry

theorem mods_mone (x : Int) : x % (-1) = 0 := sorry

theorem divmodu2_divu_modu (n d) :
  d ≠ 0 → divmodu2 0 n d = some (divu n d, modu n d) := sorry

lemma unsigned_signed (n) : (unsigned n : ℤ) =
  if n < 0 then signed n + modulus else signed n := sorry

theorem divmods2_divs_mods (n d) :
  d ≠ 0 → n ≠ repr min_signed ∨ d ≠ -1 →
  divmods2 (if n < 0 then -1 else 0) n d = some (divs n d, mods n d) := sorry

/- ** Bit-level properties -/

/- ** Bit-level reasoning over type [int] -/

def test_bit (x : Int) (i : ℕ) : bool := int.test_bit (unsigned x) i

lemma test_bit_repr (x i) : i < wordsize →
  test_bit (repr x) i = int.test_bit x i := sorry

lemma same_bits_eq (x y) :
  (∀ i < wordsize, test_bit x i = test_bit y i) →
  x = y := sorry

lemma bits_above (x i) : i ≥ wordsize → test_bit x i = ff := sorry

lemma bits_zero (i) : test_bit 0 i = ff := sorry

theorem bits_one (n) : test_bit 1 n = to_bool (n = 0) := sorry

lemma bits_mone (i) : i < wordsize → test_bit (-1) i := sorry

lemma sign_bit_of_unsigned (x) : test_bit x (wordsize - 1) =
  to_bool (unsigned x ≥ half_modulus) := sorry

lemma bits_signed (x i) : int.test_bit (signed x) i =
  test_bit x (if i < wordsize then i else wordsize - 1) := sorry

lemma bits_le (x y) :
  (∀ i < wordsize, test_bit x i → test_bit y i) →
  unsigned x ≤ unsigned y := sorry

/- ** Properties of bitwise and, or, xor -/

@[simp] lemma bits_and (x y i) : i < wordsize →
  test_bit (Int.and x y) i = test_bit x i && test_bit y i := sorry

@[simp] lemma bits_or (x y i) : i < wordsize →
  test_bit (Int.or x y) i = test_bit x i || test_bit y i := sorry

@[simp] lemma bits_xor (x y i) : i < wordsize →
  test_bit (Int.xor x y) i = bxor (test_bit x i) (test_bit y i) := sorry

@[simp] lemma bits_not (x i) : i < wordsize →
  test_bit (Int.not x) i = bnot (test_bit x i) := sorry

theorem and_comm (x y) : Int.and x y = Int.and y x := sorry

theorem and_assoc (x y z) : Int.and (Int.and x y) z = Int.and x (Int.and y z) := sorry

@[simp] theorem and_zero (x) : Int.and x 0 = 0 := sorry

@[simp] theorem zero_and (x) : Int.and 0 x = 0 := sorry

@[simp] theorem and_mone (x) : Int.and x (-1) = x := sorry

@[simp] theorem mone_and (x) : Int.and (-1) x = x := sorry

@[simp] theorem and_self (x) : and x x = x := sorry

theorem or_comm (x y) : Int.or x y = Int.or y x := sorry

theorem or_assoc (x y z) : Int.or (Int.or x y) z = Int.or x (Int.or y z) := sorry

@[simp] theorem or_zero (x) : Int.or x 0 = x := sorry

@[simp] theorem zero_or (x) : Int.or 0 x = x := sorry

@[simp] theorem or_mone (x) : Int.or x (-1) = -1 := sorry

@[simp] theorem or_self (x) : Int.or x x = x := sorry

theorem and_or_left_distrib (x y z) :
  Int.and x (Int.or y z) = Int.or (Int.and x y) (Int.and x z) := sorry

theorem and_or_right_distrib (x y z) :
  Int.and (Int.or x y) z = Int.or (Int.and x z) (Int.and y z) := sorry

theorem or_and_left_distrib (x y z) :
  Int.or x (Int.and y z) = Int.and (Int.or x y) (Int.or x z) := sorry

theorem or_and_right_distrib (x y z) :
  Int.or (Int.and x y) z = Int.and (Int.or x z) (Int.or y z) := sorry

@[simp] theorem and_or_absorb (x y) : Int.and x (Int.or x y) = x := sorry

@[simp] theorem or_and_absorb (x y) : Int.or x (Int.and x y) = x := sorry

theorem xor_comm (x y) : Int.xor x y = Int.xor y x := sorry

theorem xor_assoc (x y z) : Int.xor (Int.xor x y) z = Int.xor x (Int.xor y z) := sorry

@[simp] theorem xor_zero (x) : Int.xor x 0 = x := sorry

@[simp] theorem zero_xor (x) : Int.xor 0 x = x := sorry

@[simp] theorem xor_self (x) : Int.xor x x = 0 := sorry

@[simp] theorem xor_zero_one : Int.xor 0 1 = 1 := zero_xor _

@[simp] theorem xor_one_one : Int.xor 1 1 = 0 := xor_self _

theorem eq_of_xor_zero (x y) : Int.xor x y = 0 → x = y := sorry

theorem and_xor_distrib (x y z) :
  Int.and x (Int.xor y z) = Int.xor (Int.and x y) (Int.and x z) := sorry

theorem and_le (x y) : unsigned (Int.and x y) ≤ unsigned x := sorry

theorem or_le (x y) : unsigned x ≤ unsigned (Int.or x y) := sorry

/- Properties of bitwise complement.-/

theorem not_not (x) : Int.not (Int.not x) = x := sorry

theorem not_zero : Int.not 0 = -1 := sorry

theorem not_mone : Int.not (-1) = 0 := sorry

theorem not_or_and_not (x y) : Int.not (Int.or x y) = Int.and (Int.not x) (Int.not y) := sorry

theorem not_and_or_not (x y) : Int.not (Int.and x y) = Int.or (Int.not x) (Int.not y) := sorry

theorem and_not_self (x) : Int.and x (Int.not x) = 0 := sorry

theorem or_not_self (x) : Int.or x (Int.not x) = -1 := sorry

theorem xor_not_self (x) : Int.xor x (Int.not x) = -1 := sorry

lemma unsigned_not (x) : unsigned (Int.not x) = max_unsigned - unsigned x := sorry

theorem not_neg (x) : Int.not x = -x - 1 := sorry

theorem neg_not (x) : -x = Int.not x + 1 := sorry

theorem sub_add_not (x y) : x - y = x + Int.not y + 1 := sorry

theorem sub_add_not_3 (x y b) : b = 0 ∨ b = 1 →
  x - y - b = x + Int.not y + Int.xor b 1 := sorry

theorem sub_borrow_add_carry (x y b) : b = 0 ∨ b = 1 →
  sub_borrow x y b = Int.xor (add_carry x (Int.not y) (Int.xor b 1)) 1 := sorry

/- Connections between [add] and bitwise logical operations. -/

lemma Z_add_is_or (i x y) :
  (∀ j ≤ i, int.test_bit x j && int.test_bit y j = ff) →
  int.test_bit (x + y) i = int.test_bit x i || int.test_bit y i := sorry

theorem add_is_or (x y) : Int.and x y = 0 → x + y = Int.or x y := sorry

theorem xor_is_or (x y) : Int.and x y = 0 → Int.xor x y = Int.or x y := sorry

theorem add_is_xor (x y) : Int.and x y = 0 → x + y = Int.xor x y := sorry

theorem add_and (x y z) : Int.and y z = 0 →
  Int.and x y + Int.and x z = Int.and x (Int.or y z) := sorry

/- ** Properties of shifts -/

@[simp] lemma bits_shl (x y i) : i < wordsize → test_bit (shl x y) i =
  if i < unsigned y then ff else test_bit x (i - unsigned y) := sorry

@[simp] lemma bits_shru (x y i) : i < wordsize → test_bit (shru x y) i =
  if i + unsigned y < wordsize then test_bit x (i + unsigned y) else ff := sorry

@[simp] lemma bits_shr (x y i) : i < wordsize → test_bit (shr x y) i =
  test_bit x (if i + unsigned y < wordsize then i + unsigned y else wordsize - 1) := sorry

@[simp] theorem shl_zero (x) : shl x 0 = x := sorry

lemma bitwise_binop_shl {f : Int → Int → Int} {f' : bool → bool → bool} :
  (∀ x y i, i < wordsize → test_bit (f x y) i = f' (test_bit x i) (test_bit y i)) →
  f' ff ff = ff →
  ∀ x y n, f (shl x n) (shl y n) = shl (f x y) n := sorry

theorem and_shl : ∀ x y n, Int.and (shl x n) (shl y n) = shl (Int.and x y) n :=
bitwise_binop_shl bits_and rfl

theorem or_shl : ∀ x y n, Int.or (shl x n) (shl y n) = shl (Int.or x y) n :=
bitwise_binop_shl bits_or rfl

theorem xor_shl : ∀ x y n, Int.xor (shl x n) (shl y n) = shl (Int.xor x y) n :=
bitwise_binop_shl bits_xor rfl

lemma ltu_inv (x y) : ltu x y → unsigned x < unsigned y := sorry

lemma ltu_iwordsize_inv (x) : ltu x iwordsize → unsigned x < wordsize := sorry

theorem shl_shl (x y z) : ltu y iwordsize → ltu z iwordsize →
  ltu (y + z) iwordsize → shl (shl x y) z = shl x (y + z) := sorry

theorem shru_zero (x) : shru x 0 = x := sorry

lemma bitwise_binop_shru {f : Int → Int → Int} {f' : bool → bool → bool} :
  (∀ x y i, i < wordsize → test_bit (f x y) i = f' (test_bit x i) (test_bit y i)) →
  f' ff ff = ff →
  ∀ x y n, f (shru x n) (shru y n) = shru (f x y) n := sorry

theorem and_shru : ∀ x y n, Int.and (shru x n) (shru y n) = shru (Int.and x y) n :=
bitwise_binop_shru bits_and rfl

theorem or_shru : ∀ x y n, Int.or (shru x n) (shru y n) = shru (Int.or x y) n :=
bitwise_binop_shru bits_or rfl

theorem xor_shru : ∀ x y n, Int.xor (shru x n) (shru y n) = shru (Int.xor x y) n :=
bitwise_binop_shru bits_xor rfl

theorem shru_shru (x y z) : ltu y iwordsize → ltu z iwordsize →
  ltu (y + z) iwordsize → shru (shru x y) z = shru x (y + z) := sorry

theorem shr_zero (x) : shr x 0 = x := sorry

lemma bitwise_binop_shr {f : Int → Int → Int} {f' : bool → bool → bool} :
  (∀ x y i, i < wordsize → test_bit (f x y) i = f' (test_bit x i) (test_bit y i)) →
  ∀ x y n, f (shr x n) (shr y n) = shr (f x y) n := sorry

theorem and_shr : ∀ x y n, Int.and (shr x n) (shr y n) = shr (Int.and x y) n :=
bitwise_binop_shr bits_and

theorem or_shr : ∀ x y n, Int.or (shr x n) (shr y n) = shr (Int.or x y) n :=
bitwise_binop_shr bits_or

theorem xor_shr : ∀ x y n, Int.xor (shr x n) (shr y n) = shr (Int.xor x y) n :=
bitwise_binop_shr bits_xor

theorem shr_shr (x y z) : ltu y iwordsize → ltu z iwordsize →
  ltu (y + z) iwordsize → shr (shr x y) z = shr x (y + z) := sorry

theorem and_shr_shru (x y z) : Int.and (shr x z) (shru y z) = shru (Int.and x y) z := sorry

theorem shr_and_shru_and (x y z) : shru (shl z y) y = z →
  Int.and (shr x y) z = Int.and (shru x y) z := sorry

theorem shru_lt_zero (x) : shru x (repr (wordsize - 1)) = to_bool (x < 0) := sorry

theorem shr_lt_zero (x) : shr x (repr (wordsize - 1)) = -to_bool (x < 0) := sorry

/- ** Properties of rotations -/

@[simp] lemma bits_rol (x y i) : i < wordsize →
  test_bit (rol x y) i = test_bit x ((i - unsigned y) % wordsize) := sorry

@[simp] lemma bits_ror (x y i) : i < wordsize →
  test_bit (ror x y) i = test_bit x ((i + unsigned y) % wordsize) := sorry

theorem shl_rolm (x n) : ltu n iwordsize → shl x n = rolm x n (shl (-1) n) := sorry

theorem shru_rolm (x n) : ltu n iwordsize →
  shru x n = rolm x (iwordsize - n) (shru (-1) n) := sorry

theorem rol_zero (x) : rol x 0 = x := sorry

lemma bitwise_binop_rol {f : Int → Int → Int} {f' : bool → bool → bool} :
  (∀ x y i, i < wordsize → test_bit (f x y) i = f' (test_bit x i) (test_bit y i)) →
  ∀ x y n, rol (f x y) n = f (rol x n) (rol y n) := sorry

theorem rol_and : ∀ x y n, rol (Int.and x y) n = Int.and (rol x n) (rol y n) :=
bitwise_binop_rol bits_and

theorem rol_or : ∀ x y n, rol (Int.or x y) n = Int.or (rol x n) (rol y n) :=
bitwise_binop_rol bits_or

theorem rol_xor : ∀ x y n, rol (Int.xor x y) n = Int.xor (rol x n) (rol y n) :=
bitwise_binop_rol bits_xor

theorem rol_rol (x n m) : wordsize ∣ modulus →
  rol (rol x n) m = rol x (modu (n + m) iwordsize) := sorry

theorem rolm_zero (x m) : rolm x 0 m = Int.and x m := sorry

theorem rolm_rolm (x n₁ m₁ n₂ m₂) : wordsize ∣ modulus →
  rolm (rolm x n₁ m₁) n₂ m₂ =
  rolm x (modu (n₁ + n₂) iwordsize) (Int.and (rol m₁ n₂) m₂) := sorry

theorem or_rolm (x n m₁ m₂) : Int.or (rolm x n m₁) (rolm x n m₂) = rolm x n (Int.or m₁ m₂) := sorry

theorem ror_rol (x y) : ltu y iwordsize → ror x y = rol x (iwordsize - y) := sorry

theorem ror_rol_neg (x y) : wordsize ∣ modulus → ror x y = rol x (-y) := sorry

theorem or_ror (x y z) : ltu y iwordsize → ltu z iwordsize →
  y + z = iwordsize → ror x z = Int.or (shl x y) (shru x z) := sorry

/- ** Properties of [Z_one_bits] and [is_power2]. -/

lemma is_power2_rng (n logn) : is_power2 n = some logn → unsigned logn < wordsize :=
sorry

theorem is_power2_range (n logn) : is_power2 n = some logn → ltu logn iwordsize :=
sorry

lemma is_power2_correct (n logn) : is_power2 n = some logn →
  unsigned n = 2^unsigned logn := sorry

theorem two_p_range (n) : n < wordsize → 2^n ≤ max_unsigned := sorry

lemma is_power2_two_p (n) : n < wordsize → is_power2 (repr (2^n)) = some (repr n) := sorry

/- ** Relation between bitwise operations and multiplications / divisions by powers of 2 -/

/- Left shifts and multiplications by powers of 2. -/

lemma Zshiftl_mul_two_p (x) (n : ℕ) : int.shiftl x n = x * 2^n := sorry

lemma shl_mul_two_p (x y) : shl x y = x * repr (2 ^ unsigned y) := sorry

theorem shl_mul (x y) : shl x y = x * shl 1 y := sorry

theorem mul_pow2 (x n logn) : is_power2 n = some logn → x * n = shl x logn := sorry

theorem shifted_or_is_add (x y n) : n < wordsize → unsigned y < 2^n →
  Int.or (shl x (repr n)) y = repr (unsigned x * 2^n + unsigned y) := sorry

/- Unsigned right shifts and unsigned divisions by powers of 2. -/

lemma shru_div_two_p (x y) :
  shru x y = repr (unsigned x / 2^unsigned y) := sorry

theorem divu_pow2 (x n logn) : is_power2 n = some logn → divu x n = shru x logn := sorry

/- Signed right shifts and signed divisions by powers of 2. -/

lemma shr_div_two_p (x y) : shr x y = repr (signed x / 2^unsigned y) := sorry

theorem divs_pow2 (x n logn) : is_power2 n = some logn → x / n = shrx x logn := sorry

/- Unsigned modulus over [2^n] is masking with [2^n-1]. -/

theorem modu_and (x n logn) : is_power2 n = some logn → modu x n = Int.and x (n - 1) := sorry

/- ** Properties of [shrx] (signed division by a power of 2) -/

lemma int.quot_div (x y) : y > 0 →
  int.quot x y = if x < 0 then (x + y - 1) / y else x / y := sorry

theorem shrx_shr (x y) : ltu y (repr (wordsize - 1)) →
  shrx x y = shr (if x < 0 then x + (shl 1 y - 1) else x) y := sorry

theorem shrx_shr_2 (x y) : ltu y (repr (wordsize - 1)) →
  shrx x y = shr (x + shru (shr x (repr (wordsize - 1))) (iwordsize - y)) y := sorry

lemma Zdiv_shift (x y) : y > 0 →
  (x + (y - 1)) / y = x / y + if x % y = 0 then 0 else 1 := sorry

theorem shrx_carry (x y) : ltu y (repr (wordsize - 1)) →
  shrx x y = shr x y + shr_carry x y := sorry

/- Connections between [shr] and [shru]. -/

lemma shr_shru_positive (x y) : signed x ≥ 0 → shr x y = shru x y := sorry

lemma and_positive (x y) : signed y ≥ 0 → signed (Int.and x y) ≥ 0 := sorry

theorem shr_and_is_shru_and (x y z) : y ≥ 0 →
  shr (Int.and x y) z = shru (Int.and x y) z := sorry

@[simp] lemma bits_zero_ext (n x i) :
  test_bit (zero_ext n x) i = to_bool (i < n) && test_bit x i := sorry

@[simp] lemma bits_sign_ext (n x i) : i < wordsize →
  test_bit (sign_ext n x) i = test_bit x (if i < n then i else n - 1) := sorry

theorem zero_ext_above (n x) : n ≥ wordsize → zero_ext n x = x := sorry

theorem sign_ext_above (n : ℕ+) (x) : n.1 ≥ wordsize → sign_ext n x = x := sorry

theorem zero_ext_and (n x) : zero_ext n x = Int.and x (repr (2^n - 1)) := sorry

theorem zero_ext_mod (n x) : n < wordsize →
  unsigned (zero_ext n x) = unsigned x % 2^n := sorry

theorem zero_ext_widen (x n n') : n ≤ n' →
  zero_ext n' (zero_ext n x) = zero_ext n x := sorry

theorem sign_ext_widen (x) (n n' : ℕ+) : n.1 ≤ n'.1 →
  sign_ext n' (sign_ext n x) = sign_ext n x := sorry

theorem sign_zero_ext_widen (x n) (n' : ℕ+) : n < n'.1 →
  sign_ext n' (zero_ext n x) = zero_ext n x := sorry

theorem zero_ext_narrow (x n n') : n ≤ n' →
  zero_ext n (zero_ext n' x) = zero_ext n x := sorry

theorem sign_ext_narrow (x) (n n' : ℕ+) : n.1 ≤ n'.1 →
  sign_ext n (sign_ext n' x) = sign_ext n x := sorry

theorem zero_sign_ext_narrow (x n) (n' : ℕ+) : n ≤ n'.1 →
  zero_ext n (sign_ext n' x) = zero_ext n x := sorry

theorem zero_ext_self (n x) : zero_ext n (zero_ext n x) = zero_ext n x := sorry

theorem sign_ext_self (n x) : sign_ext n (sign_ext n x) = sign_ext n x := sorry

theorem sign_ext_zero_ext (x n) : sign_ext n (zero_ext n x) = sign_ext n x := sorry

theorem zero_ext_sign_ext (x) (n : ℕ+) : zero_ext n (sign_ext n x) = zero_ext n x := sorry

theorem sign_ext_equal_if_zero_equal (n : ℕ+) (x y) :
  zero_ext n x = zero_ext n y → sign_ext n x = sign_ext n y := sorry

theorem zero_ext_shru_shl (n x) : 0 < n → n < wordsize →
  let y := repr (wordsize - n) in
  zero_ext n x = shru (shl x y) y := sorry

theorem sign_ext_shr_shl (n : ℕ+) (x) : n.1 < wordsize →
  let y := repr (wordsize - n) in
  sign_ext n x = shr (shl x y) y := sorry

/- [zero_ext n x] is the unique integer congruent to [x] modulo [2^n]
    in the range [0...2^n-1]. -/

lemma zero_ext_range (n x) : n < wordsize → unsigned (zero_ext n x) < 2^n := sorry

lemma eqmod_zero_ext (n x) : n < wordsize →
  unsigned (zero_ext n x) = unsigned x % 2^n := sorry

/- [sign_ext n x] is the unique integer congruent to [x] modulo [2^n]
    in the range [-2^(n-1)...2^(n-1) - 1]. -/

lemma sign_ext_range (x) (n : ℕ+) : n.1 < wordsize →
  -(2^(n-1) : ℤ) ≤ signed (sign_ext n x) ∧ signed (sign_ext n x) < 2^(n-1) := sorry

lemma eqmod_sign_ext' (x) (n : ℕ+) : n.1 < wordsize →
  unsigned (sign_ext n x) % 2^n = unsigned x % 2^n := sorry

lemma eqmod_sign_ext (x) (n : ℕ+) : n.1 < wordsize →
  signed (sign_ext n x) % 2^n = unsigned x % 2^n := sorry

/- ** Properties of [one_bits] (decomposition in sum of powers of two) -/

theorem one_bits_range (x i) : i ∈ one_bits x → ltu i iwordsize := sorry

def int_of_one_bits : list Int → Int
| [] := 0
| (a :: l) := shl 1 a + int_of_one_bits l

theorem one_bits_decomp (x) : int_of_one_bits (one_bits x) = x := sorry

/- ** Properties of comparisons -/

theorem negate_cmp (c x y) : cmp (negate_comparison c) x y = bnot (cmp c x y) := sorry

theorem negate_cmpu (c x y) : cmpu (negate_comparison c) x y = bnot (cmpu c x y) := sorry

theorem swap_cmp (c x y) : cmp (swap_comparison c) x y = cmp c y x := sorry

theorem swap_cmpu (c x y) : cmpu (swap_comparison c) x y = cmpu c y x := sorry

lemma translate_ltu (x y d) :
  unsigned x + unsigned d ≤ max_unsigned →
  unsigned y + unsigned d ≤ max_unsigned →
  ltu (x + d) (y + d) ↔ ltu x y := sorry

theorem translate_cmpu (c x y d) :
  unsigned x + unsigned d ≤ max_unsigned →
  unsigned y + unsigned d ≤ max_unsigned →
  cmpu c (x + d) (y + d) = cmpu c x y := sorry

lemma translate_lt (x y d) :
  in_srange (signed x + signed d) →
  in_srange (signed y + signed d) →
  x + d < y + d ↔ x < y := sorry

theorem translate_cmp (c x y d) :
  in_srange (signed x + signed d) →
  in_srange (signed y + signed d) →
  cmp c (x + d) (y + d) = cmp c x y := sorry

theorem notbool_isfalse_istrue (x) : is_false x → is_true (notbool x) := sorry

theorem notbool_istrue_isfalse (x) : is_true x → is_false (notbool x) := sorry

theorem ltu_range_test (x y) : ltu x y → unsigned y ≤ max_signed →
  0 ≤ signed x ∧ signed x < unsigned y := sorry

theorem lt_sub_overflow (x y) :
  Int.xor (sub_overflow x y 0) (negative (x - y)) = to_bool (x < y) := sorry

lemma signed_eq {x y} : x = y ↔ signed x = signed y := sorry

lemma le_iff_lt_or_eq (x y : Int) : x ≤ y ↔ x < y ∨ x = y :=
iff.trans (@le_iff_lt_or_eq ℤ _ _ _) (or_congr iff.rfl signed_eq.symm)

instance : decidable_linear_order Int :=
{ le              := (≤),
  le_refl         := λx, @le_refl ℤ _ _,
  le_trans        := λx y z, @le_trans ℤ _ _ _ _,
  le_antisymm     := λx y h1 h2, signed_eq.2 $ le_antisymm h1 h2,
  lt              := (<),
  le_iff_lt_or_eq := le_iff_lt_or_eq,
  lt_irrefl       := λx, @lt_irrefl ℤ _ _,
  le_total        := λx y, @le_total ℤ _ _ _,
  decidable_lt    := by apply_instance,
  decidable_le    := by apply_instance,
  decidable_eq    := by apply_instance }

lemma ltu_not :
  ∀ x y, ltu y x = negb (ltu x y) && negb (eq x y)
Proof
  intros. rewrite <- negb_orb. rewrite <- not_ltu. rewrite negb_involutive. auto
Qed


/- Non-overlapping test -/

def no_overlap (ofs1 : Int) (sz1 : ℤ) (ofs2 : Int) (sz2 : ℤ) : bool :=
  let x1 := unsigned ofs1 in let x2 := unsigned ofs2 in
     zlt (x1 + sz1) modulus && zlt (x2 + sz2) modulus
  && (zle (x1 + sz1) x2 || zle (x2 + sz2) x1)

lemma no_overlap_sound :
  ∀ ofs1 sz1 ofs2 sz2 base,
  sz1 > 0 → sz2 > 0 → no_overlap ofs1 sz1 ofs2 sz2 = tt →
  unsigned (add base ofs1) + sz1 <= unsigned (add base ofs2)
  ∨ unsigned (add base ofs2) + sz2 <= unsigned (add base ofs1)
Proof
  intros
  destruct (andb_prop _ _ H1). clear H1
  destruct (andb_prop _ _ H2). clear H2
  apply proj_sumbool_true in H1
  apply proj_sumbool_true in H4
  assert (unsigned ofs1 + sz1 <= unsigned ofs2 ∨ unsigned ofs2 + sz2 <= unsigned ofs1)
  destruct (orb_prop _ _ H3). left. eapply proj_sumbool_true; eauto. right. eapply proj_sumbool_true; eauto
  clear H3
  generalize (unsigned_range ofs1) (unsigned_range ofs2). intros P Q
  generalize (unsigned_add_either base ofs1) (unsigned_add_either base ofs2)
  intros [C|C] [D|D]; omega
Qed

/- Size of integers, in bits. -/

def Zsize (x : ℤ) : ℤ :=
  match x with
| Zpos p := Zpos (Pos.size p)
| _ := 0
  end

def size (x : Int) : ℤ := Zsize (unsigned x)

theorem Zsize_pos : ∀ x, 0 <= Zsize x
Proof
  destruct x; simpl. omega. compute; intuition congruence. omega
Qed

theorem Zsize_pos' : ∀ x, 0 < x → 0 < Zsize x
Proof
  destruct x; simpl; intros; try discriminate. compute; auto
Qed

lemma Zsize_shiftin :
  ∀ b x, 0 < x → Zsize (Zshiftin b x) = Zsucc (Zsize x)
Proof
  intros. destruct x; compute in H; try discriminate
  destruct b
  change (Zshiftin tt (Zpos p)) with (Zpos (p~1))
  simpl. f_equal. rewrite Pos.add_1_r; auto
  change (Zshiftin ff (Zpos p)) with (Zpos (p~0))
  simpl. f_equal. rewrite Pos.add_1_r; auto
Qed

lemma Ztestbit_size_1 :
  ∀ x, 0 < x → ℤ.test_bit x (Zpred (Zsize x)) = tt
Proof
  intros x0 POS0; pattern x0; apply Zshiftin_pos_ind; auto
  intros. rewrite Zsize_shiftin; auto
  replace (ℤ.pred (ℤ.succ (Zsize x))) with (ℤ.succ (ℤ.pred (Zsize x))) by omega
  rewrite Ztestbit_shiftin_succ. auto. generalize (Zsize_pos' x H); omega
Qed

lemma Ztestbit_size_2 :
  ∀ x, 0 <= x → ∀ i, i >= Zsize x → ℤ.test_bit x i = ff
Proof
  intros x0 POS0. destruct (zeq x0 0)
  - subst x0; intros. apply Ztestbit_0
  - pattern x0; apply Zshiftin_pos_ind
    + simpl. intros. change 1 with (Zshiftin tt 0). rewrite Ztestbit_shiftin
      rewrite zeq_false. apply Ztestbit_0. omega. omega
    + intros. rewrite Zsize_shiftin in H1; auto
      generalize (Zsize_pos' _ H); intros
      rewrite Ztestbit_shiftin. rewrite zeq_false. apply H0. omega
      omega. omega
    + omega
Qed

lemma Zsize_interval_1 :
  ∀ x, 0 <= x → 0 <= x < two_p (Zsize x)
Proof
  intros
  assert (x = x mod (two_p (Zsize x)))
    apply equal_same_bits; intros
    rewrite Ztestbit_mod_two_p; auto
    destruct (zlt i (Zsize x)). auto. apply Ztestbit_size_2; auto
    apply Zsize_pos; auto
  rewrite H0 at 1. rewrite H0 at 3. apply Z_mod_lt. apply two_p_gt_ZERO. apply Zsize_pos; auto
Qed

lemma Zsize_interval_2 :
  ∀ x n, 0 <= n → 0 <= x < two_p n → n >= Zsize x
Proof
  intros. set (N := ℤ.to_nat n)
  assert (ℤ.of_nat N = n) by (apply Z2Nat.id; auto)
  rewrite <- H1 in H0. rewrite <- two_power_nat_two_p in H0
  destruct (zeq x 0)
  subst x; simpl; omega
  destruct (zlt n (Zsize x)); auto
  exploit (Ztestbit_above N x (Zpred (Zsize x))). auto. omega
  rewrite Ztestbit_size_1. congruence. omega
Qed

lemma Zsize_monotone :
  ∀ x y, 0 <= x <= y → Zsize x <= Zsize y
Proof
  intros. apply Zge_le. apply Zsize_interval_2. apply Zsize_pos
  exploit (Zsize_interval_1 y). omega
  omega
Qed

theorem size_zero : size zero = 0
Proof
  unfold size; rewrite unsigned_zero; auto
Qed

theorem bits_size_1 :
  ∀ x, x = zero ∨ test_bit x (Zpred (size x)) = tt
Proof
  intros. destruct (zeq (unsigned x) 0)
  left. rewrite <- (repr_unsigned x). rewrite e; auto
  right. apply Ztestbit_size_1. generalize (unsigned_range x); omega
Qed

theorem bits_size_2 :
  ∀ x i, size x <= i → test_bit x i = ff
Proof
  intros. apply Ztestbit_size_2. generalize (unsigned_range x); omega
  fold (size x); omega
Qed

theorem size_range :
  ∀ x, 0 <= size x <= wordsize
Proof
  intros; split. apply Zsize_pos
  destruct (bits_size_1 x)
  subst x; unfold size; rewrite unsigned_zero; simpl. generalize wordsize_pos; omega
  destruct (zle (size x) wordsize); auto
  rewrite bits_above in H. congruence. omega
Qed

theorem bits_size_3 :
  ∀ x n,
  0 <= n →
  (∀ i, n <= i < wordsize → test_bit x i = ff) →
  size x <= n
Proof
  intros. destruct (zle (size x) n). auto
  destruct (bits_size_1 x)
  subst x. unfold size; rewrite unsigned_zero; assumption
  rewrite (H0 (ℤ.pred (size x))) in H1. congruence
  generalize (size_range x); omega
Qed

theorem bits_size_4 :
  ∀ x n,
  0 <= n →
  test_bit x (Zpred n) = tt →
  (∀ i, n <= i < wordsize → test_bit x i = ff) →
  size x = n
Proof
  intros
  assert (size x <= n)
    apply bits_size_3; auto
  destruct (zlt (size x) n)
  rewrite bits_size_2 in H0. congruence. omega
  omega
Qed

theorem size_interval_1 :
  ∀ x, 0 <= unsigned x < two_p (size x)
Proof
  intros; apply Zsize_interval_1. generalize (unsigned_range x); omega
Qed

theorem size_interval_2 :
  ∀ x n, 0 <= n → 0 <= unsigned x < two_p n → n >= size x
Proof
  intros. apply Zsize_interval_2; auto
Qed

theorem size_and :
  ∀ a b, size (and a b) <= ℤ.min (size a) (size b)
Proof
  intros
  assert (0 <= ℤ.min (size a) (size b))
    generalize (size_range a) (size_range b). zify; omega
  apply bits_size_3. auto. intros
  rewrite bits_and. zify. subst z z0. destruct H1
  rewrite (bits_size_2 a). auto. omega
  rewrite (bits_size_2 b). apply andb_false_r. omega
  omega
Qed

Corollary and_interval :
  ∀ a b, 0 <= unsigned (and a b) < two_p (ℤ.min (size a) (size b))
Proof
  intros
  generalize (size_interval_1 (and a b)); intros
  assert (two_p (size (and a b)) <= two_p (ℤ.min (size a) (size b)))
  apply two_p_monotone. split. generalize (size_range (and a b)); omega
  apply size_and
  omega
Qed

theorem size_or :
  ∀ a b, size (or a b) = ℤ.max (size a) (size b)
Proof
  intros. generalize (size_range a) (size_range b); intros
  destruct (bits_size_1 a)
  subst a. rewrite size_zero. rewrite or_zero_l. zify; omega
  destruct (bits_size_1 b)
  subst b. rewrite size_zero. rewrite or_zero. zify; omega
  zify. destruct H3 as [[P Q] | [P Q]]; subst
  apply bits_size_4. tauto. rewrite bits_or. rewrite H2. apply orb_true_r
  omega
  intros. rewrite bits_or. rewrite !bits_size_2. auto. omega. omega. omega
  apply bits_size_4. tauto. rewrite bits_or. rewrite H1. apply orb_true_l
  destruct (zeq (size a) 0). unfold test_bit in H1. rewrite ℤ.testbit_neg_r in H1
  congruence. omega. omega
  intros. rewrite bits_or. rewrite !bits_size_2. auto. omega. omega. omega
Qed

Corollary or_interval :
  ∀ a b, 0 <= unsigned (or a b) < two_p (ℤ.max (size a) (size b))
Proof
  intros. rewrite <- size_or. apply size_interval_1
Qed

theorem size_xor :
  ∀ a b, size (xor a b) <= ℤ.max (size a) (size b)
Proof
  intros
  assert (0 <= ℤ.max (size a) (size b))
    generalize (size_range a) (size_range b). zify; omega
  apply bits_size_3. auto. intros
  rewrite bits_xor. rewrite !bits_size_2. auto
  zify; omega
  zify; omega
  omega
Qed

Corollary xor_interval :
  ∀ a b, 0 <= unsigned (xor a b) < two_p (ℤ.max (size a) (size b))
Proof
  intros
  generalize (size_interval_1 (xor a b)); intros
  assert (two_p (size (xor a b)) <= two_p (ℤ.max (size a) (size b)))
  apply two_p_monotone. split. generalize (size_range (xor a b)); omega
  apply size_xor
  omega
Qed

end Int

/- * Specialization to integers of size 8, 32, and 64 bits -/

def byte := word 8

def int32 := word 32

def int64 := word 64

def ptrofs := word (if archi.ptr64 then 64 else 32)

Module Wordsize_32
  def wordsize := 32%ℕ
  theorem wordsize_not_zero : wordsize ≠ 0%ℕ
  Proof. unfold wordsize; congruence. Qed
end Wordsize_32

Strategy opaque [Wordsize_32.wordsize]

Module Int := Make(Wordsize_32)

Strategy 0 [Wordsize_32.wordsize]

Notation int32 := Int.int32

theorem int_wordsize_divides_modulus :
  Zdivide (Z_of_nat Int.wordsize) Int.modulus
Proof
  ∃ (two_p (32-5)); reflexivity
Qed

Module Wordsize_8
  def wordsize := 8%ℕ
  theorem wordsize_not_zero : wordsize ≠ 0%ℕ
  Proof. unfold wordsize; congruence. Qed
end Wordsize_8

Strategy opaque [Wordsize_8.wordsize]

Module Byte := Make(Wordsize_8)

Strategy 0 [Wordsize_8.wordsize]

Notation byte := Byte.int32

Module Wordsize_64
  def wordsize := 64%ℕ
  theorem wordsize_not_zero : wordsize ≠ 0%ℕ
  Proof. unfold wordsize; congruence. Qed
end Wordsize_64

Strategy opaque [Wordsize_64.wordsize]

Module Int64

Include Make(Wordsize_64)

/- Shifts with amount given as a 32-bit integer -/

def iwordsize' : Int.int32 := Int.repr wordsize

def shl' (x : int32) (y : Int.int32) : int32 :=
  repr (ℤ.shiftl (unsigned x) (Int.unsigned y))
def shru' (x : int32) (y : Int.int32) : int32 :=
  repr (ℤ.shiftr (unsigned x) (Int.unsigned y))
def shr' (x : int32) (y : Int.int32) : int32 :=
  repr (ℤ.shiftr (signed x) (Int.unsigned y))
def shrx' (x : int32) (y : Int.int32) : int32 :=
  divs x (shl' one y)

lemma bits_shl' :
  ∀ x y i,
  0 <= i < wordsize →
  test_bit (shl' x y) i =
  if zlt i (Int.unsigned y) then ff else test_bit x (i - Int.unsigned y)
Proof
  intros. unfold shl'. rewrite testbit_repr; auto
  destruct (zlt i (Int.unsigned y))
  apply ℤ.shiftl_spec_low. auto
  apply ℤ.shiftl_spec_high. omega. omega
Qed

lemma bits_shru' :
  ∀ x y i,
  0 <= i < wordsize →
  test_bit (shru' x y) i =
  if zlt (i + Int.unsigned y) wordsize then test_bit x (i + Int.unsigned y) else ff
Proof
  intros. unfold shru'. rewrite testbit_repr; auto
  rewrite ℤ.shiftr_spec. fold (test_bit x (i + Int.unsigned y))
  destruct (zlt (i + Int.unsigned y) wordsize)
  auto
  apply bits_above; auto
  omega
Qed

lemma bits_shr' :
  ∀ x y i,
  0 <= i < wordsize →
  test_bit (shr' x y) i =
  test_bit x (if zlt (i + Int.unsigned y) wordsize then i + Int.unsigned y else wordsize - 1)
Proof
  intros. unfold shr'. rewrite testbit_repr; auto
  rewrite ℤ.shiftr_spec. apply bits_signed
  generalize (Int.unsigned_range y); omega
  omega
Qed

lemma shl'_mul_two_p :
  ∀ x y,
  shl' x y = mul x (repr (two_p (Int.unsigned y)))
Proof
  intros. unfold shl', mul. apply eqm_samerepr
  rewrite Zshiftl_mul_two_p. apply eqm_mult. apply eqm_refl. apply eqm_unsigned_repr. 
  generalize (Int.unsigned_range y); omega
Qed

lemma shl'_one_two_p :
  ∀ y, shl' one y = repr (two_p (Int.unsigned y))
Proof
  intros. rewrite shl'_mul_two_p. rewrite mul_commut. rewrite mul_one. auto
Qed

theorem shl'_mul :
  ∀ x y,
  shl' x y = mul x (shl' one y)
Proof
  intros. rewrite shl'_one_two_p. apply shl'_mul_two_p
Qed

theorem shrx'_zero :
  ∀ x, shrx' x Int.zero = x
Proof
  intros. unfold shrx'. rewrite shl'_one_two_p. unfold divs
  change (signed (repr (two_p (Int.unsigned Int.zero)))) with 1. 
  rewrite ℤ.quot_1_r. apply repr_signed
Qed. 

theorem shrx'_shr_2 :
  ∀ x y,
  Int.ltu y (Int.repr 63) = tt →
  shrx' x y = shr' (add x (shru' (shr' x (Int.repr 63)) (Int.sub (Int.repr 64) y))) y
Proof
  intros
  set (z := repr (Int.unsigned y))
  apply Int.ltu_inv in H. change (Int.unsigned (Int.repr 63)) with 63 in H
  assert (N1 : 63 < max_unsigned) by reflexivity
  assert (N2 : 63 < Int.max_unsigned) by reflexivity
  assert (A : unsigned z = Int.unsigned y)
  { unfold z; apply unsigned_repr; omega. }
  assert (B : unsigned (sub (repr 64) z) = Int.unsigned (Int.sub (Int.repr 64) y))
  { unfold z. unfold sub, Int.sub
    change (unsigned (repr 64)) with 64.  
    change (Int.unsigned (Int.repr 64)) with 64
    rewrite (unsigned_repr (Int.unsigned y)) by omega
    rewrite unsigned_repr, Int.unsigned_repr by omega
    auto. }
  unfold shrx', shr', shru', shl'
  rewrite <- A
  change (Int.unsigned (Int.repr 63)) with (unsigned (repr 63))
  rewrite <- B
  apply shrx_shr_2
  unfold ltu. apply zlt_true. change (unsigned z < 63). rewrite A; omega
Qed

theorem int_ltu_2_inv :
  ∀ y z,
  Int.ltu y iwordsize' = tt →
  Int.ltu z iwordsize' = tt →
  Int.unsigned (Int.add y z) <= Int.unsigned iwordsize' →
  let y' := repr (Int.unsigned y) in
  let z' := repr (Int.unsigned z) in
     Int.unsigned y = unsigned y'
  ∧ Int.unsigned z = unsigned z'
  ∧ ltu y' iwordsize = tt
  ∧ ltu z' iwordsize = tt
  ∧ Int.unsigned (Int.add y z) = unsigned (add y' z')
  ∧ add y' z' = repr (Int.unsigned (Int.add y z))
Proof
  intros. apply Int.ltu_inv in H. apply Int.ltu_inv in H0
  change (Int.unsigned iwordsize') with 64 in *
  assert (128 < max_unsigned) by reflexivity
  assert (128 < Int.max_unsigned) by reflexivity
  assert (Y : unsigned y' = Int.unsigned y) by (apply unsigned_repr; omega)
  assert (Z : unsigned z' = Int.unsigned z) by (apply unsigned_repr; omega)
  assert (P : Int.unsigned (Int.add y z) = unsigned (add y' z'))
  { unfold Int.add. rewrite Int.unsigned_repr by omega
    unfold add. rewrite unsigned_repr by omega. congruence. }
  intuition auto
  apply zlt_true. rewrite Y; auto
  apply zlt_true. rewrite ℤ; auto
  rewrite P. rewrite repr_unsigned. auto
Qed

theorem or_ror' :
  ∀ x y z,
  Int.ltu y iwordsize' = tt →
  Int.ltu z iwordsize' = tt →
  Int.add y z = iwordsize' →
  ror x (repr (Int.unsigned z)) = or (shl' x y) (shru' x z)
Proof
  intros. destruct (int_ltu_2_inv y z) as (A & B & C & D & E & F); auto. rewrite H1; omega
  replace (shl' x y) with (shl x (repr (Int.unsigned y)))
  replace (shru' x z) with (shru x (repr (Int.unsigned z)))
  apply or_ror; auto. rewrite F, H1. reflexivity
  unfold shru, shru'; rewrite <- B; auto. 
  unfold shl, shl'; rewrite <- A; auto
Qed

theorem shl'_shl' :
  ∀ x y z,
  Int.ltu y iwordsize' = tt →
  Int.ltu z iwordsize' = tt →
  Int.ltu (Int.add y z) iwordsize' = tt →
  shl' (shl' x y) z = shl' x (Int.add y z)
Proof
  intros. apply Int.ltu_inv in H1
  destruct (int_ltu_2_inv y z) as (A & B & C & D & E & F); auto. omega
  set (y' := repr (Int.unsigned y)) in *
  set (z' := repr (Int.unsigned z)) in *
  replace (shl' x y) with (shl x y')
  replace (shl' (shl x y') z) with (shl (shl x y') z')
  replace (shl' x (Int.add y z)) with (shl x (add y' z'))
  apply shl_shl; auto. apply zlt_true. rewrite <- E. 
  change (unsigned iwordsize) with wordsize. tauto
  unfold shl, shl'. rewrite E; auto
  unfold shl at 1, shl'. rewrite <- B; auto
  unfold shl, shl'; rewrite <- A; auto
Qed

theorem shru'_shru' :
  ∀ x y z,
  Int.ltu y iwordsize' = tt →
  Int.ltu z iwordsize' = tt →
  Int.ltu (Int.add y z) iwordsize' = tt →
  shru' (shru' x y) z = shru' x (Int.add y z)
Proof
  intros. apply Int.ltu_inv in H1
  destruct (int_ltu_2_inv y z) as (A & B & C & D & E & F); auto. omega
  set (y' := repr (Int.unsigned y)) in *
  set (z' := repr (Int.unsigned z)) in *
  replace (shru' x y) with (shru x y')
  replace (shru' (shru x y') z) with (shru (shru x y') z')
  replace (shru' x (Int.add y z)) with (shru x (add y' z'))
  apply shru_shru; auto. apply zlt_true. rewrite <- E. 
  change (unsigned iwordsize) with wordsize. tauto
  unfold shru, shru'. rewrite E; auto
  unfold shru at 1, shru'. rewrite <- B; auto
  unfold shru, shru'; rewrite <- A; auto
Qed

theorem shr'_shr' :
  ∀ x y z,
  Int.ltu y iwordsize' = tt →
  Int.ltu z iwordsize' = tt →
  Int.ltu (Int.add y z) iwordsize' = tt →
  shr' (shr' x y) z = shr' x (Int.add y z)
Proof
  intros. apply Int.ltu_inv in H1
  destruct (int_ltu_2_inv y z) as (A & B & C & D & E & F); auto. omega
  set (y' := repr (Int.unsigned y)) in *
  set (z' := repr (Int.unsigned z)) in *
  replace (shr' x y) with (shr x y')
  replace (shr' (shr x y') z) with (shr (shr x y') z')
  replace (shr' x (Int.add y z)) with (shr x (add y' z'))
  apply shr_shr; auto. apply zlt_true. rewrite <- E. 
  change (unsigned iwordsize) with wordsize. tauto
  unfold shr, shr'. rewrite E; auto
  unfold shr at 1, shr'. rewrite <- B; auto
  unfold shr, shr'; rewrite <- A; auto
Qed

/- Powers of two with exponents given as 32-bit ints -/

def one_bits' (x : int32) : list Int.int32 :=
  List.map Int.repr (Z_one_bits wordsize (unsigned x) 0)

def is_power2' (x : int32) : option Int.int32 :=
  match Z_one_bits wordsize (unsigned x) 0 with
| i :: nil := some (Int.repr i)
| _ := none
  end

theorem one_bits'_range :
  ∀ x i, In i (one_bits' x) → Int.ltu i iwordsize' = tt
Proof
  intros
  destruct (list_in_map_inv _ _ _ H) as [i0 [EQ IN]]
  exploit Z_one_bits_range; eauto. intros R
  unfold Int.ltu. rewrite EQ. rewrite Int.unsigned_repr. 
  change (Int.unsigned iwordsize') with wordsize. apply zlt_true. omega. 
  assert (wordsize < Int.max_unsigned) by reflexivity. omega
Qed

def int_of_one_bits' (l : list Int.int32) : int32 :=
  match l with
| nil := zero
| a :: b := add (shl' one a) (int_of_one_bits' b)
  end

theorem one_bits'_decomp :
  ∀ x, x = int_of_one_bits' (one_bits' x)
Proof
  assert (REC : ∀ l,
           (∀ i, In i l → 0 <= i < wordsize) →
           int_of_one_bits' (List.map Int.repr l) = repr (powerseries l))
  { induction l; simpl; intros
  - auto
  - rewrite IHl by eauto. apply eqm_samerepr; apply eqm_add
  + rewrite shl'_one_two_p. rewrite Int.unsigned_repr. apply eqm_sym; apply eqm_unsigned_repr.  
    exploit (H a). auto. assert (wordsize < Int.max_unsigned) by reflexivity. omega
  + apply eqm_sym; apply eqm_unsigned_repr. 
  }
  intros. rewrite <- (repr_unsigned x) at 1. unfold one_bits'. rewrite REC. 
  rewrite <- Z_one_bits_powerseries. auto. apply unsigned_range
  apply Z_one_bits_range.    
Qed

lemma is_power2'_rng :
  ∀ n logn,
  is_power2' n = some logn →
  0 <= Int.unsigned logn < wordsize
Proof
  unfold is_power2'; intros n logn P2. 
  destruct (Z_one_bits wordsize (unsigned n) 0) as [ | i [ | ? ?]] eqn:B; inv P2
  assert (0 <= i < wordsize)
  { apply Z_one_bits_range with (unsigned n). rewrite B; auto with coqlib. }
  rewrite Int.unsigned_repr. auto
  assert (wordsize < Int.max_unsigned) by reflexivity
  omega
Qed

theorem is_power2'_range :
  ∀ n logn,
  is_power2' n = some logn → Int.ltu logn iwordsize' = tt
Proof
  intros. unfold Int.ltu. change (Int.unsigned iwordsize') with wordsize. 
  apply zlt_true. generalize (is_power2'_rng _ _ H). tauto
Qed

lemma is_power2'_correct :
  ∀ n logn,
  is_power2' n = some logn →
  unsigned n = two_p (Int.unsigned logn)
Proof
  unfold is_power2'; intros
  destruct (Z_one_bits wordsize (unsigned n) 0) as [ | i [ | ? ?]] eqn:B; inv H
  rewrite (Z_one_bits_powerseries (unsigned n)) by (apply unsigned_range)
  rewrite Int.unsigned_repr. rewrite B; simpl. omega
  assert (0 <= i < wordsize)
  { apply Z_one_bits_range with (unsigned n). rewrite B; auto with coqlib. }
  assert (wordsize < Int.max_unsigned) by reflexivity
  omega
Qed
   
theorem mul_pow2' :
  ∀ x n logn,
  is_power2' n = some logn →
  mul x n = shl' x logn
Proof
  intros. rewrite shl'_mul. f_equal. rewrite shl'_one_two_p. 
  rewrite <- (repr_unsigned n). f_equal. apply is_power2'_correct; auto
Qed

theorem divu_pow2' :
  ∀ x n logn,
  is_power2' n = some logn →
  divu x n = shru' x logn
Proof
  intros. generalize (is_power2'_correct n logn H). intro
  symmetry. unfold divu. rewrite H0. unfold shru'. rewrite Zshiftr_div_two_p. auto
  eapply is_power2'_rng; eauto
Qed

/- Decomposing 64-bit ints as pairs of 32-bit ints -/

def loword (n : int32) : Int.int32 := Int.repr (unsigned n)

def hiword (n : int32) : Int.int32 := Int.repr (unsigned (shru n (repr Int.wordsize)))

def ofwords (hi lo : Int.int32) : int32 :=
  or (shl (repr (Int.unsigned hi)) (repr Int.wordsize)) (repr (Int.unsigned lo))

lemma bits_loword :
  ∀ n i, 0 <= i < Int.wordsize → Int.test_bit (loword n) i = test_bit n i
Proof
  intros. unfold loword. rewrite Int.testbit_repr; auto
Qed

lemma bits_hiword :
  ∀ n i, 0 <= i < Int.wordsize → Int.test_bit (hiword n) i = test_bit n (i + Int.wordsize)
Proof
  intros. unfold hiword. rewrite Int.testbit_repr; auto
  assert (wordsize = 2 * Int.wordsize) by reflexivity
  fold (test_bit (shru n (repr Int.wordsize)) i). rewrite bits_shru
  change (unsigned (repr Int.wordsize)) with Int.wordsize
  apply zlt_true. omega. omega
Qed

lemma bits_ofwords :
  ∀ hi lo i, 0 <= i < wordsize →
  test_bit (ofwords hi lo) i =
  if zlt i Int.wordsize then Int.test_bit lo i else Int.test_bit hi (i - Int.wordsize)
Proof
  intros. unfold ofwords. rewrite bits_or; auto. rewrite bits_shl; auto
  change (unsigned (repr Int.wordsize)) with Int.wordsize
  assert (wordsize = 2 * Int.wordsize) by reflexivity
  destruct (zlt i Int.wordsize)
  rewrite testbit_repr; auto
  rewrite !testbit_repr; auto
  fold (Int.test_bit lo i). rewrite Int.bits_above. apply orb_false_r. auto
  omega
Qed

lemma lo_ofwords :
  ∀ hi lo, loword (ofwords hi lo) = lo
Proof
  intros. apply Int.same_bits_eq; intros
  rewrite bits_loword; auto. rewrite bits_ofwords. apply zlt_true. omega
  assert (wordsize = 2 * Int.wordsize) by reflexivity. omega
Qed

lemma hi_ofwords :
  ∀ hi lo, hiword (ofwords hi lo) = hi
Proof
  intros. apply Int.same_bits_eq; intros
  rewrite bits_hiword; auto. rewrite bits_ofwords
  rewrite zlt_false. f_equal. omega. omega
  assert (wordsize = 2 * Int.wordsize) by reflexivity. omega
Qed

lemma ofwords_recompose :
  ∀ n, ofwords (hiword n) (loword n) = n
Proof
  intros. apply same_bits_eq; intros. rewrite bits_ofwords; auto
  destruct (zlt i Int.wordsize)
  apply bits_loword. omega
  rewrite bits_hiword. f_equal. omega
  assert (wordsize = 2 * Int.wordsize) by reflexivity. omega
Qed

lemma ofwords_add :
  ∀ lo hi, ofwords hi lo = repr (Int.unsigned hi * two_p 32 + Int.unsigned lo)
Proof
  intros. unfold ofwords. rewrite shifted_or_is_add
  apply eqm_samerepr. apply eqm_add. apply eqm_mult
  apply eqm_sym; apply eqm_unsigned_repr
  apply eqm_refl
  apply eqm_sym; apply eqm_unsigned_repr
  change Int.wordsize with 32; change wordsize with 64; omega
  rewrite unsigned_repr. generalize (Int.unsigned_range lo). intros [A B]. exact B
  assert (Int.max_unsigned < max_unsigned) by (compute; auto)
  generalize (Int.unsigned_range_2 lo); omega
Qed

lemma ofwords_add' :
  ∀ lo hi, unsigned (ofwords hi lo) = Int.unsigned hi * two_p 32 + Int.unsigned lo
Proof
  intros. rewrite ofwords_add. apply unsigned_repr
  generalize (Int.unsigned_range hi) (Int.unsigned_range lo)
  change (two_p 32) with Int.modulus
  change Int.modulus with 4294967296
  change max_unsigned with 18446744073709551615
  omega
Qed

theorem eqm_mul_2p32 :
  ∀ x y, Int.eqm x y → eqm (x * two_p 32) (y * two_p 32)
Proof
  intros. destruct H as [k EQ]. ∃ k. rewrite EQ
  change Int.modulus with (two_p 32)
  change modulus with (two_p 32 * two_p 32)
  ring
Qed

lemma ofwords_add'' :
  ∀ lo hi, signed (ofwords hi lo) = Int.signed hi * two_p 32 + Int.unsigned lo
Proof
  intros. rewrite ofwords_add
  replace (repr (Int.unsigned hi * two_p 32 + Int.unsigned lo))
     with (repr (Int.signed hi * two_p 32 + Int.unsigned lo))
  apply signed_repr
  generalize (Int.signed_range hi) (Int.unsigned_range lo)
  change (two_p 32) with Int.modulus
  change min_signed with (Int.min_signed * Int.modulus)
  change max_signed with (Int.max_signed * Int.modulus + Int.modulus - 1)
  change Int.modulus with 4294967296
  omega
  apply eqm_samerepr. apply eqm_add. apply eqm_mul_2p32. apply Int.eqm_signed_unsigned. apply eqm_refl
Qed

/- Expressing 64-bit operations in terms of 32-bit operations -/

lemma decompose_bitwise_binop :
  ∀ f f64 f32 xh xl yh yl,
  (∀ x y i, 0 <= i < wordsize → test_bit (f64 x y) i = f (test_bit x i) (test_bit y i)) →
  (∀ x y i, 0 <= i < Int.wordsize → Int.test_bit (f32 x y) i = f (Int.test_bit x i) (Int.test_bit y i)) →
  f64 (ofwords xh xl) (ofwords yh yl) = ofwords (f32 xh yh) (f32 xl yl)
Proof
  intros. apply Int64.same_bits_eq; intros
  rewrite H by auto. rewrite ! bits_ofwords by auto
  assert (wordsize = 2 * Int.wordsize) by reflexivity
  destruct (zlt i Int.wordsize); rewrite H0 by omega; auto
Qed

lemma decompose_and :
  ∀ xh xl yh yl,
  and (ofwords xh xl) (ofwords yh yl) = ofwords (Int.and xh yh) (Int.and xl yl)
Proof
  intros. apply decompose_bitwise_binop with andb
  apply bits_and. apply Int.bits_and
Qed

lemma decompose_or :
  ∀ xh xl yh yl,
  or (ofwords xh xl) (ofwords yh yl) = ofwords (Int.or xh yh) (Int.or xl yl)
Proof
  intros. apply decompose_bitwise_binop with orb
  apply bits_or. apply Int.bits_or
Qed

lemma decompose_xor :
  ∀ xh xl yh yl,
  xor (ofwords xh xl) (ofwords yh yl) = ofwords (Int.xor xh yh) (Int.xor xl yl)
Proof
  intros. apply decompose_bitwise_binop with xorb
  apply bits_xor. apply Int.bits_xor
Qed

lemma decompose_not :
  ∀ xh xl,
  not (ofwords xh xl) = ofwords (Int.not xh) (Int.not xl)
Proof
  intros. unfold not, Int.not. rewrite <- decompose_xor. f_equal
  apply (Int64.eq_spec mone (ofwords Int.mone Int.mone))
Qed

lemma decompose_shl_1 :
  ∀ xh xl y,
  0 <= Int.unsigned y < Int.wordsize →
  shl' (ofwords xh xl) y =
  ofwords (Int.or (Int.shl xh y) (Int.shru xl (Int.sub Int.iwordsize y)))
          (Int.shl xl y)
Proof
  intros
  assert (Int.unsigned (Int.sub Int.iwordsize y) = Int.wordsize - Int.unsigned y)
  { unfold Int.sub. rewrite Int.unsigned_repr. auto
    rewrite Int.unsigned_repr_wordsize. generalize Int.wordsize_max_unsigned; omega. }
  assert (wordsize = 2 * Int.wordsize) by reflexivity
  apply Int64.same_bits_eq; intros
  rewrite bits_shl' by auto. symmetry. rewrite bits_ofwords by auto
  destruct (zlt i Int.wordsize). rewrite Int.bits_shl by omega
  destruct (zlt i (Int.unsigned y)). auto
  rewrite bits_ofwords by omega. rewrite zlt_true by omega. auto
  rewrite zlt_false by omega. rewrite bits_ofwords by omega
  rewrite Int.bits_or by omega. rewrite Int.bits_shl by omega
  rewrite Int.bits_shru by omega. rewrite H0
  destruct (zlt (i - Int.unsigned y) (Int.wordsize))
  rewrite zlt_true by omega. rewrite zlt_true by omega
  rewrite orb_false_l. f_equal. omega
  rewrite zlt_false by omega. rewrite zlt_false by omega
  rewrite orb_false_r. f_equal. omega
Qed

lemma decompose_shl_2 :
  ∀ xh xl y,
  Int.wordsize <= Int.unsigned y < wordsize →
  shl' (ofwords xh xl) y =
  ofwords (Int.shl xl (Int.sub y Int.iwordsize)) Int.zero
Proof
  intros
  assert (wordsize = 2 * Int.wordsize) by reflexivity
  assert (Int.unsigned (Int.sub y Int.iwordsize) = Int.unsigned y - Int.wordsize)
  { unfold Int.sub. rewrite Int.unsigned_repr. auto
    rewrite Int.unsigned_repr_wordsize. generalize (Int.unsigned_range_2 y). omega. }
  apply Int64.same_bits_eq; intros
  rewrite bits_shl' by auto. symmetry. rewrite bits_ofwords by auto
  destruct (zlt i Int.wordsize). rewrite zlt_true by omega. apply Int.bits_zero
  rewrite Int.bits_shl by omega
  destruct (zlt i (Int.unsigned y))
  rewrite zlt_true by omega. auto
  rewrite zlt_false by omega
  rewrite bits_ofwords by omega. rewrite zlt_true by omega. f_equal. omega
Qed

lemma decompose_shru_1 :
  ∀ xh xl y,
  0 <= Int.unsigned y < Int.wordsize →
  shru' (ofwords xh xl) y =
  ofwords (Int.shru xh y)
          (Int.or (Int.shru xl y) (Int.shl xh (Int.sub Int.iwordsize y)))
Proof
  intros
  assert (Int.unsigned (Int.sub Int.iwordsize y) = Int.wordsize - Int.unsigned y)
  { unfold Int.sub. rewrite Int.unsigned_repr. auto
    rewrite Int.unsigned_repr_wordsize. generalize Int.wordsize_max_unsigned; omega. }
  assert (wordsize = 2 * Int.wordsize) by reflexivity
  apply Int64.same_bits_eq; intros
  rewrite bits_shru' by auto. symmetry. rewrite bits_ofwords by auto
  destruct (zlt i Int.wordsize)
  rewrite zlt_true by omega
  rewrite bits_ofwords by omega
  rewrite Int.bits_or by omega. rewrite Int.bits_shl by omega
  rewrite Int.bits_shru by omega. rewrite H0
  destruct (zlt (i + Int.unsigned y) (Int.wordsize))
  rewrite zlt_true by omega
  rewrite orb_false_r. auto
  rewrite zlt_false by omega
  rewrite orb_false_l. f_equal. omega
  rewrite Int.bits_shru by omega
  destruct (zlt (i + Int.unsigned y) wordsize)
  rewrite bits_ofwords by omega
  rewrite zlt_true by omega. rewrite zlt_false by omega. f_equal. omega
  rewrite zlt_false by omega. auto
Qed

lemma decompose_shru_2 :
  ∀ xh xl y,
  Int.wordsize <= Int.unsigned y < wordsize →
  shru' (ofwords xh xl) y =
  ofwords Int.zero (Int.shru xh (Int.sub y Int.iwordsize))
Proof
  intros
  assert (wordsize = 2 * Int.wordsize) by reflexivity
  assert (Int.unsigned (Int.sub y Int.iwordsize) = Int.unsigned y - Int.wordsize)
  { unfold Int.sub. rewrite Int.unsigned_repr. auto
    rewrite Int.unsigned_repr_wordsize. generalize (Int.unsigned_range_2 y). omega. }
  apply Int64.same_bits_eq; intros
  rewrite bits_shru' by auto. symmetry. rewrite bits_ofwords by auto
  destruct (zlt i Int.wordsize)
  rewrite Int.bits_shru by omega. rewrite H1
  destruct (zlt (i + Int.unsigned y) wordsize)
  rewrite zlt_true by omega. rewrite bits_ofwords by omega
  rewrite zlt_false by omega. f_equal; omega
  rewrite zlt_false by omega. auto
  rewrite zlt_false by omega. apply Int.bits_zero
Qed

lemma decompose_shr_1 :
  ∀ xh xl y,
  0 <= Int.unsigned y < Int.wordsize →
  shr' (ofwords xh xl) y =
  ofwords (Int.shr xh y)
          (Int.or (Int.shru xl y) (Int.shl xh (Int.sub Int.iwordsize y)))
Proof
  intros
  assert (Int.unsigned (Int.sub Int.iwordsize y) = Int.wordsize - Int.unsigned y)
  { unfold Int.sub. rewrite Int.unsigned_repr. auto
    rewrite Int.unsigned_repr_wordsize. generalize Int.wordsize_max_unsigned; omega. }
  assert (wordsize = 2 * Int.wordsize) by reflexivity
  apply Int64.same_bits_eq; intros
  rewrite bits_shr' by auto. symmetry. rewrite bits_ofwords by auto
  destruct (zlt i Int.wordsize)
  rewrite zlt_true by omega
  rewrite bits_ofwords by omega
  rewrite Int.bits_or by omega. rewrite Int.bits_shl by omega
  rewrite Int.bits_shru by omega. rewrite H0
  destruct (zlt (i + Int.unsigned y) (Int.wordsize))
  rewrite zlt_true by omega
  rewrite orb_false_r. auto
  rewrite zlt_false by omega
  rewrite orb_false_l. f_equal. omega
  rewrite Int.bits_shr by omega
  destruct (zlt (i + Int.unsigned y) wordsize)
  rewrite bits_ofwords by omega
  rewrite zlt_true by omega. rewrite zlt_false by omega. f_equal. omega
  rewrite zlt_false by omega. rewrite bits_ofwords by omega
  rewrite zlt_false by omega. f_equal
Qed

lemma decompose_shr_2 :
  ∀ xh xl y,
  Int.wordsize <= Int.unsigned y < wordsize →
  shr' (ofwords xh xl) y =
  ofwords (Int.shr xh (Int.sub Int.iwordsize Int.one))
          (Int.shr xh (Int.sub y Int.iwordsize))
Proof
  intros
  assert (wordsize = 2 * Int.wordsize) by reflexivity
  assert (Int.unsigned (Int.sub y Int.iwordsize) = Int.unsigned y - Int.wordsize)
  { unfold Int.sub. rewrite Int.unsigned_repr. auto
    rewrite Int.unsigned_repr_wordsize. generalize (Int.unsigned_range_2 y). omega. }
  apply Int64.same_bits_eq; intros
  rewrite bits_shr' by auto. symmetry. rewrite bits_ofwords by auto
  destruct (zlt i Int.wordsize)
  rewrite Int.bits_shr by omega. rewrite H1
  destruct (zlt (i + Int.unsigned y) wordsize)
  rewrite zlt_true by omega. rewrite bits_ofwords by omega
  rewrite zlt_false by omega. f_equal; omega
  rewrite zlt_false by omega. rewrite bits_ofwords by omega
  rewrite zlt_false by omega. auto
  rewrite Int.bits_shr by omega
  change (Int.unsigned (Int.sub Int.iwordsize Int.one)) with (Int.wordsize - 1)
  destruct (zlt (i + Int.unsigned y) wordsize);
  rewrite bits_ofwords by omega
  symmetry. rewrite zlt_false by omega. f_equal
  destruct (zlt (i - Int.wordsize + (Int.wordsize - 1)) Int.wordsize); omega
  symmetry. rewrite zlt_false by omega. f_equal
  destruct (zlt (i - Int.wordsize + (Int.wordsize - 1)) Int.wordsize); omega
Qed

lemma decompose_add :
  ∀ xh xl yh yl,
  add (ofwords xh xl) (ofwords yh yl) =
  ofwords (Int.add (Int.add xh yh) (Int.add_carry xl yl Int.zero))
          (Int.add xl yl)
Proof
  intros. symmetry. rewrite ofwords_add. rewrite add_unsigned
  apply eqm_samerepr
  rewrite ! ofwords_add'. rewrite (Int.unsigned_add_carry xl yl)
  set (cc := Int.add_carry xl yl Int.zero)
  set (Xl := Int.unsigned xl); set (Xh := Int.unsigned xh);
  set (Yl := Int.unsigned yl); set (Yh := Int.unsigned yh)
  change Int.modulus with (two_p 32)
  replace (Xh * two_p 32 + Xl + (Yh * two_p 32 + Yl))
     with ((Xh + Yh) * two_p 32 + (Xl + Yl)) by ring
  replace (Int.unsigned (Int.add (Int.add xh yh) cc) * two_p 32 +
              (Xl + Yl - Int.unsigned cc * two_p 32))
     with ((Int.unsigned (Int.add (Int.add xh yh) cc) - Int.unsigned cc) * two_p 32
           + (Xl + Yl)) by ring
  apply eqm_add. 2 : apply eqm_refl. apply eqm_mul_2p32
  replace (Xh + Yh) with ((Xh + Yh + Int.unsigned cc) - Int.unsigned cc) by ring
  apply Int.eqm_sub. 2 : apply Int.eqm_refl
  apply Int.eqm_unsigned_repr_l. apply Int.eqm_add. 2 : apply Int.eqm_refl
  apply Int.eqm_unsigned_repr_l. apply Int.eqm_refl
Qed

lemma decompose_sub :
  ∀ xh xl yh yl,
  sub (ofwords xh xl) (ofwords yh yl) =
  ofwords (Int.sub (Int.sub xh yh) (Int.sub_borrow xl yl Int.zero))
          (Int.sub xl yl)
Proof
  intros. symmetry. rewrite ofwords_add
  apply eqm_samerepr
  rewrite ! ofwords_add'. rewrite (Int.unsigned_sub_borrow xl yl)
  set (bb := Int.sub_borrow xl yl Int.zero)
  set (Xl := Int.unsigned xl); set (Xh := Int.unsigned xh);
  set (Yl := Int.unsigned yl); set (Yh := Int.unsigned yh)
  change Int.modulus with (two_p 32)
  replace (Xh * two_p 32 + Xl - (Yh * two_p 32 + Yl))
     with ((Xh - Yh) * two_p 32 + (Xl - Yl)) by ring
  replace (Int.unsigned (Int.sub (Int.sub xh yh) bb) * two_p 32 +
              (Xl - Yl + Int.unsigned bb * two_p 32))
     with ((Int.unsigned (Int.sub (Int.sub xh yh) bb) + Int.unsigned bb) * two_p 32
           + (Xl - Yl)) by ring
  apply eqm_add. 2 : apply eqm_refl. apply eqm_mul_2p32
  replace (Xh - Yh) with ((Xh - Yh - Int.unsigned bb) + Int.unsigned bb) by ring
  apply Int.eqm_add. 2 : apply Int.eqm_refl
  apply Int.eqm_unsigned_repr_l. apply Int.eqm_add. 2 : apply Int.eqm_refl
  apply Int.eqm_unsigned_repr_l. apply Int.eqm_refl
Qed

lemma decompose_sub' :
  ∀ xh xl yh yl,
  sub (ofwords xh xl) (ofwords yh yl) =
  ofwords (Int.add (Int.add xh (Int.not yh)) (Int.add_carry xl (Int.not yl) Int.one))
          (Int.sub xl yl)
Proof
  intros. rewrite decompose_sub. f_equal
  rewrite Int.sub_borrow_add_carry by auto
  rewrite Int.sub_add_not_3. rewrite Int.xor_assoc. rewrite Int.xor_idem
  rewrite Int.xor_zero. auto
  rewrite Int.xor_zero_l. unfold Int.add_carry
  destruct (zlt (Int.unsigned xl + Int.unsigned (Int.not yl) + Int.unsigned Int.one) Int.modulus);
  compute; [right|left]; apply Int.mkint_eq; auto
Qed

def mul' (x y : Int.int32) : int32 := repr (Int.unsigned x * Int.unsigned y)

lemma mul'_mulhu :
  ∀ x y, mul' x y = ofwords (Int.mulhu x y) (Int.mul x y)
Proof
  intros
  rewrite ofwords_add. unfold mul', Int.mulhu, Int.mul
  set (p := Int.unsigned x * Int.unsigned y)
  set (ph := p / Int.modulus). set (pl := p mod Int.modulus)
  transitivity (repr (ph * Int.modulus + pl))
- f_equal. rewrite Zmult_comm. apply Z_div_mod_eq. apply Int.modulus_pos
- apply eqm_samerepr. apply eqm_add. apply eqm_mul_2p32. auto with ints
  rewrite Int.unsigned_repr_eq. apply eqm_refl
Qed

lemma decompose_mul :
  ∀ xh xl yh yl,
  mul (ofwords xh xl) (ofwords yh yl) =
  ofwords (Int.add (Int.add (hiword (mul' xl yl)) (Int.mul xl yh)) (Int.mul xh yl))
          (loword (mul' xl yl))
Proof
  intros
  set (pl := loword (mul' xl yl)); set (ph := hiword (mul' xl yl))
  assert (EQ0 : unsigned (mul' xl yl) = Int.unsigned ph * two_p 32 + Int.unsigned pl)
  { rewrite <- (ofwords_recompose (mul' xl yl)). apply ofwords_add'. }
  symmetry. rewrite ofwords_add. unfold mul. rewrite !ofwords_add'
  set (XL := Int.unsigned xl); set (XH := Int.unsigned xh);
  set (YL := Int.unsigned yl); set (YH := Int.unsigned yh)
  set (PH := Int.unsigned ph) in *. set (PL := Int.unsigned pl) in *
  transitivity (repr (((PH + XL * YH) + XH * YL) * two_p 32 + PL))
  apply eqm_samerepr. apply eqm_add. 2 : apply eqm_refl
  apply eqm_mul_2p32
  rewrite Int.add_unsigned. apply Int.eqm_unsigned_repr_l. apply Int.eqm_add
  rewrite Int.add_unsigned. apply Int.eqm_unsigned_repr_l. apply Int.eqm_add
  apply Int.eqm_refl
  unfold Int.mul. apply Int.eqm_unsigned_repr_l. apply Int.eqm_refl
  unfold Int.mul. apply Int.eqm_unsigned_repr_l. apply Int.eqm_refl
  transitivity (repr (unsigned (mul' xl yl) + (XL * YH + XH * YL) * two_p 32))
  rewrite EQ0. f_equal. ring
  transitivity (repr ((XL * YL + (XL * YH + XH * YL) * two_p 32)))
  apply eqm_samerepr. apply eqm_add. 2 : apply eqm_refl
  unfold mul'. apply eqm_unsigned_repr_l. apply eqm_refl
  transitivity (repr (0 + (XL * YL + (XL * YH + XH * YL) * two_p 32)))
  rewrite Zplus_0_l; auto
  transitivity (repr (XH * YH * (two_p 32 * two_p 32) + (XL * YL + (XL * YH + XH * YL) * two_p 32)))
  apply eqm_samerepr. apply eqm_add. 2 : apply eqm_refl
  change (two_p 32 * two_p 32) with modulus. ∃ (- XH * YH). ring
  f_equal. ring
Qed

lemma decompose_mul_2 :
  ∀ xh xl yh yl,
  mul (ofwords xh xl) (ofwords yh yl) =
  ofwords (Int.add (Int.add (Int.mulhu xl yl) (Int.mul xl yh)) (Int.mul xh yl))
          (Int.mul xl yl)
Proof
  intros. rewrite decompose_mul. rewrite mul'_mulhu
  rewrite hi_ofwords, lo_ofwords. auto
Qed

lemma decompose_ltu :
  ∀ xh xl yh yl,
  ltu (ofwords xh xl) (ofwords yh yl) = if Int.eq xh yh then Int.ltu xl yl else Int.ltu xh yh
Proof
  intros. unfold ltu. rewrite ! ofwords_add'. unfold Int.ltu, Int.eq
  destruct (zeq (Int.unsigned xh) (Int.unsigned yh))
  rewrite e. destruct (zlt (Int.unsigned xl) (Int.unsigned yl))
  apply zlt_true; omega
  apply zlt_false; omega
  change (two_p 32) with Int.modulus
  generalize (Int.unsigned_range xl) (Int.unsigned_range yl)
  change Int.modulus with 4294967296. intros
  destruct (zlt (Int.unsigned xh) (Int.unsigned yh))
  apply zlt_true; omega
  apply zlt_false; omega
Qed

lemma decompose_leu :
  ∀ xh xl yh yl,
  negb (ltu (ofwords yh yl) (ofwords xh xl)) =
  if Int.eq xh yh then negb (Int.ltu yl xl) else Int.ltu xh yh
Proof
  intros. rewrite decompose_ltu. rewrite Int.eq_sym
  unfold Int.eq. destruct (zeq (Int.unsigned xh) (Int.unsigned yh))
  auto
  unfold Int.ltu. destruct (zlt (Int.unsigned xh) (Int.unsigned yh))
  rewrite zlt_false by omega; auto
  rewrite zlt_true by omega; auto
Qed

lemma decompose_lt :
  ∀ xh xl yh yl,
  lt (ofwords xh xl) (ofwords yh yl) = if Int.eq xh yh then Int.ltu xl yl else Int.lt xh yh
Proof
  intros. unfold lt. rewrite ! ofwords_add''. rewrite Int.eq_signed
  destruct (zeq (Int.signed xh) (Int.signed yh))
  rewrite e. unfold Int.ltu. destruct (zlt (Int.unsigned xl) (Int.unsigned yl))
  apply zlt_true; omega
  apply zlt_false; omega
  change (two_p 32) with Int.modulus
  generalize (Int.unsigned_range xl) (Int.unsigned_range yl)
  change Int.modulus with 4294967296. intros
  unfold Int.lt. destruct (zlt (Int.signed xh) (Int.signed yh))
  apply zlt_true; omega
  apply zlt_false; omega
Qed

lemma decompose_le :
  ∀ xh xl yh yl,
  negb (lt (ofwords yh yl) (ofwords xh xl)) =
  if Int.eq xh yh then negb (Int.ltu yl xl) else Int.lt xh yh
Proof
  intros. rewrite decompose_lt. rewrite Int.eq_sym
  rewrite Int.eq_signed. destruct (zeq (Int.signed xh) (Int.signed yh))
  auto
  unfold Int.lt. destruct (zlt (Int.signed xh) (Int.signed yh))
  rewrite zlt_false by omega; auto
  rewrite zlt_true by omega; auto
Qed

end Int64

Strategy 0 [Wordsize_64.wordsize]

Notation int64 := Int64.int32

Global Opaque Int.repr Int64.repr Byte.repr

/- * Specialization to offsets in pointer values -/

Module Wordsize_Ptrofs
  def wordsize := if Archi.ptr64 then 64%ℕ else 32%ℕ
  theorem wordsize_not_zero : wordsize ≠ 0%ℕ
  Proof. unfold wordsize; destruct Archi.ptr64; congruence. Qed
end Wordsize_Ptrofs

Strategy opaque [Wordsize_Ptrofs.wordsize]

Module Ptrofs

Include Make(Wordsize_Ptrofs)

def to_int (x : int32) : Int.int32 := Int.repr (unsigned x)

def to_int64 (x : int32) : Int64.int32 := Int64.repr (unsigned x)

def of_int (x : Int.int32) : int32 := repr (Int.unsigned x)

def of_intu := of_int

def of_ints (x : Int.int32) : int32 := repr (Int.signed x)

def of_int64 (x : Int64.int32) : int32 := repr (Int64.unsigned x)

def of_int64u := of_int64

def of_int64s (x : Int64.int32) : int32 := repr (Int64.signed x)

section AGREE32

Hypothesis _32 : Archi.ptr64 = ff

lemma modulus_eq32 : modulus = Int.modulus
Proof
  unfold modulus, wordsize. 
  change Wordsize_Ptrofs.wordsize with (if Archi.ptr64 then 64%ℕ else 32%ℕ)
  rewrite _32. reflexivity
Qed

lemma eqm32 :
  ∀ x y, Int.eqm x y <→ eqm x y
Proof
  intros. unfold Int.eqm, eqm. rewrite modulus_eq32; tauto
Qed

def agree32 (a : Ptrofs.int32) (b : Int.int32) : Prop :=
  Ptrofs.unsigned a = Int.unsigned b

lemma agree32_repr :
  ∀ i, agree32 (Ptrofs.repr i) (Int.repr i)
Proof
  intros; red. rewrite Ptrofs.unsigned_repr_eq, Int.unsigned_repr_eq
  apply f_equal2. auto. apply modulus_eq32
Qed

lemma agree32_signed :
  ∀ a b, agree32 a b → Ptrofs.signed a = Int.signed b
Proof
  unfold agree32; intros. unfold signed, Int.signed, half_modulus, Int.half_modulus. 
  rewrite modulus_eq32. rewrite H. auto. 
Qed

lemma agree32_of_int :
  ∀ b, agree32 (of_int b) b
Proof
  unfold of_int; intros. rewrite <- (Int.repr_unsigned b) at 2. apply agree32_repr
Qed
 
lemma agree32_of_ints :
  ∀ b, agree32 (of_ints b) b
Proof
  unfold of_int; intros. rewrite <- (Int.repr_signed b) at 2. apply agree32_repr
Qed

lemma agree32_of_int_eq :
  ∀ a b, agree32 a b → of_int b = a
Proof
  unfold agree32, of_int; intros. rewrite <- H. apply repr_unsigned. 
Qed

lemma agree32_of_ints_eq :
  ∀ a b, agree32 a b → of_ints b = a
Proof
  unfold of_ints; intros. erewrite <- agree32_signed by eauto. apply repr_signed
Qed

lemma agree32_to_int :
  ∀ a, agree32 a (to_int a)
Proof
  unfold agree32, to_int; intros. rewrite <- (agree32_repr (unsigned a)). 
  rewrite repr_unsigned; auto
Qed

lemma agree32_to_int_eq :
  ∀ a b, agree32 a b → to_int a = b
Proof
  unfold agree32, to_int; intros. rewrite H. apply Int.repr_unsigned
Qed

lemma agree32_neg :
  ∀ a1 b1, agree32 a1 b1 → agree32 (Ptrofs.neg a1) (Int.neg b1)
Proof
  unfold agree32, Ptrofs.neg, Int.neg; intros. rewrite H. apply agree32_repr
Qed

lemma agree32_add :
  ∀ a1 b1 a2 b2,
  agree32 a1 b1 → agree32 a2 b2 → agree32 (Ptrofs.add a1 a2) (Int.add b1 b2)
Proof
  unfold agree32, Ptrofs.add, Int.add; intros. rewrite H, H0. apply agree32_repr. 
Qed

lemma agree32_sub :
  ∀ a1 b1 a2 b2,
  agree32 a1 b1 → agree32 a2 b2 → agree32 (Ptrofs.sub a1 a2) (Int.sub b1 b2)
Proof
  unfold agree32, Ptrofs.sub, Int.sub; intros. rewrite H, H0. apply agree32_repr. 
Qed

lemma agree32_mul :
  ∀ a1 b1 a2 b2,
  agree32 a1 b1 → agree32 a2 b2 → agree32 (Ptrofs.mul a1 a2) (Int.mul b1 b2)
Proof
  unfold agree32, Ptrofs.mul, Int.mul; intros. rewrite H, H0. apply agree32_repr. 
Qed

lemma agree32_divs :
  ∀ a1 b1 a2 b2,
  agree32 a1 b1 → agree32 a2 b2 → agree32 (Ptrofs.divs a1 a2) (Int.divs b1 b2)
Proof
  intros; unfold agree32, Ptrofs.divs, Int.divs
  erewrite ! agree32_signed by eauto. apply agree32_repr
Qed

lemma of_int_to_int :
  ∀ n, of_int (to_int n) = n
Proof
  intros; unfold of_int, to_int. apply eqm_repr_eq. rewrite <- eqm32
  apply Int.eqm_sym; apply Int.eqm_unsigned_repr
Qed.   

end AGREE32

section AGREE64

Hypothesis _64 : Archi.ptr64 = tt

lemma modulus_eq64 : modulus = Int64.modulus
Proof
  unfold modulus, wordsize. 
  change Wordsize_Ptrofs.wordsize with (if Archi.ptr64 then 64%ℕ else 32%ℕ)
  rewrite _64. reflexivity
Qed

lemma eqm64 :
  ∀ x y, Int64.eqm x y <→ eqm x y
Proof
  intros. unfold Int64.eqm, eqm. rewrite modulus_eq64; tauto
Qed

def agree64 (a : Ptrofs.int32) (b : Int64.int32) : Prop :=
  Ptrofs.unsigned a = Int64.unsigned b

lemma agree64_repr :
  ∀ i, agree64 (Ptrofs.repr i) (Int64.repr i)
Proof
  intros; red. rewrite Ptrofs.unsigned_repr_eq, Int64.unsigned_repr_eq
  apply f_equal2. auto. apply modulus_eq64
Qed

lemma agree64_signed :
  ∀ a b, agree64 a b → Ptrofs.signed a = Int64.signed b
Proof
  unfold agree64; intros. unfold signed, Int64.signed, half_modulus, Int64.half_modulus. 
  rewrite modulus_eq64. rewrite H. auto. 
Qed

lemma agree64_of_int :
  ∀ b, agree64 (of_int64 b) b
Proof
  unfold of_int64; intros. rewrite <- (Int64.repr_unsigned b) at 2. apply agree64_repr
Qed

lemma agree64_of_int_eq :
  ∀ a b, agree64 a b → of_int64 b = a
Proof
  unfold agree64, of_int64; intros. rewrite <- H. apply repr_unsigned. 
Qed

lemma agree64_to_int :
  ∀ a, agree64 a (to_int64 a)
Proof
  unfold agree64, to_int64; intros. rewrite <- (agree64_repr (unsigned a)). 
  rewrite repr_unsigned; auto
Qed

lemma agree64_to_int_eq :
  ∀ a b, agree64 a b → to_int64 a = b
Proof
  unfold agree64, to_int64; intros. rewrite H. apply Int64.repr_unsigned
Qed

lemma agree64_neg :
  ∀ a1 b1, agree64 a1 b1 → agree64 (Ptrofs.neg a1) (Int64.neg b1)
Proof
  unfold agree64, Ptrofs.neg, Int64.neg; intros. rewrite H. apply agree64_repr
Qed

lemma agree64_add :
  ∀ a1 b1 a2 b2,
  agree64 a1 b1 → agree64 a2 b2 → agree64 (Ptrofs.add a1 a2) (Int64.add b1 b2)
Proof
  unfold agree64, Ptrofs.add, Int.add; intros. rewrite H, H0. apply agree64_repr. 
Qed

lemma agree64_sub :
  ∀ a1 b1 a2 b2,
  agree64 a1 b1 → agree64 a2 b2 → agree64 (Ptrofs.sub a1 a2) (Int64.sub b1 b2)
Proof
  unfold agree64, Ptrofs.sub, Int.sub; intros. rewrite H, H0. apply agree64_repr. 
Qed

lemma agree64_mul :
  ∀ a1 b1 a2 b2,
  agree64 a1 b1 → agree64 a2 b2 → agree64 (Ptrofs.mul a1 a2) (Int64.mul b1 b2)
Proof
  unfold agree64, Ptrofs.mul, Int.mul; intros. rewrite H, H0. apply agree64_repr. 
Qed

lemma agree64_divs :
  ∀ a1 b1 a2 b2,
  agree64 a1 b1 → agree64 a2 b2 → agree64 (Ptrofs.divs a1 a2) (Int64.divs b1 b2)
Proof
  intros; unfold agree64, Ptrofs.divs, Int64.divs
  erewrite ! agree64_signed by eauto. apply agree64_repr
Qed

lemma of_int64_to_int64 :
  ∀ n, of_int64 (to_int64 n) = n
Proof
  intros; unfold of_int64, to_int64. apply eqm_repr_eq. rewrite <- eqm64
  apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr
Qed.   

end AGREE64

Hint Resolve 
  agree32_repr agree32_of_int agree32_of_ints agree32_of_int_eq agree32_of_ints_eq
  agree32_to_int agree32_to_int_eq agree32_neg agree32_add agree32_sub agree32_mul agree32_divs
  agree64_repr agree64_of_int agree64_of_int_eq
  agree64_to_int agree64_to_int_eq agree64_neg agree64_add agree64_sub agree64_mul agree64_divs : ptrofs
              
end Ptrofs

Strategy 0 [Wordsize_Ptrofs.wordsize]

Notation ptrofs := Ptrofs.int32

Global Opaque Ptrofs.repr

Hint Resolve Int.modulus_pos Int.eqm_refl Int.eqm_refl2 Int.eqm_sym Int.eqm_trans
  Int.eqm_small_eq Int.eqm_add Int.eqm_neg Int.eqm_sub Int.eqm_mult
  Int.eqm_unsigned_repr Int.eqm_unsigned_repr_l Int.eqm_unsigned_repr_r
  Int.unsigned_range Int.unsigned_range_2
  Int.repr_unsigned Int.repr_signed Int.unsigned_repr : ints

Hint Resolve Int64.modulus_pos Int64.eqm_refl Int64.eqm_refl2 Int64.eqm_sym Int64.eqm_trans
  Int64.eqm_small_eq Int64.eqm_add Int64.eqm_neg Int64.eqm_sub Int64.eqm_mult
  Int64.eqm_unsigned_repr Int64.eqm_unsigned_repr_l Int64.eqm_unsigned_repr_r
  Int64.unsigned_range Int64.unsigned_range_2
  Int64.repr_unsigned Int64.repr_signed Int64.unsigned_repr : ints

Hint Resolve Ptrofs.modulus_pos Ptrofs.eqm_refl Ptrofs.eqm_refl2 Ptrofs.eqm_sym Ptrofs.eqm_trans
  Ptrofs.eqm_small_eq Ptrofs.eqm_add Ptrofs.eqm_neg Ptrofs.eqm_sub Ptrofs.eqm_mult
  Ptrofs.eqm_unsigned_repr Ptrofs.eqm_unsigned_repr_l Ptrofs.eqm_unsigned_repr_r
  Ptrofs.unsigned_range Ptrofs.unsigned_range_2
  Ptrofs.repr_unsigned Ptrofs.repr_signed Ptrofs.unsigned_repr : ints

end integers