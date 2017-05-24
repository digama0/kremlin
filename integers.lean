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
instance coe_int_Int : has_coe ℤ Int := ⟨repr⟩

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

instance Int.comm_ring : comm_ring Int :=
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

instance Int.decidable_linear_order : decidable_linear_order Int :=
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

lemma ltu_not (x y) : ltu y x ↔ ¬ltu x y ∧ x ≠ y := sorry

/- Non-overlapping test -/

def no_overlap (ofs1 : Int) (sz1 : ℕ) (ofs2 : Int) (sz2 : ℕ) : bool :=
let x1 := unsigned ofs1, x2 := unsigned ofs2 in
x1 + sz1 < modulus ∧ x2 + sz2 < modulus ∧ (x1 + sz1 ≤ x2 ∨ x2 + sz2 ≤ x1)

instance (ofs1 sz1 ofs2 sz2) : decidable (no_overlap ofs1 sz1 ofs2 sz2) :=
by apply_instance

lemma no_overlap_sound (ofs1 sz1 ofs2 sz2 base) :
  sz1 > 0 → sz2 > 0 → no_overlap ofs1 sz1 ofs2 sz2 →
  unsigned (base + ofs1) + sz1 ≤ unsigned (base + ofs2)
  ∨ unsigned (base + ofs2) + sz2 ≤ unsigned (base + ofs1) := sorry

/- Size of integers, in bits. -/

def size (x : Int) : ℕ := nat.size (unsigned x)

theorem size_zero : size 0 = 0 := congr_arg nat.size unsigned_zero

theorem test_bit_size (x) : x > 0 → test_bit x (size x - 1) := sorry

theorem test_bit_size_lt (x i) : test_bit x i → i < size x := sorry

theorem size_le_wordsize (x) : size x ≤ wordsize := sorry

theorem bits_size_le (x n) (h : ∀ i < wordsize, test_bit x i → i < n) : size x ≤ n := sorry

theorem bits_size_eq (x n) : test_bit x (n - 1) →
  (∀ i < wordsize, test_bit x i → i < n) → size x = n := sorry

theorem lt_pow_size (x) : unsigned x < 2^size x := nat.lt_pow_size _

theorem size_le_of_lt_pow (x n) : unsigned x < 2^n → size x ≤ n := nat.size_le_of_lt_pow

theorem size_and (a b) : size (Int.and a b) ≤ min (size a) (size b) := sorry

theorem and_interval (a b) : unsigned (Int.and a b) < 2^ min (size a) (size b) := sorry

theorem size_or (a b) : size (Int.or a b) = max (size a) (size b) := sorry

theorem or_interval (a b) : unsigned (Int.or a b) < 2^ max (size a) (size b) := sorry

theorem size_xor (a b) : size (Int.xor a b) ≤ max (size a) (size b) := sorry

theorem xor_interval (a b) : unsigned (Int.xor a b) < 2^ max (size a) (size b) := sorry

theorem wordsize_dvd_modulus (n) : wordsize = 2^n → wordsize ∣ modulus := sorry

end Int

def scoe {w w'} (x : @Int w) : @Int w' := repr (signed x)
def ucoe {w w'} (x : @Int w) : @Int w' := repr (unsigned x)

/- * Specialization to integers of size 8, 32, and 64 bits -/

def W8 : ℕ+ := ⟨8, dec_trivial⟩
def W32 : ℕ+ := ⟨32, dec_trivial⟩
def W64 : ℕ+ := ⟨64, dec_trivial⟩
def ptrofs.wordsize : ℕ+ := if archi.ptr64 then W64 else W32

def byte := @Int W8
def int32 := @Int W32
def int64 := @Int W64
def ptrofs := @Int ptrofs.wordsize

theorem byte.wordsize_dvd_modulus :
  @wordsize W8 ∣ @modulus W8 :=
wordsize_dvd_modulus 3 rfl

theorem int32.wordsize_dvd_modulus :
  @wordsize W32 ∣ @modulus W32 :=
wordsize_dvd_modulus 5 rfl

theorem int64.wordsize_dvd_modulus :
  @wordsize W64 ∣ @modulus W64 :=
wordsize_dvd_modulus 6 rfl

theorem ptrofs.wordsize_dvd_modulus :
  @wordsize ptrofs.wordsize ∣ @modulus ptrofs.wordsize :=
wordsize_dvd_modulus (if archi.ptr64 then 6 else 5)
  (by delta wordsize ptrofs.wordsize; cases archi.ptr64; refl)

instance byte.comm_ring   : comm_ring byte   := Int.comm_ring
instance int32.comm_ring  : comm_ring int32  := Int.comm_ring
instance int64.comm_ring  : comm_ring int64  := Int.comm_ring
instance ptrofs.comm_ring : comm_ring ptrofs := Int.comm_ring
instance byte.decidable_linear_order   : decidable_linear_order byte   := Int.decidable_linear_order
instance int32.decidable_linear_order  : decidable_linear_order int32  := Int.decidable_linear_order
instance int64.decidable_linear_order  : decidable_linear_order int64  := Int.decidable_linear_order
instance ptrofs.decidable_linear_order : decidable_linear_order ptrofs := Int.decidable_linear_order

namespace int64

def is_power2 (x : int64) : option int32 :=
ucoe <$> is_power2 x

lemma is_power2_rng (n logn) : is_power2 n = some logn → unsigned logn < 64 := sorry

theorem is_power2_range (n logn) : is_power2 n = some logn → Int.ltu logn 32 := sorry

lemma is_power2_correct (n logn) : is_power2 n = some logn →
  unsigned n = 2^unsigned logn := sorry
   
theorem mul_pow2 (x n logn) : is_power2 n = some logn →
  x * n = Int.shl x (ucoe logn) := sorry

theorem divu_pow2 (x n logn) : is_power2 n = some logn →
  Int.divu x n = Int.shru x (ucoe logn) := sorry

/- Decomposing 64-bit ints as pairs of 32-bit ints -/

def loword (n : int64) : int32 := ucoe n

def hiword (n : int64) : int32 := ucoe (Int.shru n 32)

def ofwords (hi lo : int32) : int64 := Int.or (Int.shl (ucoe hi) 32) (ucoe lo)

lemma bits_loword (n i) : i < 32 → test_bit (loword n) i = test_bit n i := sorry

lemma bits_hiword (n i) : i < 32 → test_bit (hiword n) i = test_bit n (i + 32) := sorry

lemma bits_ofwords (hi lo i) :
  test_bit (ofwords hi lo) i = if i < 32 then test_bit lo i else test_bit hi (i - 32) := sorry

lemma lo_ofwords (hi lo) : loword (ofwords hi lo) = lo := sorry

lemma hi_ofwords (hi lo) : hiword (ofwords hi lo) = hi := sorry

lemma ofwords_recompose (n) : ofwords (hiword n) (loword n) = n := sorry

lemma ofwords_add (lo hi) : ofwords hi lo = repr (unsigned hi * 2^32 + unsigned lo) := sorry

lemma ofwords_add' (lo hi) : unsigned (ofwords hi lo) = unsigned hi * 2^32 + unsigned lo := sorry

lemma ofwords_add'' (lo hi) : signed (ofwords hi lo) = signed hi * 2^32 + unsigned lo := sorry

/- Expressing 64-bit operations in terms of 32-bit operations -/

lemma decompose_bitwise_binop {f : ∀ {w}, @Int w → @Int w → @Int w} {f' : bool → bool → bool} :
  (∀ {w} (x y : @Int w) (i : ℕ), i < @wordsize w → test_bit (f x y) i = f' (test_bit x i) (test_bit y i)) →
  ∀ xh xl yh yl, f (ofwords xh xl) (ofwords yh yl) = ofwords (f xh yh) (f xl yl) := sorry

lemma decompose_and : ∀ xh xl yh yl,
  Int.and (ofwords xh xl) (ofwords yh yl) = ofwords (Int.and xh yh) (Int.and xl yl) :=
decompose_bitwise_binop @bits_and

lemma decompose_or : ∀ xh xl yh yl,
  Int.or (ofwords xh xl) (ofwords yh yl) = ofwords (Int.or xh yh) (Int.or xl yl) :=
decompose_bitwise_binop @bits_or

lemma decompose_xor : ∀ xh xl yh yl,
  Int.xor (ofwords xh xl) (ofwords yh yl) = ofwords (Int.xor xh yh) (Int.xor xl yl) :=
decompose_bitwise_binop @bits_xor

lemma decompose_not (xh xl) : Int.not (ofwords xh xl) = ofwords (Int.not xh) (Int.not xl) := sorry

lemma decompose_shl_1 (xh xl y) : unsigned y < 32 → Int.shl (ofwords xh xl) (ucoe y) =
  ofwords (Int.or (Int.shl xh y) (Int.shru xl (32 - y))) (Int.shl xl y) := sorry

lemma decompose_shl_2 (xh xl y) : 32 ≤ unsigned y → unsigned y < 64 →
  Int.shl (ofwords xh xl) (ucoe y) = ofwords (Int.shl xl (y - 32)) 0 := sorry

lemma decompose_shru_1 (xh xl y) : unsigned y < 32 → Int.shru (ofwords xh xl) (ucoe y) =
  ofwords (Int.shru xh y) (Int.or (Int.shru xl y) (Int.shl xh (32 - y))) := sorry

lemma decompose_shru_2 (xh xl y) : 32 ≤ unsigned y → unsigned y < 64 →
  Int.shru (ofwords xh xl) (ucoe y) = ofwords 0 (Int.shru xh (y - 32)) := sorry

lemma decompose_shr_1 (xh xl y) : unsigned y < 32 → Int.shr (ofwords xh xl) (ucoe y) =
  ofwords (Int.shr xh y) (Int.or (Int.shru xl y) (Int.shl xh (32 - y))) := sorry

lemma decompose_shr_2 (xh xl y) : 32 ≤ unsigned y → unsigned y < 64 →
  Int.shr (ofwords xh xl) (ucoe y) = ofwords (Int.shr xh (32 - 1)) (Int.shr xh (y - 32)) := sorry

lemma decompose_add (xh xl yh yl) : ofwords xh xl + ofwords yh yl =
  ofwords (xh + yh + (add_carry xl yl 0)) (xl + yl) := sorry

lemma decompose_sub (xh xl yh yl) : ofwords xh xl - ofwords yh yl =
  ofwords (xh - yh - sub_borrow xl yl 0) (xl - yl) := sorry

lemma decompose_sub' (xh xl yh yl) : ofwords xh xl - ofwords yh yl =
  ofwords (xh + Int.not yh + add_carry xl (Int.not yl) 1) (xl - yl) := sorry

lemma mul_mulhu (x y) : ucoe x * ucoe y = ofwords (Int.mulhu x y) (x * y) := sorry

lemma decompose_mul (xh xl yh yl) : ofwords xh xl * ofwords yh yl =
  ofwords (Int.mulhu xl yl + xl * yh + xh * yl) (xl * yl) := sorry

lemma decompose_ltu (xh xl yh yl) :
  Int.ltu (ofwords xh xl) (ofwords yh yl) ↔ if xh = yh then Int.ltu xl yl else Int.ltu xh yh := sorry

lemma decompose_leu (xh xl yh yl) : ¬Int.ltu (ofwords yh yl) (ofwords xh xl) ↔
  if xh = yh then ¬Int.ltu yl xl else Int.ltu xh yh := sorry

lemma decompose_lt (xh xl yh yl) :
  ofwords xh xl < ofwords yh yl ↔ if xh = yh then xl < yl else xh < yh := sorry

lemma decompose_le (xh xl yh yl) : ofwords xh xl ≤ ofwords yh yl ↔
  if xh = yh then xl ≤ yl else xh < yh := sorry

end int64

/- * Specialization to offsets in pointer values -/

namespace ptrofs

def to_int (x : ptrofs) : int32 := ucoe x

def to_int64 (x : ptrofs) : int64 := ucoe x

def of_int (x : int32) : ptrofs := ucoe x

def of_intu := of_int

def of_ints (x : int32) : ptrofs := scoe x

def of_int64 (x : int64) : ptrofs := ucoe x

def of_int64u := of_int64

def of_int64s (x : int64) : ptrofs := scoe x
              
end ptrofs

end integers