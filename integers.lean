import .archi .lib .word

namespace integers
open word

/- * Specialization to integers of size 8, 32, and 64 bits -/

def W8 : ℕ+ := ⟨8, dec_trivial⟩
def W32 : ℕ+ := ⟨32, dec_trivial⟩
def W64 : ℕ+ := ⟨64, dec_trivial⟩
def ptrofs.wordsize : ℕ+ := if archi.ptr64 then W64 else W32

def byte := word W8
def int32 := word W32
def int64 := word W64
def ptrofs := word ptrofs.wordsize

theorem byte.wordsize_dvd_modulus : wordsize W8 ∣ modulus W8 :=
wordsize_dvd_modulus 3 rfl

theorem int32.wordsize_dvd_modulus : wordsize W32 ∣ modulus W32 :=
wordsize_dvd_modulus 5 rfl

theorem int64.wordsize_dvd_modulus : wordsize W64 ∣ modulus W64 :=
wordsize_dvd_modulus 6 rfl

theorem ptrofs.wordsize_dvd_modulus :
  wordsize ptrofs.wordsize ∣ modulus ptrofs.wordsize :=
wordsize_dvd_modulus (if archi.ptr64 then 6 else 5)
  (by delta wordsize ptrofs.wordsize; cases archi.ptr64; refl)

instance byte.comm_ring   : comm_ring byte   := word.comm_ring
instance int32.comm_ring  : comm_ring int32  := word.comm_ring
instance int64.comm_ring  : comm_ring int64  := word.comm_ring
instance ptrofs.comm_ring : comm_ring ptrofs := word.comm_ring
instance byte.decidable_linear_order   : decidable_linear_order byte   := word.decidable_linear_order
instance int32.decidable_linear_order  : decidable_linear_order int32  := word.decidable_linear_order
instance int64.decidable_linear_order  : decidable_linear_order int64  := word.decidable_linear_order
instance ptrofs.decidable_linear_order : decidable_linear_order ptrofs := word.decidable_linear_order

namespace int64

def is_power2 (x : int64) : option int32 :=
ucoe <$> is_power2 x

lemma is_power2_rng (n logn) : is_power2 n = some logn → unsigned logn < 64 := sorry

theorem is_power2_range (n logn) : is_power2 n = some logn → ltu logn 32 := sorry

lemma is_power2_correct (n logn) : is_power2 n = some logn →
  unsigned n = 2^unsigned logn := sorry
   
theorem mul_pow2 (x n logn) : is_power2 n = some logn →
  x * n = shl x (ucoe logn) := sorry

theorem divu_pow2 (x n logn) : is_power2 n = some logn →
  divu x n = shru x (ucoe logn) := sorry

/- Decomposing 64-bit ints as pairs of 32-bit ints -/

def loword (n : int64) : int32 := ucoe n

def hiword (n : int64) : int32 := ucoe (shru n 32)

def ofwords (hi lo : int32) : int64 := word.or (shl (ucoe hi) 32) (ucoe lo)

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

lemma decompose_bitwise_binop {f : ∀ {w}, word w → word w → word w} {f' : bool → bool → bool} :
  (∀ {w} (x y : word w) (i : ℕ), i < wordsize w → test_bit (f x y) i = f' (test_bit x i) (test_bit y i)) →
  ∀ xh xl yh yl, f (ofwords xh xl) (ofwords yh yl) = ofwords (f xh yh) (f xl yl) := sorry

lemma decompose_and : ∀ xh xl yh yl,
  word.and (ofwords xh xl) (ofwords yh yl) = ofwords (word.and xh yh) (word.and xl yl) :=
decompose_bitwise_binop @bits_and

lemma decompose_or : ∀ xh xl yh yl,
  word.or (ofwords xh xl) (ofwords yh yl) = ofwords (word.or xh yh) (word.or xl yl) :=
decompose_bitwise_binop @bits_or

lemma decompose_xor : ∀ xh xl yh yl,
  word.xor (ofwords xh xl) (ofwords yh yl) = ofwords (word.xor xh yh) (word.xor xl yl) :=
decompose_bitwise_binop @bits_xor

lemma decompose_not (xh xl) : word.not (ofwords xh xl) = ofwords (word.not xh) (word.not xl) := sorry

lemma decompose_shl_1 (xh xl y) : unsigned y < 32 → shl (ofwords xh xl) (ucoe y) =
  ofwords (word.or (shl xh y) (shru xl (32 - y))) (shl xl y) := sorry

lemma decompose_shl_2 (xh xl y) : 32 ≤ unsigned y → unsigned y < 64 →
  shl (ofwords xh xl) (ucoe y) = ofwords (shl xl (y - 32)) 0 := sorry

lemma decompose_shru_1 (xh xl y) : unsigned y < 32 → shru (ofwords xh xl) (ucoe y) =
  ofwords (shru xh y) (word.or (shru xl y) (shl xh (32 - y))) := sorry

lemma decompose_shru_2 (xh xl y) : 32 ≤ unsigned y → unsigned y < 64 →
  shru (ofwords xh xl) (ucoe y) = ofwords 0 (shru xh (y - 32)) := sorry

lemma decompose_shr_1 (xh xl y) : unsigned y < 32 → shr (ofwords xh xl) (ucoe y) =
  ofwords (shr xh y) (word.or (shru xl y) (shl xh (32 - y))) := sorry

lemma decompose_shr_2 (xh xl y) : 32 ≤ unsigned y → unsigned y < 64 →
  shr (ofwords xh xl) (ucoe y) = ofwords (shr xh (32 - 1)) (shr xh (y - 32)) := sorry

lemma decompose_add (xh xl yh yl) : ofwords xh xl + ofwords yh yl =
  ofwords (xh + yh + (add_carry xl yl 0)) (xl + yl) := sorry

lemma decompose_sub (xh xl yh yl) : ofwords xh xl - ofwords yh yl =
  ofwords (xh - yh - sub_borrow xl yl 0) (xl - yl) := sorry

lemma decompose_sub' (xh xl yh yl) : ofwords xh xl - ofwords yh yl =
  ofwords (xh + word.not yh + add_carry xl (word.not yl) 1) (xl - yl) := sorry

lemma mul_mulhu (x y) : ucoe x * ucoe y = ofwords (mulhu x y) (x * y) := sorry

lemma decompose_mul (xh xl yh yl) : ofwords xh xl * ofwords yh yl =
  ofwords (mulhu xl yl + xl * yh + xh * yl) (xl * yl) := sorry

lemma decompose_ltu (xh xl yh yl) :
  ltu (ofwords xh xl) (ofwords yh yl) ↔ if xh = yh then ltu xl yl else ltu xh yh := sorry

lemma decompose_leu (xh xl yh yl) : ¬ltu (ofwords yh yl) (ofwords xh xl) ↔
  if xh = yh then ¬ltu yl xl else ltu xh yh := sorry

lemma decompose_lt (xh xl yh yl) :
  ofwords xh xl < ofwords yh yl ↔ if xh = yh then xl < yl else xh < yh := sorry

lemma decompose_le (xh xl yh yl) : ofwords xh xl ≤ ofwords yh yl ↔
  if xh = yh then xl ≤ yl else xh < yh := sorry

lemma bytes_of_int64 (i) :
  (words_of_int 8 (unsigned i) : list byte) =
  words_of_int 4 (unsigned (loword i)) ++ words_of_int 4 (unsigned (hiword i)) := sorry

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