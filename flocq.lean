import .lib .Int

/- Stub file for Flocq definitions -/

namespace flocq

def float : Type := sorry /- the type of IEE754 double-precision FP numbers -/
def float32 : Type := sorry /- the type of IEE754 single-precision FP numbers -/

def binary32 : Type := sorry
def binary64 : Type := sorry
def float.is_nan : float → bool := sorry
def float32.is_nan : float32 → bool := sorry
def split_bits : ℕ → ℕ → ℤ → bool × ℤ × ℤ := sorry

def nan_pl (n : ℕ) (h : n > 0 . exact_dec_trivial) := Int ⟨n, h⟩

def int_round_odd (x : ℤ) (p : ℕ) :=
(if x % (2^p) = 0 ∨ (x / 2^p) % 2 = 1 then x / 2^p else x / 2^p + 1) * 2^p.

end flocq