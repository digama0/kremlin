import .lib .word

/- Stub file for Flocq definitions -/

namespace flocq

def binary32 : Type := sorry
def binary64 : Type := sorry
def split_bits : ℕ → ℕ → ℤ → bool × ℤ × ℤ := sorry

def nan_pl (n : ℕ) (h : n > 0 . exact_dec_trivial) := word n

def int_round_odd (x : ℤ) (p : ℕ) :=
(if x % (2^p) = 0 ∨ (x / 2^p) % 2 = 1 then x / 2^p else x / 2^p + 1) * 2^p.

end flocq