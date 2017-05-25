import ..flocq

/- Indeterminate architecture -/

namespace archi
open flocq

def ptr64 : bool := sorry

def big_endian : bool := sorry

def align_int64 : ℕ := sorry
def align_float64 ℕ := sorry

def splitlong : bool := sorry

lemma splitlong_ptr32 : splitlong = tt → ptr64 = ff := sorry

def default_pl_64 : bool × nan_pl 53 := sorry

def choose_binop_pl_64 (s1 : bool) (pl1 : nan_pl 53) (s2 : bool) (pl2 : nan_pl 53) : bool := sorry

def default_pl_32 : bool × nan_pl 24 := sorry

def choose_binop_pl_32 (s1 : bool) (pl1 : nan_pl 24) (s2 : bool) (pl2 : nan_pl 24) : bool := sorry

def float_of_single_preserves_sNaN : bool := sorry

end archi