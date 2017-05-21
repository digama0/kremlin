
/- Architecture-dependent parameters for ARM -/

def nan_pl : ℕ → Type := sorry

namespace archi

def ptr64 : bool := ff

constant big_endian : bool

def align_int64 := 8
def align_float64 := 8

def splitlong := tt

lemma splitlong_ptr32 : splitlong = tt -> ptr64 = ff := λ_, rfl

def default_pl_64 : bool × nan_pl 53 :=
(ff, sorry)
  
def choose_binop_pl_64 (s1 : bool) (pl1 : nan_pl 53) (s2 : bool) (pl2 : nan_pl 53) : bool :=
sorry

def default_pl_32 : bool × nan_pl 24 :=
(ff, sorry)
  
def choose_binop_pl_32 (s1 : bool) (pl1 : nan_pl 24) (s2 : bool) (pl2 : nan_pl 24) : bool :=
sorry
   
def float_of_single_preserves_sNaN := ff
    
/- Which ABI to use : either the standard ARM EABI with floats passed
  in integer registers, or the "hardfloat" variant of the EABI
  that uses FP registers instead. -/

inductive abi_kind | Softfloat | Hardfloat
constant abi : abi_kind

end archi