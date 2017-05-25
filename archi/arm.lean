import ..flocq

/- Architecture-dependent parameters for ARM -/

namespace archi
open flocq

def ptr64 : bool := ff

def big_endian : bool := sorry

def align_int64 := 8
def align_float64 := 8

def splitlong := tt

lemma splitlong_ptr32 : splitlong = tt → ptr64 = ff := λ_, rfl

def default_pl_64 : bool × nan_pl 53 :=
(ff, word.repr (2^51))
  
def choose_binop_pl_64 (s1 : bool) (pl1 : nan_pl 53) (s2 : bool) (pl2 : nan_pl 53) : bool :=
/- Choose second NaN if pl2 is sNaN but pl1 is qNan.
   In all other cases, choose first NaN -/
pl1.unsigned.test_bit 51 && bnot (pl2.unsigned.test_bit 51)

def default_pl_32 : bool × nan_pl 24 :=
(ff,  word.repr (2^22))
  
def choose_binop_pl_32 (s1 : bool) (pl1 : nan_pl 24) (s2 : bool) (pl2 : nan_pl 24) : bool :=
/- Choose second NaN if pl2 is sNaN but pl1 is qNan.
   In all other cases, choose first NaN -/
pl1.unsigned.test_bit 22 && bnot (pl2.unsigned.test_bit 22)
   
def float_of_single_preserves_sNaN := ff
    
/- Which ABI to use : either the standard ARM EABI with floats passed
  in integer registers, or the "hardfloat" variant of the EABI
  that uses FP registers instead. -/

inductive abi_kind | Softfloat | Hardfloat
constant abi : abi_kind

end archi