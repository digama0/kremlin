import ..flocq

/- Architecture-dependent parameters for PowerPC -/

namespace archi
open flocq

def ptr64 : bool := ff

def big_endian : bool := tt

def align_int64 := 8
def align_float64 := 8

def splitlong := tt

lemma splitlong_ptr32 : splitlong = tt → ptr64 = ff := λ_, rfl

def default_pl_64 : bool × nan_pl 53 :=
(ff, Int.repr (2^51))
  
def choose_binop_pl_64 (s1 : bool) (pl1 : nan_pl 53) (s2 : bool) (pl2 : nan_pl 53) : bool :=
ff /- always choose first NaN -/

def default_pl_32 : bool × nan_pl 24 :=
(ff,  Int.repr (2^22))
  
def choose_binop_pl_32 (s1 : bool) (pl1 : nan_pl 24) (s2 : bool) (pl2 : nan_pl 24) : bool :=
ff /- always choose first NaN -/
   
def float_of_single_preserves_sNaN := tt

/- Can we use the 64-bit extensions to the PowerPC architecture? -/
constant ppc64 : bool

end archi