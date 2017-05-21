import .archi

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

variable wordsize : ℕ

def word := fin (2^wordsize)

def byte := word 8

def int32 := word 32

def int64 := word 64

def ptrofs := word (if archi.ptr64 then 64 else 32)

end integers