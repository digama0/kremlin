
/- Arithmetic and logical operators for the Compcert C and Clight languages -/

import .ctypes .memory

namespace cop
open ast integers floats values memory ctypes word
     ctypes.intsize ctypes.floatsize ctypes.signedness

/- * Syntax of operators. -/

inductive unary_operation : Type
| Onotbool          /- boolean negation ([!] in C) -/
| Onotint           /- integer complement ([~] in C) -/
| Oneg              /- opposite (unary [-]) -/
| Oabsfloat         /- floating-point absolute value -/
open unary_operation

inductive binary_operation : Type
| Oadd              /- addition (binary [+]) -/
| Osub              /- subtraction (binary [-]) -/
| Omul              /- multiplication (binary [*]) -/
| Odiv              /- division ([/]) -/
| Omod              /- remainder ([%]) -/
| Oand              /- bitwise and ([&]) -/
| Oor               /- bitwise or ([|]) -/
| Oxor              /- bitwise xor ([^]) -/
| Oshl              /- left shift ([<<]) -/
| Oshr              /- right shift ([>>]) -/
| Oeq               /- comparison ([==]) -/
| One               /- comparison ([!=]) -/
| Olt               /- comparison ([<]) -/
| Ogt               /- comparison ([>]) -/
| Ole               /- comparison ([<=]) -/
| Oge               /- comparison ([>=]) -/
open binary_operation

inductive incr_or_decr : Type | Incr | Decr
open incr_or_decr

/- * Type classification and semantics of operators. -/

/- Most C operators are overloaded (they apply to arguments of various
  types) and their semantics depend on the types of their arguments.
  The following [classify_*] functions take as arguments the types
  of the arguments of an operation.  They return enough information
  to resolve overloading for this operator applications, such as
  ``both arguments are floats'', or ``the first is a pointer
  and the second is an integer''.  This classification is used in the
  compiler (module [Cshmgen]) to resolve overloading statically.

  The [sem_*] functions below compute the result of an operator
  application.  Since operators are overloaded, the result depends
  both on the static types of the arguments and on their run-time values.
  The corresponding [classify_*] function is first called on the
  types of the arguments to resolve static overloading.  It is then
  followed by a case analysis on the values of the arguments. -/

/- ** Casts and truth values -/

inductive classify_cast_cases : Type
| cast_case_pointer                                /- between pointer types or intptr_t types -/
| cast_case_i2i (sz2 : intsize) (si2 : signedness) /- int -> int -/
| cast_case_f2f                                    /- double -> double -/
| cast_case_s2s                                    /- single -> single -/
| cast_case_f2s                                    /- double -> single -/
| cast_case_s2f                                    /- single -> double -/
| cast_case_i2f (si1 : signedness)                 /- int -> double -/
| cast_case_i2s (si1 : signedness)                 /- int -> single -/
| cast_case_f2i (sz2 : intsize) (si2 : signedness) /- double -> int -/
| cast_case_s2i (sz2 : intsize) (si2 : signedness) /- single -> int -/
| cast_case_l2l                                    /- long -> long -/
| cast_case_i2l (si1 : signedness)                 /- int -> long -/
| cast_case_l2i (sz2 : intsize) (si2 : signedness) /- long -> int -/
| cast_case_l2f (si1 : signedness)                 /- long -> double -/
| cast_case_l2s (si1 : signedness)                 /- long -> single -/
| cast_case_f2l (si2 : signedness)                 /- double -> long -/
| cast_case_s2l (si2 : signedness)                 /- single -> long -/
| cast_case_i2bool                                 /- int -> bool -/
| cast_case_l2bool                                 /- long -> bool -/
| cast_case_f2bool                                 /- double -> bool -/
| cast_case_s2bool                                 /- single -> bool -/
| cast_case_struct (id1 id2 : ident)               /- struct -> struct -/
| cast_case_union  (id1 id2 : ident)               /- union -> union -/
| cast_case_void                                   /- any -> void -/
| cast_case_default
open classify_cast_cases

def classify_cast (tfrom tto : type) : classify_cast_cases :=
match tto, tfrom with
  /- To [void] -/
| Tvoid, _ := cast_case_void
  /- To [_Bool] -/
| Tint IBool _ _, Tint _ _ _ := cast_case_i2bool
| Tint IBool _ _, Tlong _ _ := cast_case_l2bool
| Tint IBool _ _, Tfloat F64 _ := cast_case_f2bool
| Tint IBool _ _, Tfloat F32 _ := cast_case_s2bool
| Tint IBool _ _, Tpointer _ _ := if archi.ptr64 then cast_case_l2bool else cast_case_i2bool
| Tint IBool _ _, Tarray _ _ _ := if archi.ptr64 then cast_case_l2bool else cast_case_i2bool
| Tint IBool _ _, Tfunction _ _ _ := if archi.ptr64 then cast_case_l2bool else cast_case_i2bool
  /- To [int] other than [_Bool] -/
| Tint sz2 si2 _, Tint _ _ _ :=
      if archi.ptr64 then cast_case_i2i sz2 si2
      else if sz2 = I32 then cast_case_pointer
      else cast_case_i2i sz2 si2
| Tint sz2 si2 _, Tlong _ _ := cast_case_l2i sz2 si2
| Tint sz2 si2 _, Tfloat F64 _ := cast_case_f2i sz2 si2
| Tint sz2 si2 _, Tfloat F32 _ := cast_case_s2i sz2 si2
| Tint sz2 si2 _, Tpointer _ _ :=
      if archi.ptr64 then cast_case_l2i sz2 si2
      else if sz2 = I32 then cast_case_pointer
      else cast_case_i2i sz2 si2
| Tint sz2 si2 _, Tarray _ _ _ :=
      if archi.ptr64 then cast_case_l2i sz2 si2
      else if sz2 = I32 then cast_case_pointer
      else cast_case_i2i sz2 si2
| Tint sz2 si2 _, Tfunction _ _ _ :=
      if archi.ptr64 then cast_case_l2i sz2 si2
      else if sz2 = I32 then cast_case_pointer
      else cast_case_i2i sz2 si2
  /- To [long] -/
| Tlong _ _, Tlong _ _ :=
      if archi.ptr64 then cast_case_pointer else cast_case_l2l
| Tlong _ _, Tint sz1 si1 _ := cast_case_i2l si1
| Tlong si2 _, Tfloat F64 _ := cast_case_f2l si2
| Tlong si2 _, Tfloat F32 _ := cast_case_s2l si2
| Tlong si2 _, Tpointer _ _ := if archi.ptr64 then cast_case_pointer else cast_case_i2l si2
| Tlong si2 _, Tarray _ _ _ := if archi.ptr64 then cast_case_pointer else cast_case_i2l si2
| Tlong si2 _, Tfunction _ _ _ := if archi.ptr64 then cast_case_pointer else cast_case_i2l si2
  /- To [float] -/
| Tfloat F64 _, Tint sz1 si1 _ := cast_case_i2f si1
| Tfloat F32 _, Tint sz1 si1 _ := cast_case_i2s si1
| Tfloat F64 _, Tlong si1 _ := cast_case_l2f si1
| Tfloat F32 _, Tlong si1 _ := cast_case_l2s si1
| Tfloat F64 _, Tfloat F64 _ := cast_case_f2f
| Tfloat F32 _, Tfloat F32 _ := cast_case_s2s
| Tfloat F64 _, Tfloat F32 _ := cast_case_s2f
| Tfloat F32 _, Tfloat F64 _ := cast_case_f2s
  /- To pointer types -/
| Tpointer _ _, Tint _ _ _ :=
      if archi.ptr64 then cast_case_i2l Unsigned else cast_case_pointer
| Tpointer _ _, Tlong _ _ :=
      if archi.ptr64 then cast_case_pointer else cast_case_l2i I32 Unsigned
| Tpointer _ _, Tpointer _ _ := cast_case_pointer
| Tpointer _ _, Tarray _ _ _ := cast_case_pointer
| Tpointer _ _, Tfunction _ _ _ := cast_case_pointer
  /- To struct or union types -/
| Tstruct id2 _, Tstruct id1 _ := cast_case_struct id1 id2
| Tunion id2 _, Tunion id1 _ := cast_case_union id1 id2
  /- Catch-all -/
| _, _ := cast_case_default
end

/- Semantics of casts.  [sem_cast v1 t1 t2 m = Some v2] if value [v1],
  viewed with static type [t1], can be converted  to type [t2],
  resulting in value [v2].  -/

def cast_int_int : intsize → signedness → int32 → int32
| I8  Signed   i := sign_ext W8 i
| I8  Unsigned i := zero_ext 8 i
| I16 Signed   i := sign_ext W16 i
| I16 Unsigned i := zero_ext 16 i
| I32 _        i := i
| IBool _      i := if i = 0 then 0 else 1

def cast_int_float : signedness → int32 → float
| Signed   := float.of_int
| Unsigned := float.of_intu

def cast_float_int : signedness → float → option int32
| Signed   := float.to_int
| Unsigned := float.to_intu

def cast_int_single : signedness → int32 → float32
| Signed   := float32.of_int
| Unsigned := float32.of_intu

def cast_single_int : signedness → float32 → option int32
| Signed   := float32.to_int
| Unsigned := float32.to_intu

def cast_int_long : signedness → int32 → int64
| Signed   := scoe
| Unsigned := ucoe

def cast_long_float : signedness → int64 → float
| Signed   := float.of_long
| Unsigned := float.of_longu

def cast_long_single : signedness → int64 → float32
| Signed   := float32.of_long
| Unsigned := float32.of_longu

def cast_float_long : signedness → float → option int64
| Signed   := float.to_long
| Unsigned := float.to_longu

def cast_single_long : signedness → float32 → option int64
| Signed   := float32.to_long
| Unsigned := float32.to_longu

def sem_cast (m : mem) (v : val) (t1 t2 : type) : option val :=
match classify_cast t1 t2, v with
| cast_case_pointer,        Vptr _ _   := some v
| cast_case_pointer,        Vint _     := if archi.ptr64 then none else some v
| cast_case_pointer,        Vlong _    := if archi.ptr64 then some v else none
| cast_case_i2i sz2 si2,    Vint i     := some (Vint (cast_int_int sz2 si2 i))
| cast_case_f2f,            Vfloat f   := some (Vfloat f)
| cast_case_s2s,            Vsingle f  := some (Vsingle f)
| cast_case_s2f,            Vsingle f  := some (Vfloat (float.of_single f))
| cast_case_f2s,            Vfloat f   := some (Vsingle (float.to_single f))
| cast_case_i2f si1,        Vint i     := some (Vfloat (cast_int_float si1 i))
| cast_case_i2s si1,        Vint i     := some (Vsingle (cast_int_single si1 i))
| cast_case_f2i sz2 si2,    Vfloat f   := (λi, Vint (cast_int_int sz2 si2 i)) <$> cast_float_int si2 f
| cast_case_s2i sz2 si2,    Vsingle f  := (λi, Vint (cast_int_int sz2 si2 i)) <$> cast_single_int si2 f
| cast_case_i2bool,         Vint n     := some (Vint (if n = 0 then 0 else 1))
| cast_case_i2bool,         Vptr b ofs := if ¬ archi.ptr64 ∧ weak_valid_pointer m b (unsigned ofs) then some Vone else none
| cast_case_l2bool,         Vlong n    := some (Vint (if n = 0 then 0 else 1))
| cast_case_l2bool,         Vptr b ofs := if archi.ptr64 ∧ weak_valid_pointer m b (unsigned ofs) then some Vone else none
| cast_case_f2bool,         Vfloat f   := some (Vint (if float.cmp Ceq f 0 then 0 else 1))
| cast_case_s2bool,         Vsingle f  := some (Vint (if float32.cmp Ceq f 0 then 0 else 1))
| cast_case_l2l,            Vlong n    := some (Vlong n)
| cast_case_i2l si,         Vint n     := some (Vlong (cast_int_long si n))
| cast_case_l2i sz si,      Vlong n    := some (Vint (cast_int_int sz si (ucoe n)))
| cast_case_l2f si1,        Vlong i    := some (Vfloat (cast_long_float si1 i))
| cast_case_l2s si1,        Vlong i    := some (Vsingle (cast_long_single si1 i))
| cast_case_f2l si2,        Vfloat f   := Vlong <$> cast_float_long si2 f
| cast_case_s2l si2,        Vsingle f  := Vlong <$> cast_single_long si2 f
| cast_case_struct id1 id2, Vptr b ofs := if id1 = id2 then some v else none
| cast_case_union id1 id2,  Vptr b ofs := if id1 = id2 then some v else none
| cast_case_void,           v          := some v
| _,                        _          := none
end

/- The following describes types that can be interpreted as a boolean:
  integers, floats, pointers.  It is used for the semantics of
  the [!] and [?] operators, as well as the [if], [while],
  and [for] statements. -/

inductive classify_bool_cases : Type
| bool_case_i                           /- integer -/
| bool_case_l                           /- long -/
| bool_case_f                           /- double float -/
| bool_case_s                           /- single float -/
| bool_default
open classify_bool_cases

def classify_bool (ty : type) : classify_bool_cases :=
match typeconv ty with
| Tint _ _ _   := bool_case_i
| Tpointer _ _ := if archi.ptr64 then bool_case_l else bool_case_i
| Tfloat F64 _ := bool_case_f
| Tfloat F32 _ := bool_case_s
| Tlong _ _    := bool_case_l
| _            := bool_default
end

/- Interpretation of values as truth values.
  Non-zero integers, non-zero floats and non-null pointers are
  considered as true.  The integer zero (which also represents
  the null pointer) and the float 0.0 are false. -/

def bool_val (m : mem) (v : val) (t : type) : option bool :=
match classify_bool t, v with
| bool_case_i, Vint n := some (n ≠ 0)
| bool_case_i, Vptr b ofs := if archi.ptr64 then none else
          if weak_valid_pointer m b (unsigned ofs) then some tt else none
| bool_case_l, Vlong n := some (n ≠ 0)
| bool_case_l, Vptr b ofs := if ¬ archi.ptr64 then none else
          if weak_valid_pointer m b (unsigned ofs) then some tt else none
| bool_case_f, Vfloat f := some (bnot (float.cmp Ceq f 0))
| bool_case_s, Vsingle f := some (bnot (float32.cmp Ceq f 0))
| _, _ := none
end

/- ** Unary operators -/

/- *** Boolean negation -/

def sem_notbool (m : mem) (v : val) (ty : type) : option val :=
(λ b, val.of_bool (bnot b)) <$> bool_val m v ty

/- *** Opposite and absolute value -/

inductive classify_neg_cases : Type
| neg_case_i (s : signedness)            /- int -/
| neg_case_f                             /- double float -/
| neg_case_s                             /- single float -/
| neg_case_l (s : signedness)            /- long -/
| neg_default
open classify_neg_cases

def classify_neg : type → classify_neg_cases
| (Tint I32 Unsigned _) := neg_case_i Unsigned
| (Tint _ _ _)          := neg_case_i Signed
| (Tfloat F64 _)        := neg_case_f
| (Tfloat F32 _)        := neg_case_s
| (Tlong si _)          := neg_case_l si
| _                     := neg_default

def sem_neg (v : val) (ty : type) : option val :=
match classify_neg ty, v with
| neg_case_i sg, Vint n  := some (Vint (-n))
| neg_case_f, Vfloat f   := some (Vfloat (-f))
| neg_case_s, Vsingle f  := some (Vsingle (-f))
| neg_case_l sg, Vlong n := some (Vlong (-n))
| _, _                   := none
end

def sem_absfloat (v : val) (ty : type) : option val :=
match classify_neg ty, v with
| neg_case_i sg, Vint n  := some (Vfloat (float.abs (cast_int_float sg n)))
| neg_case_f, Vfloat f   := some (Vfloat (float.abs f))
| neg_case_s, Vsingle f  := some (Vfloat (float.abs (float.of_single f)))
| neg_case_l sg, Vlong n := some (Vfloat (float.abs (cast_long_float sg n)))
| _, _                   := none
end

/- *** Bitwise complement -/

inductive classify_notint_cases : Type
| notint_case_i (s : signedness)              /- int -/
| notint_case_l (s : signedness)              /- long -/
| notint_default
open classify_notint_cases

def classify_notint : type → classify_notint_cases
| (Tint I32 Unsigned _) := notint_case_i Unsigned
| (Tint _ _ _) := notint_case_i Signed
| (Tlong si _) := notint_case_l si
| _ := notint_default

def sem_notint (v : val) (ty : type) : option val :=
match classify_notint ty, v with
| notint_case_i sg, Vint n  := some (Vint (word.not n))
| notint_case_l sg, Vlong n := some (Vlong (word.not n))
| _, _                      := none
end

/- ** Binary operators -/

/- For binary operations, the "usual binary conversions" consist in
- determining the type at which the operation is to be performed
  (a form of least upper bound of the types of the two arguments);
- casting the two arguments to this common type;
- performing the operation at that type.
-/

inductive binarith_cases : Type
| bin_case_i (s : signedness)        /- at int type -/
| bin_case_l (s : signedness)        /- at long int type -/
| bin_case_f                         /- at double float type -/
| bin_case_s                         /- at single float type -/
| bin_default                        /- error -/
open binarith_cases

def classify_binarith : type → type → binarith_cases
| (Tint I32 Unsigned _) (Tint _ _ _)          := bin_case_i Unsigned
| (Tint _ _ _)          (Tint I32 Unsigned _) := bin_case_i Unsigned
| (Tint _ _ _)          (Tint _ _ _)          := bin_case_i Signed
| (Tlong Signed _)      (Tlong Signed _)      := bin_case_l Signed
| (Tlong _ _)           (Tlong _ _)           := bin_case_l Unsigned
| (Tlong sg _)          (Tint _ _ _)          := bin_case_l sg
| (Tint _ _ _)          (Tlong sg _)          := bin_case_l sg
| (Tfloat F32 _)        (Tfloat F32 _)        := bin_case_s
| (Tfloat _ _)          (Tfloat _ _)          := bin_case_f
| (Tfloat F64 _)        (Tint _ _ _)          := bin_case_f
| (Tfloat F64 _)        (Tlong _ _)           := bin_case_f
| (Tint _ _ _)          (Tfloat F64 _)        := bin_case_f
| (Tlong _ _)           (Tfloat F64 _)        := bin_case_f
| (Tfloat F32 _)        (Tint _ _ _)          := bin_case_s
| (Tfloat F32 _)        (Tlong _ _)           := bin_case_s
| (Tint _ _ _)          (Tfloat F32 _)        := bin_case_s
| (Tlong _ _)           (Tfloat F32 _)        := bin_case_s
| _                     _                     := bin_default

/- The static type of the result. Both arguments are converted to this type
    before the actual computation. -/

def binarith_type : binarith_cases → type
| (bin_case_i sg) := Tint I32 sg noattr
| (bin_case_l sg) := Tlong sg noattr
| bin_case_f      := Tfloat F64 noattr
| bin_case_s      := Tfloat F32 noattr
| bin_default     := Tvoid

def sem_binarith
    (sem_int : signedness → int32 → int32 → option val)
    (sem_long : signedness → int64 → int64 → option val)
    (sem_float : float → float → option val)
    (sem_single : float32 → float32 → option val)
    (m : mem) (v1 : val) (t1 : type) (v2 : val) (t2 : type) : option val :=
let c := classify_binarith t1 t2, t := binarith_type c in
match sem_cast m v1 t1 t, sem_cast m v2 t2 t, c with
| some (Vint n1),    some (Vint n2),    bin_case_i sg := sem_int sg n1 n2
| some (Vfloat n1),  some (Vfloat n2),  bin_case_f    := sem_float n1 n2
| some (Vsingle n1), some (Vsingle n2), bin_case_s    := sem_single n1 n2
| some (Vlong n1),   some (Vlong n2),   bin_case_l sg := sem_long sg n1 n2
| _,                 _,                 _             := none
end

/- *** Addition -/

inductive classify_add_cases : Type
| add_case_pi (ty : type) (si : signedness)     /- pointer, int -/
| add_case_pl (ty : type)                       /- pointer, long -/
| add_case_ip (si : signedness) (ty : type)     /- int, pointer -/
| add_case_lp (ty : type)                       /- long, pointer -/
| add_default                                   /- numerical type, numerical type -/
open classify_add_cases

def classify_add (ty1 : type) (ty2 : type) :=
match typeconv ty1, typeconv ty2 with
| Tpointer ty _, Tint _ si _   := add_case_pi ty si
| Tpointer ty _, Tlong _ _     := add_case_pl ty
| Tint _ si _,   Tpointer ty _ := add_case_ip si ty
| Tlong _ _,     Tpointer ty _ := add_case_lp ty
| _,             _             := add_default
end

def ptrofs_of_int : signedness → int32 → ptrofs
| Signed := ptrofs.of_ints
| Unsigned := ptrofs.of_intu

def sem_add_ptr_int (cenv : composite_env) (ty : type) (si : signedness) : val → val → option val
| (Vptr b1 ofs1) (Vint n2) := let n2 := ptrofs_of_int si n2 in
                              some (Vptr b1 (ofs1 + repr (sizeof cenv ty) * n2))
| (Vint n1)      (Vint n2) := if archi.ptr64 then none else
                              some (Vint (n1 + repr (sizeof cenv ty) * n2))
| (Vlong n1)     (Vint n2) := let n2 := cast_int_long si n2 in
                              if ¬ archi.ptr64 then none else
                              some (Vlong (n1 + repr (sizeof cenv ty) * n2))
| _              _         := none

def sem_add_ptr_long (cenv : composite_env) (ty : type) : val → val → option val
| (Vptr b1 ofs1) (Vlong n2) := let n2 := ptrofs.of_int64 n2 in
                               some (Vptr b1 (ofs1 + repr (sizeof cenv ty) * n2))
| (Vint n1)      (Vlong n2) := let n2 : int32 := ucoe n2 in
                               if archi.ptr64 then none else
                               some (Vint (n1 + repr (sizeof cenv ty) * n2))
| (Vlong n1)     (Vlong n2) := if ¬ archi.ptr64 then none else
                               some (Vlong (n1 + repr (sizeof cenv ty) * n2))
| _              _          := none

def sem_add (cenv : composite_env) (m : mem) (v1 : val) (t1 : type) (v2 : val) (t2 : type) : option val :=
match classify_add t1 t2 with
| add_case_pi ty si := sem_add_ptr_int cenv ty si v1 v2             /- pointer plus integer -/
| add_case_pl ty    := sem_add_ptr_long cenv ty v1 v2                 /- pointer plus long -/
| add_case_ip si ty := sem_add_ptr_int cenv ty si v2 v1             /- integer plus pointer -/
| add_case_lp ty    := sem_add_ptr_long cenv ty v2 v1                  /- long plus pointer -/
| add_default       := sem_binarith
    (λ sg n1 n2, some (Vint (n1 + n2)))
    (λ sg n1 n2, some (Vlong (n1 + n2)))
    (λ n1 n2, some (Vfloat (n1 + n2)))
    (λ n1 n2, some (Vsingle (n1 + n2)))
    m v1 t1 v2 t2
end

/- *** Subtraction -/

inductive classify_sub_cases : Type
| sub_case_pi (ty : type) (si : signedness)  /- pointer, int -/
| sub_case_pp (ty : type)               /- pointer, pointer -/
| sub_case_pl (ty : type)               /- pointer, long -/
| sub_default                           /- numerical type, numerical type -/
open classify_sub_cases

def classify_sub (ty1 : type) (ty2 : type) :=
match typeconv ty1, typeconv ty2 with
| Tpointer ty _,  Tint _ si _  := sub_case_pi ty si
| Tpointer ty _ , Tpointer _ _ := sub_case_pp ty
| Tpointer ty _,  Tlong _ _    := sub_case_pl ty
| _,              _            := sub_default
end

def sem_sub (cenv : composite_env) (m : mem) (v1 : val) (t1 : type) (v2 : val) (t2 : type) : option val :=
match classify_sub t1 t2, v1, v2 with
| sub_case_pi ty si, Vptr b1 ofs1, Vint n2 :=
    let n2 := ptrofs_of_int si n2 in
    some (Vptr b1 (ofs1 - repr (sizeof cenv ty) * n2))
| sub_case_pi ty si, Vint n1, Vint n2 :=
    if archi.ptr64 then none else some (Vint (n1 - repr (sizeof cenv ty) * n2))
| sub_case_pi ty si, Vlong n1, Vint n2 :=
    let n2 := cast_int_long si n2 in
    if archi.ptr64 then some (Vlong (n1 - repr (sizeof cenv ty) * n2)) else none
| sub_case_pl ty, Vptr b1 ofs1, Vlong n2 :=
    let n2 := ptrofs.of_int64 n2 in
    some (Vptr b1 (ofs1 - repr (sizeof cenv ty) * n2))
| sub_case_pl ty, Vint n1, Vlong n2 :=
    if archi.ptr64 then none else some (Vint (n1 - repr (sizeof cenv ty) * ucoe n2))
| sub_case_pl ty, Vlong n1, Vlong n2 :=
    if archi.ptr64 then some (Vlong (n1 - repr (sizeof cenv ty) * n2)) else none
| sub_case_pp ty, Vptr b1 ofs1, Vptr b2 ofs2 :=
    if b1 = b2 then
      let sz := sizeof cenv ty in
      if 0 < sz ∧ sz ≤ max_signed ptrofs.wordsize
      then some (Vptrofs ((ofs1 - ofs2) / repr sz : word _))
      else none
    else none
| sub_default, _, _ := sem_binarith
      (λ sg n1 n2, some (Vint (n1 - n2)))
      (λ sg n1 n2, some (Vlong (n1 - n2)))
      (λ n1 n2, some (Vfloat (n1 - n2)))
      (λ n1 n2, some (Vsingle (n1 - n2)))
      m v1 t1 v2 t2
| _, _, _ := none
end

/- *** Multiplication, division, modulus -/

def sem_mul : mem → val → type → val → type → option val :=
sem_binarith
  (λ sg n1 n2, some (Vint (n1 * n2)))
  (λ sg n1 n2, some (Vlong (n1 * n2)))
  (λ n1 n2, some (Vfloat (n1 * n2)))
  (λ n1 n2, some (Vsingle (n1 * n2)))

def sem_div : mem → val → type → val → type → option val :=
sem_binarith
  (λ sg n1 n2,
    match sg with
    | Signed   := if n2 = 0 ∨ n1 = repr (min_signed W32) ∧ n2 = -1
                  then none else some (Vint (n1 / n2 : word _))
    | Unsigned := if n2 = 0 then none else some (Vint (n1 / n2 : uword _))
    end)
  (λ sg n1 n2,
    match sg with
    | Signed   := if n2 = 0 ∨ n1 = repr (min_signed W64) ∧ n2 = -1
                  then none else some (Vlong (n1 / n2 : word _))
    | Unsigned := if n2 = 0 then none else some (Vlong (n1 / n2 : uword _))
    end)
  (λ n1 n2, some (Vfloat (n1 / n2)))
  (λ n1 n2, some (Vsingle (n1 / n2)))

def sem_mod : mem → val → type → val → type → option val :=
sem_binarith
  (λ sg n1 n2,
    match sg with
    | Signed   := if n2 = 0 ∨ n1 = repr (min_signed W32) ∧ n2 = -1
                  then none else some (Vint (n1 % n2 : word _))
    | Unsigned := if n2 = 0 then none else some (Vint (n1 % n2 : uword _))
    end)
  (λ sg n1 n2,
    match sg with
    | Signed   := if n2 = 0 ∨ n1 = repr (min_signed W64) ∧ n2 = -1
                  then none else some (Vlong (n1 % n2 : word _))
    | Unsigned := if n2 = 0 then none else some (Vlong (n1 % n2 : uword _))
    end)
  (λ n1 n2, none)
  (λ n1 n2, none)

def sem_and : mem → val → type → val → type → option val :=
sem_binarith
  (λ sg n1 n2, some (Vint (word.and n1 n2)))
  (λ sg n1 n2, some (Vlong (word.and n1 n2)))
  (λ n1 n2, none)
  (λ n1 n2, none)

def sem_or : mem → val → type → val → type → option val :=
sem_binarith
  (λ sg n1 n2, some (Vint (word.or n1 n2)))
  (λ sg n1 n2, some (Vlong (word.or n1 n2)))
  (λ n1 n2, none)
  (λ n1 n2, none)

def sem_xor : mem → val → type → val → type → option val :=
sem_binarith
  (λ sg n1 n2, some (Vint (word.xor n1 n2)))
  (λ sg n1 n2, some (Vlong (word.xor n1 n2)))
  (λ n1 n2, none)
  (λ n1 n2, none)

/- *** Shifts -/

/- Shifts do not perform the usual binary conversions.  Instead,
  each argument is converted independently, and the signedness
  of the result is always that of the first argument. -/

inductive classify_shift_cases : Type
| shift_case_ii (s : signedness)         /- int , int -/
| shift_case_ll (s : signedness)         /- long, long -/
| shift_case_il (s : signedness)         /- int, long -/
| shift_case_li (s : signedness)         /- long, int -/
| shift_default
open classify_shift_cases

def classify_shift (ty1 : type) (ty2 : type) :=
match typeconv ty1, typeconv ty2 with
| Tint I32 Unsigned _, Tint _ _ _ := shift_case_ii Unsigned
| Tint _ _ _,          Tint _ _ _ := shift_case_ii Signed
| Tint I32 Unsigned _, Tlong _ _  := shift_case_il Unsigned
| Tint _ _ _,          Tlong _ _  := shift_case_il Signed
| Tlong s _,           Tint _ _ _ := shift_case_li s
| Tlong s _,           Tlong _ _  := shift_case_ll s
| _,                   _          := shift_default
end

def sem_shift
    (sem_int : signedness → int32 → int32 → int32)
    (sem_long : signedness → int64 → int64 → int64)
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) : option val :=
match classify_shift t1 t2, v1, v2 with
| shift_case_ii sg, Vint n1,  Vint n2  := if ltu n2 iwordsize then some (Vint (sem_int sg n1 n2)) else none
| shift_case_il sg, Vint n1,  Vlong n2 := if ltu n2 (repr 32) then some (Vint (sem_int sg n1 n2.loword)) else none
| shift_case_li sg, Vlong n1, Vint n2  := if ltu n2 (repr 64) then some (Vlong (sem_long sg n1 (ucoe n2))) else none
| shift_case_ll sg, Vlong n1, Vlong n2 := if ltu n2 iwordsize then some (Vlong (sem_long sg n1 n2)) else none
| _,                _,        _        := none
end

def sem_shl : val → type → val → type → option val :=
sem_shift
  (λ sg n1 n2, word.shl n1 n2)
  (λ sg n1 n2, word.shl n1 n2)

def sem_shr : val → type → val → type → option val :=
sem_shift
  (λ sg n1 n2, match sg with Signed := word.shr n1 n2 | Unsigned := word.shru n1 n2 end)
  (λ sg n1 n2, match sg with Signed := word.shr n1 n2 | Unsigned := word.shru n1 n2 end)

/- *** Comparisons -/

inductive classify_cmp_cases : Type
| cmp_case_pp                        /- pointer, pointer -/
| cmp_case_pi (si : signedness)      /- pointer, int -/
| cmp_case_ip (si : signedness)      /- int, pointer -/
| cmp_case_pl                        /- pointer, long -/
| cmp_case_lp                        /- long, pointer -/
| cmp_default                        /- numerical, numerical -/
open classify_cmp_cases

def classify_cmp (ty1 : type) (ty2 : type) :=
match typeconv ty1, typeconv ty2 with
| Tpointer _ _ , Tpointer _ _ := cmp_case_pp
| Tpointer _ _ , Tint _ si _  := cmp_case_pi si
| Tint _ si _,   Tpointer _ _ := cmp_case_ip si
| Tpointer _ _ , Tlong _ _    := cmp_case_pl
| Tlong _ _ ,    Tpointer _ _ := cmp_case_lp
| _,             _            := cmp_default
end

def cmp_ptr (m : mem) (c : comparison) (v1 v2 : val) : option val :=
val.of_bool <$> (if archi.ptr64 then cmplu_bool else cmpu_bool) (valid_pointer m) c v1 v2

def sem_cmp (c : comparison) (m : mem) (v1 : val) (t1 : type) (v2 : val) (t2 : type) : option val :=
match classify_cmp t1 t2, v1, v2 with
| cmp_case_pp,    v1, v2         := cmp_ptr m c v1 v2
| cmp_case_pi si, v1, Vint n2    := cmp_ptr m c v1 (Vptrofs (ptrofs_of_int si n2))
| cmp_case_pi si, v1, Vptr b ofs := if archi.ptr64 then none else cmp_ptr m c v1 v2
| cmp_case_ip si, Vint n1, v2    := cmp_ptr m c (Vptrofs (ptrofs_of_int si n1)) v2
| cmp_case_ip si, Vptr b ofs, v2 := if archi.ptr64 then none else cmp_ptr m c (Vptr b ofs) v2
| cmp_case_pl,    v1, Vlong n2   := cmp_ptr m c v1 (Vptrofs (ptrofs.of_int64 n2))
| cmp_case_pl,    v1, Vptr b ofs := if archi.ptr64 then cmp_ptr m c v1 (Vptr b ofs) else none
| cmp_case_lp,    Vlong n1,   v2 := cmp_ptr m c (Vptrofs (ptrofs.of_int64 n1)) v2
| cmp_case_lp,    Vptr b ofs, v2 := if archi.ptr64 then cmp_ptr m c v1 v2 else none
| cmp_default,    v1, v2         := sem_binarith
    (λ sg n1 n2, some (val.of_bool ((match sg with Signed := word.cmp | Unsigned := word.cmpu end) c n1 n2)))
    (λ sg n1 n2, some (val.of_bool ((match sg with Signed := word.cmp | Unsigned := word.cmpu end) c n1 n2)))
    (λ n1 n2, some (val.of_bool (float.cmp c n1 n2)))
    (λ n1 n2, some (val.of_bool (float32.cmp c n1 n2)))
    m v1 t1 v2 t2
| _,              _, _           := none
end

/- ** Function applications -/

inductive classify_fun_cases : Type
| fun_case_f (targs : list type) (tres : type) (cc : calling_convention) /- (pointer to) function -/
| fun_default
open classify_fun_cases

def classify_fun : type → classify_fun_cases
| (Tfunction args res cc)              := fun_case_f args res cc
| (Tpointer (Tfunction args res cc) _) := fun_case_f args res cc
| _                                    := fun_default

/- ** Argument of a [switch] statement -/

inductive classify_switch_cases : Type
| switch_case_i
| switch_case_l
| switch_default
open classify_switch_cases

def classify_switch : type → classify_switch_cases
| (Tint _ _ _) := switch_case_i
| (Tlong _ _)  := switch_case_l
| _            := switch_default

def sem_switch_arg (v : val) (ty : type) : option ℤ :=
match classify_switch ty, v with
| switch_case_i, Vint n  := some (unsigned n)
| switch_case_l, Vlong n := some (unsigned n)
| _,             _       := none
end

/- * Combined semantics of unary and binary operators -/

def sem_unary_operation : unary_operation → mem → val → type → option val
| Onotbool  := sem_notbool
| Onotint   := λ_, sem_notint
| Oneg      := λ_, sem_neg
| Oabsfloat := λ_, sem_absfloat

def sem_binary_operation (cenv : composite_env) :
  binary_operation → mem → val → type → val → type → option val
| Oadd := sem_add cenv
| Osub := sem_sub cenv
| Omul := sem_mul
| Omod := sem_mod
| Odiv := sem_div
| Oand := sem_and
| Oor  := sem_or
| Oxor := sem_xor
| Oshl := λ_, sem_shl
| Oshr := λ_, sem_shr
| Oeq  := sem_cmp Ceq
| One  := sem_cmp Cne
| Olt  := sem_cmp Clt
| Ogt  := sem_cmp Cgt
| Ole  := sem_cmp Cle
| Oge  := sem_cmp Cge

def sem_incrdecr (cenv : composite_env) (id : incr_or_decr) (m : mem) (v : val) (ty : type) :=
match id with
| Incr := sem_add cenv m v ty 1 type_int32s
| Decr := sem_sub cenv m v ty 1 type_int32s
end

def incrdecr_type (ty : type) :=
match typeconv ty with
| Tpointer ty a := Tpointer ty a
| Tint sz sg a  := Tint sz sg noattr
| Tlong sg a    := Tlong sg noattr
| Tfloat sz a   := Tfloat sz noattr
| _             := Tvoid
end

/- * Compatibility with extensions and injections -/

section generic_injection

parameters {f : meminj} {m m' : mem}

parameter (valid_pointer_inj :
  ∀ b1 (ofs : ptrofs) b2 delta,
  f b1 = some (b2, delta) →
  valid_pointer m b1 (unsigned ofs) →
  valid_pointer m' b2 (unsigned (ofs + repr delta)))

parameter (weak_valid_pointer_inj :
  ∀ b1 (ofs : ptrofs) b2 delta,
  f b1 = some (b2, delta) →
  weak_valid_pointer m b1 (unsigned ofs) →
  weak_valid_pointer m' b2 (unsigned (ofs + repr delta)))

parameter (weak_valid_pointer_no_overflow :
  ∀ b1 (ofs : ptrofs) b2 delta,
  f b1 = some (b2, delta) →
  weak_valid_pointer m b1 (unsigned ofs) →
  unsigned ofs + unsigned (repr delta : ptrofs) ≤ max_unsigned ptrofs.wordsize)

parameter (valid_different_pointers_inj :
  ∀ b1 b2 (ofs1 ofs2 : ptrofs) b1' delta1 b2' delta2,
  b1 ≠ b2 →
  valid_pointer m b1 (unsigned ofs1) →
  valid_pointer m b2 (unsigned ofs2) →
  f b1 = some (b1', delta1) →
  f b2 = some (b2', delta2) →
  b1' = b2' →
  unsigned (ofs1 + repr delta1) ≠ unsigned (ofs2 + repr delta2))

theorem val_inject_vtrue (f) : inject f Vtrue Vtrue := sorry'

theorem val_inject_vfalse (f) : inject f Vfalse Vfalse := sorry'

theorem val_inject_of_bool (f b) : inject f (val.of_bool b) (val.of_bool b) := sorry'

theorem val_inject_vptrofs (n) : inject f (Vptrofs n) (Vptrofs n) := sorry'

lemma sem_cast_inj {v1 ty1 ty v tv1} :
  sem_cast m v1 ty1 ty = some v →
  inject f v1 tv1 →
  ∃ tv, sem_cast m' tv1 ty1 ty = some tv ∧ inject f v tv := sorry'

lemma bool_val_inj {v ty b tv} :
  bool_val m v ty = some b →
  inject f v tv →
  bool_val m' tv ty = some b := sorry'

lemma sem_unary_operation_inj {op v1 ty v tv1} :
  sem_unary_operation op m v1 ty = some v →
  inject f v1 tv1 →
  ∃ tv, sem_unary_operation op m' tv1 ty = some tv ∧ inject f v tv := sorry'

def optval_self_injects : option val → bool
| (some (Vptr b ofs)) := ff
| _                   := tt

theorem sem_binarith_inject {sem_int sem_long sem_float sem_single v1 t1 v2 t2 v v1' v2'} :
  sem_binarith sem_int sem_long sem_float sem_single m v1 t1 v2 t2 = some v →
  inject f v1 v1' → inject f v2 v2' →
  (∀ sg n1 n2, optval_self_injects (sem_int sg n1 n2)) →
  (∀ sg n1 n2, optval_self_injects (sem_long sg n1 n2)) →
  (∀ n1 n2, optval_self_injects (sem_float n1 n2)) →
  (∀ n1 n2, optval_self_injects (sem_single n1 n2)) →
  ∃ v', sem_binarith sem_int sem_long sem_float sem_single m' v1' t1 v2' t2 = some v' ∧ inject f v v' := sorry'

theorem sem_shift_inject {sem_int sem_long v1 t1 v2 t2 v v1' v2'} :
  sem_shift sem_int sem_long v1 t1 v2 t2 = some v →
  inject f v1 v1' → inject f v2 v2' →
  ∃ v', sem_shift sem_int sem_long v1' t1 v2' t2 = some v' ∧ inject f v v' := sorry'

theorem sem_cmp_ptr_inj {c v1 v2 v tv1 tv2} :
  cmp_ptr m c v1 v2 = some v →
  inject f v1 tv1 →
  inject f v2 tv2 →
  ∃ tv, cmp_ptr m' c tv1 tv2 = some tv ∧ inject f v tv := sorry'

theorem sem_cmp_inj {cmp v1 tv1 ty1 v2 tv2 ty2 v} :
  sem_cmp cmp m v1 ty1 v2 ty2 = some v →
  inject f v1 tv1 →
  inject f v2 tv2 →
  ∃ tv, sem_cmp cmp m' tv1 ty1 tv2 ty2 = some tv ∧ inject f v tv := sorry'

lemma sem_binary_operation_inj {cenv op v1 ty1 v2 ty2 v tv1 tv2} :
  sem_binary_operation cenv op m v1 ty1 v2 ty2 = some v →
  inject f v1 tv1 → inject f v2 tv2 →
  ∃ tv, sem_binary_operation cenv op m' tv1 ty1 tv2 ty2 = some tv ∧ inject f v tv := sorry'

end generic_injection

lemma sem_cast_inject {f v1 ty1 ty m v tv1 tm} :
  sem_cast m v1 ty1 ty = some v →
  inject f v1 tv1 →
  inject f m tm →
  ∃ tv, sem_cast tm tv1 ty1 ty = some tv ∧ inject f v tv := sorry'

lemma sem_unary_operation_inject {f m m' op v1 ty1 v tv1} :
  sem_unary_operation op m v1 ty1 = some v →
  inject f v1 tv1 →
  inject f m m' →
  ∃ tv, sem_unary_operation op m' tv1 ty1 = some tv ∧ inject f v tv := sorry'

lemma sem_binary_operation_inject {f m m' cenv op v1 ty1 v2 ty2 v tv1 tv2} :
  sem_binary_operation cenv op m v1 ty1 v2 ty2 = some v →
  inject f v1 tv1 → inject f v2 tv2 →
  inject f m m' →
  ∃ tv, sem_binary_operation cenv op m' tv1 ty1 tv2 ty2 = some tv ∧ inject f v tv := sorry'

lemma bool_val_inject {f m m' v ty b tv} :
  bool_val m v ty = some b →
  inject f v tv →
  inject f m m' →
  bool_val m' tv ty = some b := sorry'

/- * Some properties of operator semantics -/

/- This section collects some common-sense properties about the type
  classification and semantic functions above.  Some properties are used
  in the CompCert semantics preservation proofs.  Others are not, but increase
  confidence in the specification and its relation with the ISO C99 standard. -/

/- Relation between Boolean value and casting to [_Bool] type. -/

lemma cast_bool_bool_val {v t m} :
  sem_cast m v t (Tint IBool Signed noattr) =
  val.of_bool <$> bool_val m v t := sorry'

/- Relation between Boolean value and Boolean negation. -/

lemma notbool_bool_val {v t m} :
  sem_notbool m v t =
  val.of_bool <$> bnot <$> bool_val m v t := sorry'

/- Properties of values obtained by casting to a given type. -/

section val_casted

inductive val_casted : val → type → Prop
| int (sz si attr n)       : cast_int_int sz si n = n → val_casted (Vint n) (Tint sz si attr)
| float (attr n)           : val_casted (Vfloat n) (Tfloat F64 attr)
| single (attr n)          : val_casted (Vsingle n) (Tfloat F32 attr)
| long (si attr n)         : val_casted (Vlong n) (Tlong si attr)
| ptr_ptr (b ofs ty attr)  : val_casted (Vptr b ofs) (Tpointer ty attr)
| int_ptr (n ty attr)      : ¬ archi.ptr64 → val_casted (Vint n) (Tpointer ty attr)
| ptr_int (b ofs si attr)  : ¬ archi.ptr64 → val_casted (Vptr b ofs) (Tint I32 si attr)
| long_ptr (n ty attr)     : archi.ptr64 → val_casted (Vlong n) (Tpointer ty attr)
| ptr_long (b ofs si attr) : archi.ptr64 → val_casted (Vptr b ofs) (Tlong si attr)
| struct (id attr b ofs)   : val_casted (Vptr b ofs) (Tstruct id attr)
| union (id attr b ofs)    : val_casted (Vptr b ofs) (Tunion id attr)
| void (v)                 : val_casted v Tvoid

theorem cast_int_int_idem (sz sg i) :
  cast_int_int sz sg (cast_int_int sz sg i) = cast_int_int sz sg i := sorry'

lemma cast_val_is_casted {v ty ty' v' m} :
  sem_cast v ty ty' m = some v' → val_casted v' ty' := sorry'

end val_casted

/- As a consequence, casting twice is equivalent to casting once. -/

lemma cast_val_casted {m v ty} :
  val_casted v ty → sem_cast m v ty ty = some v := sorry'

lemma cast_idempotent {m v ty ty' v'} :
  sem_cast m v ty ty' = some v' → sem_cast m v' ty' ty' = some v' := sorry'

/- Relation with the arithmetic conversions of ISO C99, section 6.3.1 -/

section arith_conv

/- This is the ISO C algebra of arithmetic types, without qualifiers.
    [S] stands for "signed" and [U] for "unsigned".  -/

inductive int_type : Type
| Bool
| Char | SChar | UChar
| Short | UShort
| Int | UInt
| Long | ULong
| Longlong | ULonglong
open int_type

inductive arith_type : Type
| I (it : int_type)
| Float
| Double
| Longdouble
open arith_type

instance eq_int_type : decidable_eq int_type := by tactic.mk_dec_eq_instance


def is_unsigned : int_type → bool
| Bool      := tt
| UChar     := tt
| UShort    := tt
| UInt      := tt
| ULong     := tt
| ULonglong := tt
| _         := ff

def unsigned_type : int_type → int_type
| Char     := UChar
| SChar    := UChar
| Short    := UShort
| Int      := UInt
| Long     := ULong
| Longlong := ULonglong
| t        := t

def int_sizeof : int_type → ℕ
| Bool      := 1
| Char      := 1
| SChar     := 1
| UChar     := 1
| Short     := 2
| UShort    := 2
| Int       := 4
| UInt      := 4
| Long      := 4
| ULong     := 4
| Longlong  := 8
| ULonglong := 8

/- 6.3.1.1 para 1: integer conversion rank -/

def rank : int_type → ℕ
| Bool      := 1
| Char      := 2
| SChar     := 2
| UChar     := 2
| Short     := 3
| UShort    := 3
| Int       := 4
| UInt      := 4
| Long      := 5
| ULong     := 5
| Longlong  := 6
| ULonglong := 6

/- 6.3.1.1 para 2: integer promotions, a.k.a. usual unary conversions -/

def integer_promotion (t : int_type) : int_type :=
if rank t < rank Int then Int else t

/- 6.3.1.8: Usual arithmetic conversions, a.k.a. binary conversions.
  This function returns the type to which the two operands must be
  converted. -/

def usual_arithmetic_conversion : arith_type → arith_type → arith_type
  /- First, if the corresponding real type of either operand is long
     double, the other operand is converted, without change of type domain,
     to a type whose corresponding real type is long double. -/
| Longdouble _ := Longdouble
| _ Longdouble := Longdouble
  /- Otherwise, if the corresponding real type of either operand is
     double, the other operand is converted, without change of type domain,
     to a type whose corresponding real type is double. -/
| Double _ := Double
| _ Double := Double
  /- Otherwise, if the corresponding real type of either operand is
     float, the other operand is converted, without change of type domain,
     to a type whose corresponding real type is float. -/
| Float _ := Float
| _ Float := Float
  /- Otherwise, the integer promotions are performed on both operands. -/
| (I i1) (I i2) :=
    let j1 := integer_promotion i1, j2 := integer_promotion i2 in
    /- Then the following rules are applied to the promoted operands:
       If both operands have the same type, then no further conversion
       is needed. -/
    if j1 = j2 then I j1 else
    match is_unsigned j1, is_unsigned j2 with
    /- Otherwise, if both operands have signed integer types or both
       have unsigned integer types, the operand with the type of lesser
       integer conversion rank is converted to the type of the operand with
       greater rank. -/
    | tt, tt := if rank j1 < rank j2 then I j2 else I j1
    | ff, ff := if rank j1 < rank j2 then I j2 else I j1
    | tt, ff :=
    /- Otherwise, if the operand that has unsigned integer type has
       rank greater or equal to the rank of the type of the other operand,
       then the operand with signed integer type is converted to the type of
       the operand with unsigned integer type. -/
        if rank j2 ≤ rank j1 then I j1 else
    /- Otherwise, if the type of the operand with signed integer type
       can represent all of the values of the type of the operand with
       unsigned integer type, then the operand with unsigned integer type is
       converted to the type of the operand with signed integer type. -/
        if int_sizeof j1 < int_sizeof j2 then I j2 else
    /- Otherwise, both operands are converted to the unsigned integer type
       corresponding to the type of the operand with signed integer type. -/
        I (unsigned_type j2)
    | ff, tt :=
    /- Same logic as above, swapping the roles of j1 and j2 -/
        if rank j1 ≤ rank j2 then I j2 else
        if int_sizeof j2 < int_sizeof j1 then I j1 else
        I (unsigned_type j1)
    end

/- Mapping ISO arithmetic types to CompCert types -/

def proj_type : arith_type → type
| (I Bool)      := Tint IBool Unsigned noattr
| (I Char)      := Tint I8 Unsigned noattr
| (I SChar)     := Tint I8 Signed noattr
| (I UChar)     := Tint I8 Unsigned noattr
| (I Short)     := Tint I16 Signed noattr
| (I UShort)    := Tint I16 Unsigned noattr
| (I Int)       := Tint I32 Signed noattr
| (I UInt)      := Tint I32 Unsigned noattr
| (I Long)      := Tint I32 Signed noattr
| (I ULong)     := Tint I32 Unsigned noattr
| (I Longlong)  := Tlong Signed noattr
| (I ULonglong) := Tlong Unsigned noattr
| Float         := Tfloat F32 noattr
| Double        := Tfloat F64 noattr
| Longdouble    := Tfloat F64 noattr

/- Relation between [typeconv] and integer promotion. -/

lemma typeconv_integer_promotion (i) :
  typeconv (proj_type (I i)) = proj_type (I (integer_promotion i)) := sorry'

/- Relation between [classify_binarith] and arithmetic conversion. -/

lemma classify_binarith_arithmetic_conversion (t1 t2) :
  binarith_type (classify_binarith (proj_type t1) (proj_type t2)) =
  proj_type (usual_arithmetic_conversion t1 t2) := sorry'

end arith_conv

end cop
