/- ********************************************************************-/
/-                                                                     -/
/-              The Compcert verified compiler                         -/
/-                                                                     -/
/-          Xavier Leroy, INRIA Paris-Rocquencourt                     -/
/-                                                                     -/
/-  Copyright Institut National de Recherche en Informatique et en     -/
/-  Automatique.  All rights reserved.  This file is distributed       -/
/-  under the terms of the GNU General Public License as published by  -/
/-  the Free Software Foundation, either version 2 of the License, or  -/
/-  (at your option) any later version.  This file is also distributed -/
/-  under the terms of the INRIA Non-Commercial License Agreement.     -/
/-                                                                     -/
/- ********************************************************************-/

/- This module defines the type of values that is used in the dynamic
  semantics of all our intermediate languages. -/

import .lib .integers

namespace values
open integers

def block : Type := pos_num
instance eq_block : decidable_eq block := by tactic.mk_dec_eq_instance

/- A value is either:
- a machine integer;
- a floating-point number;
- a pointer: a pair of a memory address and an integer offset with respect
  to this address;
- the [Vundef] value denoting an arbitrary bit pattern, such as the
  value of an uninitialized variable.
-/

inductive val : Type
| Vundef : val
| Vint : int32 → val
| Vlong : int64 → val
| Vfloat : float → val
| Vsingle : float32 → val
| Vptr : block → ptrofs → val
open val

def Vzero : val := Vint Int.zero
def Vone : val := Vint Int.one
def Vmone : val := Vint Int.mone

def Vtrue : val := Vint Int.one
def Vfalse : val := Vint Int.zero

def Vnullptr :=
  if Archi.ptr64 then Vlong Int64.zero else Vint Int.zero

def Vptrofs (n : ptrofs) :=
  if Archi.ptr64 then Vlong (Ptrofs.to_int64 n) else Vint (Ptrofs.to_int n)

/- * Operations over values -/

/- The module [Val] defines a number of arithmetic and logical operations
  over type [val].  Most of these operations are straightforward extensions
  of the corresponding integer or floating-point operations. -/

Module Val

def eq (x y : val) : {x=y} + {x≠y}
Proof
  decide equality
  apply Int.eq_dec
  apply Int64.eq_dec
  apply Float.eq_dec
  apply Float32.eq_dec
  apply Ptrofs.eq_dec
  apply eq_block
Defined
Global Opaque eq

def has_type (v : val) (t : typ) : Prop :=
  match v, t with
| Vundef, _ := true
| Vint _, Tint := true
| Vlong _, Tlong := true
| Vfloat _, Tfloat := true
| Vsingle _, Tsingle := true
| Vptr _ _, Tint := Archi.ptr64 = ff
| Vptr _ _, Tlong := Archi.ptr64 = tt
| (Vint _ | Vsingle _), Tany32 := true
| Vptr _ _, Tany32 := Archi.ptr64 = ff
| _, Tany64 := true
| _, _ := false
  end

def has_type_list (vl : list val) (tl : list typ) {struct vl} : Prop :=
  match vl, tl with
| nil, nil := true
| v1 :: vs, t1 :: ts := has_type v1 t1 ∧ has_type_list vs ts
| _, _ := false
  end

def has_opttype (v : val) (ot : option typ) : Prop :=
  match ot with
| none := v = Vundef
| some t := has_type v t
  end

lemma Vptr_has_type :
  ∀ b ofs, has_type (Vptr b ofs) Tptr
Proof
  intros. unfold Tptr, has_type; destruct Archi.ptr64; reflexivity
Qed

lemma Vnullptr_has_type :
  has_type Vnullptr Tptr
Proof
  unfold has_type, Vnullptr, Tptr; destruct Archi.ptr64; reflexivity
Qed

lemma has_subtype :
  ∀ ty1 ty2 v,
  subtype ty1 ty2 = tt → has_type v ty1 → has_type v ty2
Proof
  intros. destruct ty1; destruct ty2; simpl in H;
  (contradiction || discriminate || assumption || idtac);
  unfold has_type in *; destruct v; auto; contradiction
Qed

lemma has_subtype_list :
  ∀ tyl1 tyl2 vl,
  subtype_list tyl1 tyl2 = tt → has_type_list vl tyl1 → has_type_list vl tyl2
Proof
  induction tyl1; intros; destruct tyl2; try discriminate; destruct vl; try contradiction
  red; auto
  simpl in *. InvBooleans. destruct H0. split; auto. eapply has_subtype; eauto
Qed

/- Truth values.  Non-zero integers are treated as [True].
  The integer 0 (also used to represent the null pointer) is [False].
  Other values are neither true nor false. -/

inductive bool_of_val : val → bool → Prop :=
| bool_of_val_int :
      ∀ n, bool_of_val (Vint n) (negb (Int.eq n Int.zero))

/- Arithmetic operations -/

def neg (v : val) : val :=
  match v with
| Vint n := Vint (Int.neg n)
| _ := Vundef
  end

def negf (v : val) : val :=
  match v with
| Vfloat f := Vfloat (Float.neg f)
| _ := Vundef
  end

def absf (v : val) : val :=
  match v with
| Vfloat f := Vfloat (Float.abs f)
| _ := Vundef
  end

def negfs (v : val) : val :=
  match v with
| Vsingle f := Vsingle (Float32.neg f)
| _ := Vundef
  end

def absfs (v : val) : val :=
  match v with
| Vsingle f := Vsingle (Float32.abs f)
| _ := Vundef
  end

def maketotal (ov : option val) : val :=
  match ov with some v := v | none := Vundef end

def intoffloat (v : val) : option val :=
  match v with
| Vfloat f := option_map Vint (Float.to_int f)
| _ := none
  end

def intuoffloat (v : val) : option val :=
  match v with
| Vfloat f := option_map Vint (Float.to_intu f)
| _ := none
  end

def floatofint (v : val) : option val :=
  match v with
| Vint n := some (Vfloat (Float.of_int n))
| _ := none
  end

def floatofintu (v : val) : option val :=
  match v with
| Vint n := some (Vfloat (Float.of_intu n))
| _ := none
  end

def intofsingle (v : val) : option val :=
  match v with
| Vsingle f := option_map Vint (Float32.to_int f)
| _ := none
  end

def intuofsingle (v : val) : option val :=
  match v with
| Vsingle f := option_map Vint (Float32.to_intu f)
| _ := none
  end

def singleofint (v : val) : option val :=
  match v with
| Vint n := some (Vsingle (Float32.of_int n))
| _ := none
  end

def singleofintu (v : val) : option val :=
  match v with
| Vint n := some (Vsingle (Float32.of_intu n))
| _ := none
  end

def negint (v : val) : val :=
  match v with
| Vint n := Vint (Int.neg n)
| _ := Vundef
  end

def notint (v : val) : val :=
  match v with
| Vint n := Vint (Int.not n)
| _ := Vundef
  end

def of_bool (b : bool) : val := if b then Vtrue else Vfalse

def boolval (v : val) : val :=
  match v with
| Vint n := of_bool (negb (Int.eq n Int.zero))
| Vptr b ofs := Vtrue
| _ := Vundef
  end

def notbool (v : val) : val :=
  match v with
| Vint n := of_bool (Int.eq n Int.zero)
| Vptr b ofs := Vfalse
| _ := Vundef
  end

def zero_ext (nbits : ℤ) (v : val) : val :=
  match v with
| Vint n := Vint(Int.zero_ext nbits n)
| _ := Vundef
  end

def sign_ext (nbits : ℤ) (v : val) : val :=
  match v with
| Vint n := Vint(Int.sign_ext nbits n)
| _ := Vundef
  end

def singleoffloat (v : val) : val :=
  match v with
| Vfloat f := Vsingle (Float.to_single f)
| _ := Vundef
  end

def floatofsingle (v : val) : val :=
  match v with
| Vsingle f := Vfloat (Float.of_single f)
| _ := Vundef
  end

def add (v1 v2 : val) : val :=
  match v1, v2 with
| Vint n1, Vint n2 := Vint(Int.add n1 n2)
| Vptr b1 ofs1, Vint n2 := if Archi.ptr64 then Vundef else Vptr b1 (Ptrofs.add ofs1 (Ptrofs.of_int n2))
| Vint n1, Vptr b2 ofs2 := if Archi.ptr64 then Vundef else Vptr b2 (Ptrofs.add ofs2 (Ptrofs.of_int n1))
| _, _ := Vundef
  end

def sub (v1 v2 : val) : val :=
  match v1, v2 with
| Vint n1, Vint n2 := Vint(Int.sub n1 n2)
| Vptr b1 ofs1, Vint n2 := if Archi.ptr64 then Vundef else Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.of_int n2))
| Vptr b1 ofs1, Vptr b2 ofs2 :=
      if Archi.ptr64 then Vundef else
      if eq_block b1 b2 then Vint(Ptrofs.to_int (Ptrofs.sub ofs1 ofs2)) else Vundef
| _, _ := Vundef
  end

def mul (v1 v2 : val) : val :=
  match v1, v2 with
| Vint n1, Vint n2 := Vint(Int.mul n1 n2)
| _, _ := Vundef
  end

def mulhs (v1 v2 : val) : val :=
  match v1, v2 with
| Vint n1, Vint n2 := Vint(Int.mulhs n1 n2)
| _, _ := Vundef
  end

def mulhu (v1 v2 : val) : val :=
  match v1, v2 with
| Vint n1, Vint n2 := Vint(Int.mulhu n1 n2)
| _, _ := Vundef
  end

def divs (v1 v2 : val) : option val :=
  match v1, v2 with
| Vint n1, Vint n2 :=
      if Int.eq n2 Int.zero
      || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
      then none
      else some(Vint(Int.divs n1 n2))
| _, _ := none
  end

def mods (v1 v2 : val) : option val :=
  match v1, v2 with
| Vint n1, Vint n2 :=
      if Int.eq n2 Int.zero
      || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
      then none
      else some(Vint(Int.mods n1 n2))
| _, _ := none
  end

def divu (v1 v2 : val) : option val :=
  match v1, v2 with
| Vint n1, Vint n2 :=
      if Int.eq n2 Int.zero then none else some(Vint(Int.divu n1 n2))
| _, _ := none
  end

def modu (v1 v2 : val) : option val :=
  match v1, v2 with
| Vint n1, Vint n2 :=
      if Int.eq n2 Int.zero then none else some(Vint(Int.modu n1 n2))
| _, _ := none
  end

def add_carry (v1 v2 cin : val) : val :=
  match v1, v2, cin with
| Vint n1, Vint n2, Vint c := Vint(Int.add_carry n1 n2 c)
| _, _, _ := Vundef
  end

def sub_overflow (v1 v2 : val) : val :=
  match v1, v2 with
| Vint n1, Vint n2 := Vint(Int.sub_overflow n1 n2 Int.zero)
| _, _ := Vundef
  end

def negative (v : val) : val :=
  match v with
| Vint n := Vint (Int.negative n)
| _ := Vundef
  end

def and (v1 v2 : val) : val :=
  match v1, v2 with
| Vint n1, Vint n2 := Vint(Int.and n1 n2)
| _, _ := Vundef
  end

def or (v1 v2 : val) : val :=
  match v1, v2 with
| Vint n1, Vint n2 := Vint(Int.or n1 n2)
| _, _ := Vundef
  end

def xor (v1 v2 : val) : val :=
  match v1, v2 with
| Vint n1, Vint n2 := Vint(Int.xor n1 n2)
| _, _ := Vundef
  end

def shl (v1 v2 : val) : val :=
  match v1, v2 with
| Vint n1, Vint n2 :=
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shl n1 n2)
     else Vundef
| _, _ := Vundef
  end

def shr (v1 v2 : val) : val :=
  match v1, v2 with
| Vint n1, Vint n2 :=
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shr n1 n2)
     else Vundef
| _, _ := Vundef
  end

def shr_carry (v1 v2 : val) : val :=
  match v1, v2 with
| Vint n1, Vint n2 :=
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shr_carry n1 n2)
     else Vundef
| _, _ := Vundef
  end

def shrx (v1 v2 : val) : option val :=
  match v1, v2 with
| Vint n1, Vint n2 :=
     if Int.ltu n2 (Int.repr 31)
     then some(Vint(Int.shrx n1 n2))
     else none
| _, _ := none
  end

def shru (v1 v2 : val) : val :=
  match v1, v2 with
| Vint n1, Vint n2 :=
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shru n1 n2)
     else Vundef
| _, _ := Vundef
  end

def rol (v1 v2 : val) : val :=
  match v1, v2 with
| Vint n1, Vint n2 := Vint(Int.rol n1 n2)
| _, _ := Vundef
  end

def rolm (v : val) (amount mask : int) : val :=
  match v with
| Vint n := Vint(Int.rolm n amount mask)
| _ := Vundef
  end

def ror (v1 v2 : val) : val :=
  match v1, v2 with
| Vint n1, Vint n2 := Vint(Int.ror n1 n2)
| _, _ := Vundef
  end

def addf (v1 v2 : val) : val :=
  match v1, v2 with
| Vfloat f1, Vfloat f2 := Vfloat(Float.add f1 f2)
| _, _ := Vundef
  end

def subf (v1 v2 : val) : val :=
  match v1, v2 with
| Vfloat f1, Vfloat f2 := Vfloat(Float.sub f1 f2)
| _, _ := Vundef
  end

def mulf (v1 v2 : val) : val :=
  match v1, v2 with
| Vfloat f1, Vfloat f2 := Vfloat(Float.mul f1 f2)
| _, _ := Vundef
  end

def divf (v1 v2 : val) : val :=
  match v1, v2 with
| Vfloat f1, Vfloat f2 := Vfloat(Float.div f1 f2)
| _, _ := Vundef
  end

def floatofwords (v1 v2 : val) : val :=
  match v1, v2 with
| Vint n1, Vint n2 := Vfloat (Float.from_words n1 n2)
| _, _ := Vundef
  end

def addfs (v1 v2 : val) : val :=
  match v1, v2 with
| Vsingle f1, Vsingle f2 := Vsingle(Float32.add f1 f2)
| _, _ := Vundef
  end

def subfs (v1 v2 : val) : val :=
  match v1, v2 with
| Vsingle f1, Vsingle f2 := Vsingle(Float32.sub f1 f2)
| _, _ := Vundef
  end

def mulfs (v1 v2 : val) : val :=
  match v1, v2 with
| Vsingle f1, Vsingle f2 := Vsingle(Float32.mul f1 f2)
| _, _ := Vundef
  end

def divfs (v1 v2 : val) : val :=
  match v1, v2 with
| Vsingle f1, Vsingle f2 := Vsingle(Float32.div f1 f2)
| _, _ := Vundef
  end

/- Operations on 64-bit integers -/

def longofwords (v1 v2 : val) : val :=
  match v1, v2 with
| Vint n1, Vint n2 := Vlong (Int64.ofwords n1 n2)
| _, _ := Vundef
  end

def loword (v : val) : val :=
  match v with
| Vlong n  := Vint (Int64.loword n)
| _ := Vundef
  end

def hiword (v : val) : val :=
  match v with
| Vlong n  := Vint (Int64.hiword n)
| _ := Vundef
  end

def negl (v : val) : val :=
  match v with
| Vlong n := Vlong (Int64.neg n)
| _ := Vundef
  end

def notl (v : val) : val :=
  match v with
| Vlong n := Vlong (Int64.not n)
| _ := Vundef
  end

def longofint (v : val) : val :=
  match v with
| Vint n := Vlong (Int64.repr (Int.signed n))
| _ := Vundef
  end

def longofintu (v : val) : val :=
  match v with
| Vint n := Vlong (Int64.repr (Int.unsigned n))
| _ := Vundef
  end

def longoffloat (v : val) : option val :=
  match v with
| Vfloat f := option_map Vlong (Float.to_long f)
| _ := none
  end

def longuoffloat (v : val) : option val :=
  match v with
| Vfloat f := option_map Vlong (Float.to_longu f)
| _ := none
  end

def longofsingle (v : val) : option val :=
  match v with
| Vsingle f := option_map Vlong (Float32.to_long f)
| _ := none
  end

def longuofsingle (v : val) : option val :=
  match v with
| Vsingle f := option_map Vlong (Float32.to_longu f)
| _ := none
  end

def floatoflong (v : val) : option val :=
  match v with
| Vlong n := some (Vfloat (Float.of_long n))
| _ := none
  end

def floatoflongu (v : val) : option val :=
  match v with
| Vlong n := some (Vfloat (Float.of_longu n))
| _ := none
  end

def singleoflong (v : val) : option val :=
  match v with
| Vlong n := some (Vsingle (Float32.of_long n))
| _ := none
  end

def singleoflongu (v : val) : option val :=
  match v with
| Vlong n := some (Vsingle (Float32.of_longu n))
| _ := none
  end

def addl (v1 v2 : val) : val :=
  match v1, v2 with
| Vlong n1, Vlong n2 := Vlong(Int64.add n1 n2)
| Vptr b1 ofs1, Vlong n2 := if Archi.ptr64 then Vptr b1 (Ptrofs.add ofs1 (Ptrofs.of_int64 n2)) else Vundef
| Vlong n1, Vptr b2 ofs2 := if Archi.ptr64 then Vptr b2 (Ptrofs.add ofs2 (Ptrofs.of_int64 n1)) else Vundef
| _, _ := Vundef
  end

def subl (v1 v2 : val) : val :=
  match v1, v2 with
| Vlong n1, Vlong n2 := Vlong(Int64.sub n1 n2)
| Vptr b1 ofs1, Vlong n2 :=
      if Archi.ptr64 then Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.of_int64 n2)) else Vundef
| Vptr b1 ofs1, Vptr b2 ofs2 :=
      if negb Archi.ptr64 then Vundef else
      if eq_block b1 b2 then Vlong(Ptrofs.to_int64 (Ptrofs.sub ofs1 ofs2)) else Vundef
| _, _ := Vundef
  end

def mull (v1 v2 : val) : val :=
  match v1, v2 with
| Vlong n1, Vlong n2 := Vlong(Int64.mul n1 n2)
| _, _ := Vundef
  end

def mull' (v1 v2 : val) : val :=
  match v1, v2 with
| Vint n1, Vint n2 := Vlong(Int64.mul' n1 n2)
| _, _ := Vundef
  end

def mullhs (v1 v2 : val) : val :=
  match v1, v2 with
| Vlong n1, Vlong n2 := Vlong(Int64.mulhs n1 n2)
| _, _ := Vundef
  end

def mullhu (v1 v2 : val) : val :=
  match v1, v2 with
| Vlong n1, Vlong n2 := Vlong(Int64.mulhu n1 n2)
| _, _ := Vundef
  end

def divls (v1 v2 : val) : option val :=
  match v1, v2 with
| Vlong n1, Vlong n2 :=
      if Int64.eq n2 Int64.zero
      || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
      then none
      else some(Vlong(Int64.divs n1 n2))
| _, _ := none
  end

def modls (v1 v2 : val) : option val :=
  match v1, v2 with
| Vlong n1, Vlong n2 :=
      if Int64.eq n2 Int64.zero
      || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
      then none
      else some(Vlong(Int64.mods n1 n2))
| _, _ := none
  end

def divlu (v1 v2 : val) : option val :=
  match v1, v2 with
| Vlong n1, Vlong n2 :=
      if Int64.eq n2 Int64.zero then none else some(Vlong(Int64.divu n1 n2))
| _, _ := none
  end

def modlu (v1 v2 : val) : option val :=
  match v1, v2 with
| Vlong n1, Vlong n2 :=
      if Int64.eq n2 Int64.zero then none else some(Vlong(Int64.modu n1 n2))
| _, _ := none
  end

def subl_overflow (v1 v2 : val) : val :=
  match v1, v2 with
| Vlong n1, Vlong n2 := Vint (Int.repr (Int64.unsigned (Int64.sub_overflow n1 n2 Int64.zero)))
| _, _ := Vundef
  end

def negativel (v : val) : val :=
  match v with
| Vlong n := Vint (Int.repr (Int64.unsigned (Int64.negative n)))
| _ := Vundef
  end

def andl (v1 v2 : val) : val :=
  match v1, v2 with
| Vlong n1, Vlong n2 := Vlong(Int64.and n1 n2)
| _, _ := Vundef
  end

def orl (v1 v2 : val) : val :=
  match v1, v2 with
| Vlong n1, Vlong n2 := Vlong(Int64.or n1 n2)
| _, _ := Vundef
  end

def xorl (v1 v2 : val) : val :=
  match v1, v2 with
| Vlong n1, Vlong n2 := Vlong(Int64.xor n1 n2)
| _, _ := Vundef
  end

def shll (v1 v2 : val) : val :=
  match v1, v2 with
| Vlong n1, Vint n2 :=
     if Int.ltu n2 Int64.iwordsize'
     then Vlong(Int64.shl' n1 n2)
     else Vundef
| _, _ := Vundef
  end

def shrl (v1 v2 : val) : val :=
  match v1, v2 with
| Vlong n1, Vint n2 :=
     if Int.ltu n2 Int64.iwordsize'
     then Vlong(Int64.shr' n1 n2)
     else Vundef
| _, _ := Vundef
  end

def shrlu (v1 v2 : val) : val :=
  match v1, v2 with
| Vlong n1, Vint n2 :=
     if Int.ltu n2 Int64.iwordsize'
     then Vlong(Int64.shru' n1 n2)
     else Vundef
| _, _ := Vundef
  end

def shrxl (v1 v2 : val) : option val :=
  match v1, v2 with
| Vlong n1, Vint n2 :=
     if Int.ltu n2 (Int.repr 63)
     then some(Vlong(Int64.shrx' n1 n2))
     else none
| _, _ := none
  end

def roll (v1 v2 : val) : val :=
  match v1, v2 with
| Vlong n1, Vint n2 := Vlong(Int64.rol n1 (Int64.repr (Int.unsigned n2)))
| _, _ := Vundef
  end

def rorl (v1 v2 : val) : val :=
  match v1, v2 with
| Vlong n1, Vint n2 := Vlong(Int64.ror n1 (Int64.repr (Int.unsigned n2)))
| _, _ := Vundef
  end

def rolml (v : val) (amount mask : int64) : val :=
  match v with
| Vlong n := Vlong(Int64.rolm n amount mask)
| _ := Vundef
  end

/- Comparisons -/

section COMPARISONS

parameter valid_ptr : block → ℤ → bool
def weak_valid_ptr (b : block) (ofs : ℤ) := valid_ptr b ofs || valid_ptr b (ofs - 1)

def cmp_bool (c : comparison) (v1 v2 : val) : option bool :=
  match v1, v2 with
| Vint n1, Vint n2 := some (Int.cmp c n1 n2)
| _, _ := none
  end

def cmp_different_blocks (c : comparison) : option bool :=
  match c with
| Ceq := some ff
| Cne := some tt
| _   := none
  end

def cmpu_bool (c : comparison) (v1 v2 : val) : option bool :=
  match v1, v2 with
| Vint n1, Vint n2 :=
      some (Int.cmpu c n1 n2)
| Vint n1, Vptr b2 ofs2 :=
      if Archi.ptr64 then none else
      if Int.eq n1 Int.zero && weak_valid_ptr b2 (Ptrofs.unsigned ofs2)
      then cmp_different_blocks c
      else none
| Vptr b1 ofs1, Vptr b2 ofs2 :=
      if Archi.ptr64 then none else
      if eq_block b1 b2 then
        if weak_valid_ptr b1 (Ptrofs.unsigned ofs1)
           && weak_valid_ptr b2 (Ptrofs.unsigned ofs2)
        then some (Ptrofs.cmpu c ofs1 ofs2)
        else none
      else
        if valid_ptr b1 (Ptrofs.unsigned ofs1)
           && valid_ptr b2 (Ptrofs.unsigned ofs2)
        then cmp_different_blocks c
        else none
| Vptr b1 ofs1, Vint n2 :=
      if Archi.ptr64 then none else
      if Int.eq n2 Int.zero && weak_valid_ptr b1 (Ptrofs.unsigned ofs1)
      then cmp_different_blocks c
      else none
| _, _ := none
  end

def cmpf_bool (c : comparison) (v1 v2 : val) : option bool :=
  match v1, v2 with
| Vfloat f1, Vfloat f2 := some (Float.cmp c f1 f2)
| _, _ := none
  end

def cmpfs_bool (c : comparison) (v1 v2 : val) : option bool :=
  match v1, v2 with
| Vsingle f1, Vsingle f2 := some (Float32.cmp c f1 f2)
| _, _ := none
  end

def cmpl_bool (c : comparison) (v1 v2 : val) : option bool :=
  match v1, v2 with
| Vlong n1, Vlong n2 := some (Int64.cmp c n1 n2)
| _, _ := none
  end

def cmplu_bool (c : comparison) (v1 v2 : val) : option bool :=
  match v1, v2 with
| Vlong n1, Vlong n2 := some (Int64.cmpu c n1 n2)
| Vlong n1, Vptr b2 ofs2 :=
      if negb Archi.ptr64 then none else
      if Int64.eq n1 Int64.zero && weak_valid_ptr b2 (Ptrofs.unsigned ofs2)
      then cmp_different_blocks c
      else none
| Vptr b1 ofs1, Vptr b2 ofs2 :=
      if negb Archi.ptr64 then none else
      if eq_block b1 b2 then
        if weak_valid_ptr b1 (Ptrofs.unsigned ofs1)
           && weak_valid_ptr b2 (Ptrofs.unsigned ofs2)
        then some (Ptrofs.cmpu c ofs1 ofs2)
        else none
      else
        if valid_ptr b1 (Ptrofs.unsigned ofs1)
           && valid_ptr b2 (Ptrofs.unsigned ofs2)
        then cmp_different_blocks c
        else none
| Vptr b1 ofs1, Vlong n2 :=
      if negb Archi.ptr64 then none else
      if Int64.eq n2 Int64.zero && weak_valid_ptr b1 (Ptrofs.unsigned ofs1)
      then cmp_different_blocks c
      else none
| _, _ := none
  end

def of_optbool (ob : option bool) : val :=
  match ob with some tt := Vtrue | some ff := Vfalse | none := Vundef end

def cmp (c : comparison) (v1 v2 : val) : val :=
  of_optbool (cmp_bool c v1 v2)

def cmpu (c : comparison) (v1 v2 : val) : val :=
  of_optbool (cmpu_bool c v1 v2)

def cmpf (c : comparison) (v1 v2 : val) : val :=
  of_optbool (cmpf_bool c v1 v2)

def cmpfs (c : comparison) (v1 v2 : val) : val :=
  of_optbool (cmpfs_bool c v1 v2)

def cmpl (c : comparison) (v1 v2 : val) : option val :=
  option_map of_bool (cmpl_bool c v1 v2)

def cmplu (c : comparison) (v1 v2 : val) : option val :=
  option_map of_bool (cmplu_bool c v1 v2)

def maskzero_bool (v : val) (mask : int) : option bool :=
  match v with
| Vint n := some (Int.eq (Int.and n mask) Int.zero)
| _ := none
  end

end COMPARISONS

/- Add the given offset to the given pointer. -/

def offset_ptr (v : val) (delta : ptrofs) : val :=
  match v with
| Vptr b ofs := Vptr b (Ptrofs.add ofs delta)
| _ := Vundef
  end

/- [load_result] reflects the effect of storing a value with a given
  memory chunk, then reading it back with the same chunk.  Depending
  on the chunk and the type of the value, some normalization occurs.
  For instance, consider storing the integer value [0xFFF] on 1 byte
  at a given address, and reading it back.  If it is read back with
  chunk [Mint8unsigned], zero-extension must be performed, resulting
  in [0xFF].  If it is read back as a [Mint8signed], sign-extension is
  performed and [0xFFFFFFFF] is returned. -/

def load_result (chunk : memory_chunk) (v : val) :=
  match chunk, v with
| Mint8signed, Vint n := Vint (Int.sign_ext 8 n)
| Mint8unsigned, Vint n := Vint (Int.zero_ext 8 n)
| Mint16signed, Vint n := Vint (Int.sign_ext 16 n)
| Mint16unsigned, Vint n := Vint (Int.zero_ext 16 n)
| Mint32, Vint n := Vint n
| Mint32, Vptr b ofs := if Archi.ptr64 then Vundef else Vptr b ofs
| Mint64, Vlong n := Vlong n
| Mint64, Vptr b ofs := if Archi.ptr64 then Vptr b ofs else Vundef
| Mfloat32, Vsingle f := Vsingle f
| Mfloat64, Vfloat f := Vfloat f
| Many32, (Vint _ | Vsingle _) := v
| Many32, Vptr _ _ := if Archi.ptr64 then Vundef else v
| Many64, _ := v
| _, _ := Vundef
  end

lemma load_result_type :
  ∀ chunk v, has_type (load_result chunk v) (type_of_chunk chunk)
Proof
  intros. unfold has_type; destruct chunk; destruct v; simpl; auto; destruct Archi.ptr64 eqn:SF; simpl; auto
Qed

lemma load_result_same :
  ∀ v ty, has_type v ty → load_result (chunk_of_type ty) v = v
Proof
  unfold has_type, load_result; intros
  destruct v; destruct ty; destruct Archi.ptr64; try contradiction; try discriminate; auto
Qed

/- Theorems on arithmetic operations. -/

theorem cast8unsigned_and :
  ∀ x, zero_ext 8 x = and x (Vint(Int.repr 255))
Proof
  destruct x; simpl; auto. decEq
  change 255 with (two_p 8 - 1). apply Int.zero_ext_and. omega
Qed

theorem cast16unsigned_and :
  ∀ x, zero_ext 16 x = and x (Vint(Int.repr 65535))
Proof
  destruct x; simpl; auto. decEq
  change 65535 with (two_p 16 - 1). apply Int.zero_ext_and. omega
Qed

theorem bool_of_val_of_bool :
  ∀ b1 b2, bool_of_val (of_bool b1) b2 → b1 = b2
Proof
  intros. destruct b1; simpl in H; inv H; auto
Qed

theorem bool_of_val_of_optbool :
  ∀ ob b, bool_of_val (of_optbool ob) b → ob = some b
Proof
  intros. destruct ob; simpl in H
  destruct b0; simpl in H; inv H; auto
  inv H
Qed

theorem notbool_negb_1 :
  ∀ b, of_bool (negb b) = notbool (of_bool b)
Proof
  destruct b; reflexivity
Qed

theorem notbool_negb_2 :
  ∀ b, of_bool b = notbool (of_bool (negb b))
Proof
  destruct b; reflexivity
Qed

theorem notbool_negb_3 :
  ∀ ob, of_optbool (option_map negb ob) = notbool (of_optbool ob)
Proof
  destruct ob; auto. destruct b; auto
Qed

theorem notbool_idem2 :
  ∀ b, notbool(notbool(of_bool b)) = of_bool b
Proof
  destruct b; reflexivity
Qed

theorem notbool_idem3 :
  ∀ x, notbool(notbool(notbool x)) = notbool x
Proof
  destruct x; simpl; auto
  case (Int.eq i Int.zero); reflexivity
Qed

theorem notbool_idem4 :
  ∀ ob, notbool (notbool (of_optbool ob)) = of_optbool ob
Proof
  destruct ob; auto. destruct b; auto
Qed

theorem add_commut : ∀ x y, add x y = add y x
Proof
  destruct x; destruct y; simpl; auto
  decEq. apply Int.add_commut
Qed

theorem add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
Proof
  unfold add; intros; destruct Archi.ptr64 eqn:SF, x, y, z; simpl; auto
- rewrite Int.add_assoc; auto
- rewrite Int.add_assoc; auto
- rewrite ! Ptrofs.add_assoc. f_equal. f_equal
  rewrite Ptrofs.add_commut. auto with ptrofs
- rewrite ! Ptrofs.add_assoc. f_equal. f_equal
  apply Ptrofs.add_commut
- rewrite ! Ptrofs.add_assoc. f_equal. f_equal
  symmetry. auto with ptrofs
Qed

theorem add_permut : ∀ x y z, add x (add y z) = add y (add x z)
Proof
  intros. rewrite (add_commut y z). rewrite <- add_assoc. apply add_commut
Qed

theorem add_permut_4 :
  ∀ x y z t, add (add x y) (add z t) = add (add x z) (add y t)
Proof
  intros. rewrite add_permut. rewrite add_assoc
  rewrite add_permut. symmetry. apply add_assoc
Qed

theorem neg_zero : neg Vzero = Vzero
Proof
  reflexivity
Qed

theorem neg_add_distr : ∀ x y, neg(add x y) = add (neg x) (neg y)
Proof
  unfold neg, add; intros; destruct Archi.ptr64 eqn:SF, x, y; simpl; auto;
  rewrite Int.neg_add_distr; auto
Qed

theorem sub_zero_r : ∀ x, sub Vzero x = neg x
Proof
  destruct x; simpl; auto
Qed

theorem sub_add_opp : ∀ x y, sub x (Vint y) = add x (Vint (Int.neg y))
Proof
  unfold sub, add; intros; destruct Archi.ptr64 eqn:SF, x; auto
- rewrite Int.sub_add_opp; auto
- rewrite Int.sub_add_opp; auto
- rewrite Ptrofs.sub_add_opp. f_equal. f_equal. symmetry. auto with ptrofs
Qed

theorem sub_opp_add : ∀ x y, sub x (Vint (Int.neg y)) = add x (Vint y)
Proof
  intros. rewrite sub_add_opp. rewrite Int.neg_involutive. auto
Qed

theorem sub_add_l :
  ∀ v1 v2 i, sub (add v1 (Vint i)) v2 = add (sub v1 v2) (Vint i)
Proof
  unfold sub, add; intros; destruct Archi.ptr64 eqn:SF, v1, v2; auto
- rewrite Int.sub_add_l; auto
- rewrite Int.sub_add_l; auto
- rewrite Ptrofs.sub_add_l; auto
- destruct (eq_block b b0); auto
  f_equal. rewrite Ptrofs.sub_add_l. auto with ptrofs
Qed

theorem sub_add_r :
  ∀ v1 v2 i, sub v1 (add v2 (Vint i)) = add (sub v1 v2) (Vint (Int.neg i))
Proof
  unfold sub, add; intros; destruct Archi.ptr64 eqn:SF, v1, v2; auto
- rewrite Int.add_commut. rewrite Int.sub_add_r. auto
- rewrite Int.add_commut. rewrite Int.sub_add_r. auto
- f_equal. replace (Ptrofs.of_int (Int.add i1 i)) with (Ptrofs.add (Ptrofs.of_int i) (Ptrofs.of_int i1))
  rewrite Ptrofs.sub_add_r. f_equal
  symmetry. auto with ptrofs
  symmetry. rewrite Int.add_commut. auto with ptrofs
- destruct (eq_block b b0); auto
  f_equal. rewrite Ptrofs.add_commut. rewrite Ptrofs.sub_add_r. auto with ptrofs. 
Qed

theorem mul_commut : ∀ x y, mul x y = mul y x
Proof
  destruct x; destruct y; simpl; auto. decEq. apply Int.mul_commut
Qed

theorem mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
Proof
  destruct x; destruct y; destruct z; simpl; auto
  decEq. apply Int.mul_assoc
Qed

theorem mul_add_distr_l :
  ∀ x y z, mul (add x y) z = add (mul x z) (mul y z)
Proof
  unfold mul, add; intros; destruct Archi.ptr64 eqn:SF, x, y, z; simpl; auto;
  rewrite Int.mul_add_distr_l; auto
Qed

theorem mul_add_distr_r :
  ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
Proof
  unfold mul, add; intros; destruct Archi.ptr64 eqn:SF, x, y, z; simpl; auto;
  rewrite Int.mul_add_distr_r; auto
Qed

theorem mul_pow2 :
  ∀ x n logn,
  Int.is_power2 n = some logn →
  mul x (Vint n) = shl x (Vint logn)
Proof
  intros; destruct x; simpl; auto
  change 32 with Int.zwordsize
  rewrite (Int.is_power2_range _ _ H). decEq. apply Int.mul_pow2. auto
Qed

theorem mods_divs :
  ∀ x y z,
  mods x y = some z → ∃ v, divs x y = some v ∧ z = sub x (mul v y)
Proof
  intros. destruct x; destruct y; simpl in *; try discriminate
  destruct (Int.eq i0 Int.zero
        || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H
  ∃ (Vint (Int.divs i i0)); split; auto
  simpl. rewrite Int.mods_divs. auto
Qed

theorem modu_divu :
  ∀ x y z,
  modu x y = some z → ∃ v, divu x y = some v ∧ z = sub x (mul v y)
Proof
  intros. destruct x; destruct y; simpl in *; try discriminate
  destruct (Int.eq i0 Int.zero) eqn:?; inv H
  ∃ (Vint (Int.divu i i0)); split; auto
  simpl. rewrite Int.modu_divu. auto
  generalize (Int.eq_spec i0 Int.zero). rewrite Heqb; auto
Qed

theorem divs_pow2 :
  ∀ x n logn y,
  Int.is_power2 n = some logn → Int.ltu logn (Int.repr 31) = tt →
  divs x (Vint n) = some y →
  shrx x (Vint logn) = some y
Proof
  intros; destruct x; simpl in H1; inv H1
  destruct (Int.eq n Int.zero
         || Int.eq i (Int.repr Int.min_signed) && Int.eq n Int.mone); inv H3
  simpl. rewrite H0. decEq. decEq. symmetry. apply Int.divs_pow2. auto
Qed

theorem divu_pow2 :
  ∀ x n logn y,
  Int.is_power2 n = some logn →
  divu x (Vint n) = some y →
  shru x (Vint logn) = y
Proof
  intros; destruct x; simpl in H0; inv H0
  destruct (Int.eq n Int.zero); inv H2
  simpl
  rewrite (Int.is_power2_range _ _ H)
  decEq. symmetry. apply Int.divu_pow2. auto
Qed

theorem modu_pow2 :
  ∀ x n logn y,
  Int.is_power2 n = some logn →
  modu x (Vint n) = some y →
  and x (Vint (Int.sub n Int.one)) = y
Proof
  intros; destruct x; simpl in H0; inv H0
  destruct (Int.eq n Int.zero); inv H2
  simpl. decEq. symmetry. eapply Int.modu_and; eauto
Qed

theorem and_commut : ∀ x y, and x y = and y x
Proof
  destruct x; destruct y; simpl; auto. decEq. apply Int.and_commut
Qed

theorem and_assoc : ∀ x y z, and (and x y) z = and x (and y z)
Proof
  destruct x; destruct y; destruct z; simpl; auto
  decEq. apply Int.and_assoc
Qed

theorem or_commut : ∀ x y, or x y = or y x
Proof
  destruct x; destruct y; simpl; auto. decEq. apply Int.or_commut
Qed

theorem or_assoc : ∀ x y z, or (or x y) z = or x (or y z)
Proof
  destruct x; destruct y; destruct z; simpl; auto
  decEq. apply Int.or_assoc
Qed

theorem xor_commut : ∀ x y, xor x y = xor y x
Proof
  destruct x; destruct y; simpl; auto. decEq. apply Int.xor_commut
Qed

theorem xor_assoc : ∀ x y z, xor (xor x y) z = xor x (xor y z)
Proof
  destruct x; destruct y; destruct z; simpl; auto
  decEq. apply Int.xor_assoc
Qed

theorem not_xor : ∀ x, notint x = xor x (Vint Int.mone)
Proof
  destruct x; simpl; auto
Qed

theorem shl_mul : ∀ x y, mul x (shl Vone y) = shl x y
Proof
  destruct x; destruct y; simpl; auto
  case (Int.ltu i0 Int.iwordsize); auto
  decEq. symmetry. apply Int.shl_mul
Qed

theorem shl_rolm :
  ∀ x n,
  Int.ltu n Int.iwordsize = tt →
  shl x (Vint n) = rolm x n (Int.shl Int.mone n)
Proof
  intros; destruct x; simpl; auto
  rewrite H. decEq. apply Int.shl_rolm. exact H
Qed

theorem shru_rolm :
  ∀ x n,
  Int.ltu n Int.iwordsize = tt →
  shru x (Vint n) = rolm x (Int.sub Int.iwordsize n) (Int.shru Int.mone n)
Proof
  intros; destruct x; simpl; auto
  rewrite H. decEq. apply Int.shru_rolm. exact H
Qed

theorem shrx_carry :
  ∀ x y z,
  shrx x y = some z →
  add (shr x y) (shr_carry x y) = z
Proof
  intros. destruct x; destruct y; simpl in H; inv H
  destruct (Int.ltu i0 (Int.repr 31)) eqn:?; inv H1
  exploit Int.ltu_inv; eauto. change (Int.unsigned (Int.repr 31)) with 31. intros
  assert (Int.ltu i0 Int.iwordsize = tt)
    unfold Int.ltu. apply zlt_true. change (Int.unsigned Int.iwordsize) with 32. omega
  simpl. rewrite H0. simpl. decEq. rewrite Int.shrx_carry; auto
Qed

theorem shrx_shr :
  ∀ x y z,
  shrx x y = some z →
  ∃ p, ∃ q,
    x = Vint p ∧ y = Vint q ∧
    z = shr (if Int.lt p Int.zero then add x (Vint (Int.sub (Int.shl Int.one q) Int.one)) else x) (Vint q)
Proof
  intros. destruct x; destruct y; simpl in H; inv H
  destruct (Int.ltu i0 (Int.repr 31)) eqn:?; inv H1
  exploit Int.ltu_inv; eauto. change (Int.unsigned (Int.repr 31)) with 31. intros
  assert (Int.ltu i0 Int.iwordsize = tt)
    unfold Int.ltu. apply zlt_true. change (Int.unsigned Int.iwordsize) with 32. omega
  ∃ i; ∃ i0; intuition
  rewrite Int.shrx_shr; auto. destruct (Int.lt i Int.zero); simpl; rewrite H0; auto
Qed

theorem shrx_shr_2 :
  ∀ n x z,
  shrx x (Vint n) = some z →
  z = (if Int.eq n Int.zero then x else
         shr (add x (shru (shr x (Vint (Int.repr 31)))
                    (Vint (Int.sub (Int.repr 32) n))))
             (Vint n))
Proof
  intros. destruct x; simpl in H; try discriminate
  destruct (Int.ltu n (Int.repr 31)) eqn:LT; inv H
  exploit Int.ltu_inv; eauto. change (Int.unsigned (Int.repr 31)) with 31; intros LT'
  predSpec Int.eq Int.eq_spec n Int.zero
- subst n. unfold Int.shrx. rewrite Int.shl_zero. unfold Int.divs. change (Int.signed Int.one) with 1
  rewrite ℤ.quot_1_r. rewrite Int.repr_signed; auto
- simpl. change (Int.ltu (Int.repr 31) Int.iwordsize) with tt. simpl
  replace (Int.ltu (Int.sub (Int.repr 32) n) Int.iwordsize) with tt. simpl
  replace (Int.ltu n Int.iwordsize) with tt
  f_equal; apply Int.shrx_shr_2; assumption
  symmetry; apply zlt_true. change (Int.unsigned n < 32); omega
  symmetry; apply zlt_true. unfold Int.sub. change (Int.unsigned (Int.repr 32)) with 32
  assert (Int.unsigned n ≠ 0). { red; intros; elim H. rewrite <- (Int.repr_unsigned n), H0. auto. }
  rewrite Int.unsigned_repr. 
  change (Int.unsigned Int.iwordsize) with 32; omega
  assert (32 < Int.max_unsigned) by reflexivity. omega
Qed

theorem or_rolm :
  ∀ x n m1 m2,
  or (rolm x n m1) (rolm x n m2) = rolm x n (Int.or m1 m2)
Proof
  intros; destruct x; simpl; auto
  decEq. apply Int.or_rolm
Qed

theorem rolm_rolm :
  ∀ x n1 m1 n2 m2,
  rolm (rolm x n1 m1) n2 m2 =
    rolm x (Int.modu (Int.add n1 n2) Int.iwordsize)
           (Int.and (Int.rol m1 n2) m2)
Proof
  intros; destruct x; simpl; auto
  decEq
  apply Int.rolm_rolm. apply int_wordsize_divides_modulus
Qed

theorem rolm_zero :
  ∀ x m,
  rolm x Int.zero m = and x (Vint m)
Proof
  intros; destruct x; simpl; auto. decEq. apply Int.rolm_zero
Qed

theorem addl_commut : ∀ x y, addl x y = addl y x
Proof
  destruct x; destruct y; simpl; auto
  decEq. apply Int64.add_commut
Qed

theorem addl_assoc : ∀ x y z, addl (addl x y) z = addl x (addl y z)
Proof
  unfold addl; intros; destruct Archi.ptr64 eqn:SF, x, y, z; simpl; auto
- rewrite Int64.add_assoc; auto
- rewrite ! Ptrofs.add_assoc. f_equal. f_equal
  rewrite Ptrofs.add_commut. auto with ptrofs
- rewrite ! Ptrofs.add_assoc. f_equal. f_equal
  apply Ptrofs.add_commut
- rewrite ! Ptrofs.add_assoc. f_equal. f_equal
  symmetry. auto with ptrofs
- rewrite Int64.add_assoc; auto
Qed

theorem addl_permut : ∀ x y z, addl x (addl y z) = addl y (addl x z)
Proof
  intros. rewrite (addl_commut y z). rewrite <- addl_assoc. apply addl_commut
Qed

theorem addl_permut_4 :
  ∀ x y z t, addl (addl x y) (addl z t) = addl (addl x z) (addl y t)
Proof
  intros. rewrite addl_permut. rewrite addl_assoc
  rewrite addl_permut. symmetry. apply addl_assoc
Qed

theorem negl_addl_distr : ∀ x y, negl(addl x y) = addl (negl x) (negl y)
Proof
  unfold negl, addl; intros; destruct Archi.ptr64 eqn:SF; destruct x; destruct y; simpl; auto;
  decEq; apply Int64.neg_add_distr
Qed

theorem subl_addl_opp : ∀ x y, subl x (Vlong y) = addl x (Vlong (Int64.neg y))
Proof
  unfold subl, addl; intros; destruct Archi.ptr64 eqn:SF, x; auto
- rewrite Int64.sub_add_opp; auto
- rewrite Ptrofs.sub_add_opp. f_equal. f_equal. symmetry. auto with ptrofs
- rewrite Int64.sub_add_opp; auto
Qed

theorem subl_opp_addl : ∀ x y, subl x (Vlong (Int64.neg y)) = addl x (Vlong y)
Proof
  intros. rewrite subl_addl_opp. rewrite Int64.neg_involutive. auto
Qed

theorem subl_addl_l :
  ∀ v1 v2 i, subl (addl v1 (Vlong i)) v2 = addl (subl v1 v2) (Vlong i)
Proof
  unfold subl, addl; intros; destruct Archi.ptr64 eqn:SF, v1, v2; auto
- rewrite Int64.sub_add_l; auto
- rewrite Ptrofs.sub_add_l; auto
- destruct (eq_block b b0); auto
  simpl. f_equal. rewrite Ptrofs.sub_add_l. auto with ptrofs
- rewrite Int64.sub_add_l; auto
Qed

theorem subl_addl_r :
  ∀ v1 v2 i, subl v1 (addl v2 (Vlong i)) = addl (subl v1 v2) (Vlong (Int64.neg i))
Proof
  unfold subl, addl; intros; destruct Archi.ptr64 eqn:SF, v1, v2; auto
- rewrite Int64.add_commut. rewrite Int64.sub_add_r. auto
- f_equal. replace (Ptrofs.of_int64 (Int64.add i1 i)) with (Ptrofs.add (Ptrofs.of_int64 i) (Ptrofs.of_int64 i1))
  rewrite Ptrofs.sub_add_r. f_equal
  symmetry. auto with ptrofs
  symmetry. rewrite Int64.add_commut. auto with ptrofs
- destruct (eq_block b b0); auto
  simpl; f_equal. rewrite Ptrofs.add_commut. rewrite Ptrofs.sub_add_r. auto with ptrofs. 
- rewrite Int64.add_commut. rewrite Int64.sub_add_r. auto
Qed

theorem mull_commut : ∀ x y, mull x y = mull y x
Proof
  destruct x; destruct y; simpl; auto. decEq. apply Int64.mul_commut
Qed

theorem mull_assoc : ∀ x y z, mull (mull x y) z = mull x (mull y z)
Proof
  destruct x; destruct y; destruct z; simpl; auto
  decEq. apply Int64.mul_assoc
Qed

theorem mull_addl_distr_l :
  ∀ x y z, mull (addl x y) z = addl (mull x z) (mull y z)
Proof
  unfold mull, addl; intros; destruct Archi.ptr64 eqn:SF; destruct x; destruct y; destruct z; simpl; auto;
  decEq; apply Int64.mul_add_distr_l
Qed

theorem mull_addl_distr_r :
  ∀ x y z, mull x (addl y z) = addl (mull x y) (mull x z)
Proof
  unfold mull, addl; intros; destruct Archi.ptr64 eqn:SF; destruct x; destruct y; destruct z; simpl; auto;
  decEq; apply Int64.mul_add_distr_r
Qed

theorem andl_commut : ∀ x y, andl x y = andl y x
Proof
  destruct x; destruct y; simpl; auto. decEq. apply Int64.and_commut
Qed

theorem andl_assoc : ∀ x y z, andl (andl x y) z = andl x (andl y z)
Proof
  destruct x; destruct y; destruct z; simpl; auto
  decEq. apply Int64.and_assoc
Qed

theorem orl_commut : ∀ x y, orl x y = orl y x
Proof
  destruct x; destruct y; simpl; auto. decEq. apply Int64.or_commut
Qed

theorem orl_assoc : ∀ x y z, orl (orl x y) z = orl x (orl y z)
Proof
  destruct x; destruct y; destruct z; simpl; auto
  decEq. apply Int64.or_assoc
Qed

theorem xorl_commut : ∀ x y, xorl x y = xorl y x
Proof
  destruct x; destruct y; simpl; auto. decEq. apply Int64.xor_commut
Qed

theorem xorl_assoc : ∀ x y z, xorl (xorl x y) z = xorl x (xorl y z)
Proof
  destruct x; destruct y; destruct z; simpl; auto
  decEq. apply Int64.xor_assoc
Qed

theorem notl_xorl : ∀ x, notl x = xorl x (Vlong Int64.mone)
Proof
  destruct x; simpl; auto
Qed

theorem divls_pow2 :
  ∀ x n logn y,
  Int64.is_power2' n = some logn → Int.ltu logn (Int.repr 63) = tt →
  divls x (Vlong n) = some y →
  shrxl x (Vint logn) = some y
Proof
  intros; destruct x; simpl in H1; inv H1
  destruct (Int64.eq n Int64.zero
         || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq n Int64.mone); inv H3
  simpl. rewrite H0. decEq. decEq
  generalize (Int64.is_power2'_correct _ _ H); intro
  unfold Int64.shrx'. rewrite Int64.shl'_mul_two_p. rewrite <- H1. 
  rewrite Int64.mul_commut. rewrite Int64.mul_one
  rewrite Int64.repr_unsigned. auto
Qed

theorem divlu_pow2 :
  ∀ x n logn y,
  Int64.is_power2' n = some logn →
  divlu x (Vlong n) = some y →
  shrlu x (Vint logn) = y
Proof
  intros; destruct x; simpl in H0; inv H0
  destruct (Int64.eq n Int64.zero); inv H2
  simpl
  rewrite (Int64.is_power2'_range _ _ H)
  decEq. symmetry. apply Int64.divu_pow2'. auto
Qed

theorem modlu_pow2 :
  ∀ x n logn y,
  Int64.is_power2 n = some logn →
  modlu x (Vlong n) = some y →
  andl x (Vlong (Int64.sub n Int64.one)) = y
Proof
  intros; destruct x; simpl in H0; inv H0
  destruct (Int64.eq n Int64.zero); inv H2
  simpl. decEq. symmetry. eapply Int64.modu_and; eauto
Qed

theorem shrxl_shrl_2 :
  ∀ n x z,
  shrxl x (Vint n) = some z →
  z = (if Int.eq n Int.zero then x else
         shrl (addl x (shrlu (shrl x (Vint (Int.repr 63)))
                      (Vint (Int.sub (Int.repr 64) n))))
              (Vint n))
Proof
  intros. destruct x; simpl in H; try discriminate
  destruct (Int.ltu n (Int.repr 63)) eqn:LT; inv H
  exploit Int.ltu_inv; eauto. change (Int.unsigned (Int.repr 63)) with 63; intros LT'
  predSpec Int.eq Int.eq_spec n Int.zero
- subst n. rewrite Int64.shrx'_zero. auto
- simpl. change (Int.ltu (Int.repr 63) Int64.iwordsize') with tt. simpl
  replace (Int.ltu (Int.sub (Int.repr 64) n) Int64.iwordsize') with tt. simpl
  replace (Int.ltu n Int64.iwordsize') with tt
  f_equal; apply Int64.shrx'_shr_2; assumption
  symmetry; apply zlt_true. change (Int.unsigned n < 64); omega
  symmetry; apply zlt_true. unfold Int.sub. change (Int.unsigned (Int.repr 64)) with 64
  assert (Int.unsigned n ≠ 0). { red; intros; elim H. rewrite <- (Int.repr_unsigned n), H0. auto. }
  rewrite Int.unsigned_repr. 
  change (Int.unsigned Int64.iwordsize') with 64; omega
  assert (64 < Int.max_unsigned) by reflexivity. omega
Qed

theorem negate_cmp_bool :
  ∀ c x y, cmp_bool (negate_comparison c) x y = option_map negb (cmp_bool c x y)
Proof
  destruct x; destruct y; simpl; auto. rewrite Int.negate_cmp. auto
Qed

theorem negate_cmpu_bool :
  ∀ valid_ptr c x y,
  cmpu_bool valid_ptr (negate_comparison c) x y = option_map negb (cmpu_bool valid_ptr c x y)
Proof
  assert (∀ c,
    cmp_different_blocks (negate_comparison c) = option_map negb (cmp_different_blocks c))
  { destruct c; auto. }
  unfold cmpu_bool; intros; destruct Archi.ptr64 eqn:SF, x, y; auto
- rewrite Int.negate_cmpu. auto
- rewrite Int.negate_cmpu. auto
- destruct (Int.eq i Int.zero && (valid_ptr b (Ptrofs.unsigned i0) || valid_ptr b (Ptrofs.unsigned i0 - 1))); auto
- destruct (Int.eq i0 Int.zero && (valid_ptr b (Ptrofs.unsigned i) || valid_ptr b (Ptrofs.unsigned i - 1))); auto
- destruct (eq_block b b0)
  destruct ((valid_ptr b (Ptrofs.unsigned i) || valid_ptr b (Ptrofs.unsigned i - 1)) &&
            (valid_ptr b0 (Ptrofs.unsigned i0) || valid_ptr b0 (Ptrofs.unsigned i0 - 1)))
  rewrite Ptrofs.negate_cmpu. auto
  auto
  destruct (valid_ptr b (Ptrofs.unsigned i) && valid_ptr b0 (Ptrofs.unsigned i0)); auto
Qed

theorem negate_cmpl_bool :
  ∀ c x y, cmpl_bool (negate_comparison c) x y = option_map negb (cmpl_bool c x y)
Proof
  destruct x; destruct y; simpl; auto. rewrite Int64.negate_cmp. auto
Qed

theorem negate_cmplu_bool :
  ∀ valid_ptr c x y,
  cmplu_bool valid_ptr (negate_comparison c) x y = option_map negb (cmplu_bool valid_ptr c x y)
Proof
  assert (∀ c,
    cmp_different_blocks (negate_comparison c) = option_map negb (cmp_different_blocks c))
  { destruct c; auto. }
  unfold cmplu_bool; intros; destruct Archi.ptr64 eqn:SF, x, y; auto
- rewrite Int64.negate_cmpu. auto
- simpl. destruct (Int64.eq i Int64.zero && (valid_ptr b (Ptrofs.unsigned i0) || valid_ptr b (Ptrofs.unsigned i0 - 1))); auto
- simpl. destruct (Int64.eq i0 Int64.zero && (valid_ptr b (Ptrofs.unsigned i) || valid_ptr b (Ptrofs.unsigned i - 1))); auto
- simpl. destruct (eq_block b b0)
  destruct ((valid_ptr b (Ptrofs.unsigned i) || valid_ptr b (Ptrofs.unsigned i - 1)) &&
            (valid_ptr b0 (Ptrofs.unsigned i0) || valid_ptr b0 (Ptrofs.unsigned i0 - 1)))
  rewrite Ptrofs.negate_cmpu. auto
  auto
  destruct (valid_ptr b (Ptrofs.unsigned i) && valid_ptr b0 (Ptrofs.unsigned i0)); auto
- rewrite Int64.negate_cmpu. auto
Qed

lemma not_of_optbool :
  ∀ ob, of_optbool (option_map negb ob) = notbool (of_optbool ob)
Proof
  destruct ob; auto. destruct b; auto
Qed

theorem negate_cmp :
  ∀ c x y,
  cmp (negate_comparison c) x y = notbool (cmp c x y)
Proof
  intros. unfold cmp. rewrite negate_cmp_bool. apply not_of_optbool
Qed

theorem negate_cmpu :
  ∀ valid_ptr c x y,
  cmpu valid_ptr (negate_comparison c) x y =
    notbool (cmpu valid_ptr c x y)
Proof
  intros. unfold cmpu. rewrite negate_cmpu_bool. apply not_of_optbool
Qed

theorem swap_cmp_bool :
  ∀ c x y,
  cmp_bool (swap_comparison c) x y = cmp_bool c y x
Proof
  destruct x; destruct y; simpl; auto. rewrite Int.swap_cmp. auto
Qed

theorem swap_cmpu_bool :
  ∀ valid_ptr c x y,
  cmpu_bool valid_ptr (swap_comparison c) x y =
    cmpu_bool valid_ptr c y x
Proof
  assert (E : ∀ c, cmp_different_blocks (swap_comparison c) = cmp_different_blocks c)
  { destruct c; auto. }
  intros; unfold cmpu_bool. rewrite ! E. destruct Archi.ptr64 eqn:SF, x, y; auto.  
- rewrite Int.swap_cmpu. auto
- rewrite Int.swap_cmpu. auto
- destruct (eq_block b b0); subst
  rewrite dec_eq_true
  destruct (valid_ptr b0 (Ptrofs.unsigned i) || valid_ptr b0 (Ptrofs.unsigned i - 1));
  destruct (valid_ptr b0 (Ptrofs.unsigned i0) || valid_ptr b0 (Ptrofs.unsigned i0 - 1));
  simpl; auto
  rewrite Ptrofs.swap_cmpu. auto
  rewrite dec_eq_false by auto
  destruct (valid_ptr b (Ptrofs.unsigned i));
    destruct (valid_ptr b0 (Ptrofs.unsigned i0)); simpl; auto
Qed

theorem swap_cmpl_bool :
  ∀ c x y,
  cmpl_bool (swap_comparison c) x y = cmpl_bool c y x
Proof
  destruct x; destruct y; simpl; auto. rewrite Int64.swap_cmp. auto
Qed

theorem swap_cmplu_bool :
  ∀ valid_ptr c x y,
  cmplu_bool valid_ptr (swap_comparison c) x y = cmplu_bool valid_ptr c y x
Proof
  assert (E : ∀ c, cmp_different_blocks (swap_comparison c) = cmp_different_blocks c)
  { destruct c; auto. }
  intros; unfold cmplu_bool. rewrite ! E. destruct Archi.ptr64 eqn:SF, x, y; auto.  
- rewrite Int64.swap_cmpu. auto
- destruct (eq_block b b0); subst
  rewrite dec_eq_true
  destruct (valid_ptr b0 (Ptrofs.unsigned i) || valid_ptr b0 (Ptrofs.unsigned i - 1));
  destruct (valid_ptr b0 (Ptrofs.unsigned i0) || valid_ptr b0 (Ptrofs.unsigned i0 - 1));
  simpl; auto
  rewrite Ptrofs.swap_cmpu. auto
  rewrite dec_eq_false by auto
  destruct (valid_ptr b (Ptrofs.unsigned i));
    destruct (valid_ptr b0 (Ptrofs.unsigned i0)); simpl; auto
- rewrite Int64.swap_cmpu. auto
Qed

theorem negate_cmpf_eq :
  ∀ v1 v2, notbool (cmpf Cne v1 v2) = cmpf Ceq v1 v2
Proof
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool
  rewrite Float.cmp_ne_eq. destruct (Float.cmp Ceq f f0); auto
Qed

theorem negate_cmpf_ne :
  ∀ v1 v2, notbool (cmpf Ceq v1 v2) = cmpf Cne v1 v2
Proof
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool
  rewrite Float.cmp_ne_eq. destruct (Float.cmp Ceq f f0); auto
Qed

theorem cmpf_le :
  ∀ v1 v2, cmpf Cle v1 v2 = or (cmpf Clt v1 v2) (cmpf Ceq v1 v2)
Proof
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool
  rewrite Float.cmp_le_lt_eq
  destruct (Float.cmp Clt f f0); destruct (Float.cmp Ceq f f0); auto
Qed

theorem cmpf_ge :
  ∀ v1 v2, cmpf Cge v1 v2 = or (cmpf Cgt v1 v2) (cmpf Ceq v1 v2)
Proof
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool
  rewrite Float.cmp_ge_gt_eq
  destruct (Float.cmp Cgt f f0); destruct (Float.cmp Ceq f f0); auto
Qed

theorem cmp_ne_0_optbool :
  ∀ ob, cmp Cne (of_optbool ob) (Vint Int.zero) = of_optbool ob
Proof
  intros. destruct ob; simpl; auto. destruct b; auto
Qed

theorem cmp_eq_1_optbool :
  ∀ ob, cmp Ceq (of_optbool ob) (Vint Int.one) = of_optbool ob
Proof
  intros. destruct ob; simpl; auto. destruct b; auto
Qed

theorem cmp_eq_0_optbool :
  ∀ ob, cmp Ceq (of_optbool ob) (Vint Int.zero) = of_optbool (option_map negb ob)
Proof
  intros. destruct ob; simpl; auto. destruct b; auto
Qed

theorem cmp_ne_1_optbool :
  ∀ ob, cmp Cne (of_optbool ob) (Vint Int.one) = of_optbool (option_map negb ob)
Proof
  intros. destruct ob; simpl; auto. destruct b; auto
Qed

theorem cmpu_ne_0_optbool :
  ∀ valid_ptr ob,
  cmpu valid_ptr Cne (of_optbool ob) (Vint Int.zero) = of_optbool ob
Proof
  intros. destruct ob; simpl; auto. destruct b; auto
Qed

theorem cmpu_eq_1_optbool :
  ∀ valid_ptr ob,
  cmpu valid_ptr Ceq (of_optbool ob) (Vint Int.one) = of_optbool ob
Proof
  intros. destruct ob; simpl; auto. destruct b; auto
Qed

theorem cmpu_eq_0_optbool :
  ∀ valid_ptr ob,
  cmpu valid_ptr Ceq (of_optbool ob) (Vint Int.zero) = of_optbool (option_map negb ob)
Proof
  intros. destruct ob; simpl; auto. destruct b; auto
Qed

theorem cmpu_ne_1_optbool :
  ∀ valid_ptr ob,
  cmpu valid_ptr Cne (of_optbool ob) (Vint Int.one) = of_optbool (option_map negb ob)
Proof
  intros. destruct ob; simpl; auto. destruct b; auto
Qed

lemma zero_ext_and :
  ∀ n v,
  0 < n < Int.zwordsize →
  Val.zero_ext n v = Val.and v (Vint (Int.repr (two_p n - 1)))
Proof
  intros. destruct v; simpl; auto. decEq. apply Int.zero_ext_and; auto. omega
Qed

lemma rolm_lt_zero :
  ∀ v, rolm v Int.one Int.one = cmp Clt v (Vint Int.zero)
Proof
  intros. unfold cmp, cmp_bool; destruct v; simpl; auto
  transitivity (Vint (Int.shru i (Int.repr (Int.zwordsize - 1))))
  decEq. symmetry. rewrite Int.shru_rolm. auto. auto
  rewrite Int.shru_lt_zero. destruct (Int.lt i Int.zero); auto
Qed

lemma rolm_ge_zero :
  ∀ v,
  xor (rolm v Int.one Int.one) (Vint Int.one) = cmp Cge v (Vint Int.zero)
Proof
  intros. rewrite rolm_lt_zero. destruct v; simpl; auto
  unfold cmp; simpl. destruct (Int.lt i Int.zero); auto
Qed

/- The ``is less defined'' relation between values.
    A value is less defined than itself, and [Vundef] is
    less defined than any value. -/

inductive lessdef : val → val → Prop :=
| lessdef_refl : ∀ v, lessdef v v
| lessdef_undef : ∀ v, lessdef Vundef v

lemma lessdef_same :
  ∀ v1 v2, v1 = v2 → lessdef v1 v2
Proof
  intros. subst v2. constructor
Qed

lemma lessdef_trans :
  ∀ v1 v2 v3, lessdef v1 v2 → lessdef v2 v3 → lessdef v1 v3
Proof
  intros. inv H. auto. constructor
Qed

inductive lessdef_list : list val → list val → Prop :=
| lessdef_list_nil :
      lessdef_list nil nil
| lessdef_list_cons :
      ∀ v1 v2 vl1 vl2,
      lessdef v1 v2 → lessdef_list vl1 vl2 →
      lessdef_list (v1 :: vl1) (v2 :: vl2)

Hint Resolve lessdef_refl lessdef_undef lessdef_list_nil lessdef_list_cons

lemma lessdef_list_inv :
  ∀ vl1 vl2, lessdef_list vl1 vl2 → vl1 = vl2 ∨ In Vundef vl1
Proof
  induction 1; simpl
  tauto
  inv H. destruct IHlessdef_list
  left; congruence. tauto. tauto
Qed

lemma lessdef_list_trans :
  ∀ vl1 vl2, lessdef_list vl1 vl2 → ∀ vl3, lessdef_list vl2 vl3 → lessdef_list vl1 vl3
Proof
  induction 1; intros vl3 LD; inv LD; constructor; eauto using lessdef_trans
Qed

/- Compatibility of operations with the [lessdef] relation. -/

lemma load_result_lessdef :
  ∀ chunk v1 v2,
  lessdef v1 v2 → lessdef (load_result chunk v1) (load_result chunk v2)
Proof
  intros. inv H. auto. destruct chunk; simpl; auto
Qed

lemma zero_ext_lessdef :
  ∀ n v1 v2, lessdef v1 v2 → lessdef (zero_ext n v1) (zero_ext n v2)
Proof
  intros; inv H; simpl; auto
Qed

lemma sign_ext_lessdef :
  ∀ n v1 v2, lessdef v1 v2 → lessdef (sign_ext n v1) (sign_ext n v2)
Proof
  intros; inv H; simpl; auto
Qed

lemma singleoffloat_lessdef :
  ∀ v1 v2, lessdef v1 v2 → lessdef (singleoffloat v1) (singleoffloat v2)
Proof
  intros; inv H; simpl; auto
Qed

lemma add_lessdef :
  ∀ v1 v1' v2 v2',
  lessdef v1 v1' → lessdef v2 v2' → lessdef (add v1 v2) (add v1' v2')
Proof
  intros. inv H. inv H0. auto. destruct v1'; simpl; auto. simpl; auto
Qed

lemma addl_lessdef :
  ∀ v1 v1' v2 v2',
  lessdef v1 v1' → lessdef v2 v2' → lessdef (addl v1 v2) (addl v1' v2')
Proof
  intros. inv H. inv H0. auto. destruct v1'; simpl; auto. simpl; auto
Qed

lemma cmpu_bool_lessdef :
  ∀ valid_ptr valid_ptr' c v1 v1' v2 v2' b,
  (∀ b ofs, valid_ptr b ofs = tt → valid_ptr' b ofs = tt) →
  lessdef v1 v1' → lessdef v2 v2' →
  cmpu_bool valid_ptr c v1 v2 = some b →
  cmpu_bool valid_ptr' c v1' v2' = some b
Proof
  intros
  assert (X : ∀ b ofs,
             valid_ptr b ofs || valid_ptr b (ofs - 1) = tt →
             valid_ptr' b ofs || valid_ptr' b (ofs - 1) = tt)
  { intros. apply orb_true_intro. destruct (orb_prop _ _ H3)
    rewrite (H b0 ofs); auto
    rewrite (H b0 (ofs - 1)); auto. }
  inv H0; [ | discriminate]
  inv H1; [ | destruct v1'; discriminate ]
  unfold cmpu_bool in *. remember Archi.ptr64 as ptr64
  destruct v1'; auto; destruct v2'; auto; destruct ptr64; auto
- destruct (Int.eq i Int.zero); auto
  destruct (valid_ptr b0 (Ptrofs.unsigned i0) || valid_ptr b0 (Ptrofs.unsigned i0 - 1)) eqn:A; inv H2
  rewrite X; auto
- destruct (Int.eq i0 Int.zero); auto
  destruct (valid_ptr b0 (Ptrofs.unsigned i) || valid_ptr b0 (Ptrofs.unsigned i - 1)) eqn:A; inv H2
  rewrite X; auto
- destruct (eq_block b0 b1)
+ destruct (valid_ptr b0 (Ptrofs.unsigned i) || valid_ptr b0 (Ptrofs.unsigned i - 1)) eqn:A; inv H2
  destruct (valid_ptr b1 (Ptrofs.unsigned i0) || valid_ptr b1 (Ptrofs.unsigned i0 - 1)) eqn:B; inv H1
  rewrite ! X; auto
+ destruct (valid_ptr b0 (Ptrofs.unsigned i) && valid_ptr b1 (Ptrofs.unsigned i0)) eqn:A; inv H2
  InvBooleans. rewrite ! H; auto
Qed

lemma cmplu_bool_lessdef :
  ∀ valid_ptr valid_ptr' c v1 v1' v2 v2' b,
  (∀ b ofs, valid_ptr b ofs = tt → valid_ptr' b ofs = tt) →
  lessdef v1 v1' → lessdef v2 v2' →
  cmplu_bool valid_ptr c v1 v2 = some b →
  cmplu_bool valid_ptr' c v1' v2' = some b
Proof
  intros
  assert (X : ∀ b ofs,
             valid_ptr b ofs || valid_ptr b (ofs - 1) = tt →
             valid_ptr' b ofs || valid_ptr' b (ofs - 1) = tt)
  { intros. apply orb_true_intro. destruct (orb_prop _ _ H3)
    rewrite (H b0 ofs); auto
    rewrite (H b0 (ofs - 1)); auto. }
  inv H0; [ | discriminate]
  inv H1; [ | destruct v1'; discriminate ]
  unfold cmplu_bool in *. remember Archi.ptr64 as ptr64
  destruct v1'; auto; destruct v2'; auto; destruct ptr64; auto
- destruct (Int64.eq i Int64.zero); auto
  destruct (valid_ptr b0 (Ptrofs.unsigned i0) || valid_ptr b0 (Ptrofs.unsigned i0 - 1)) eqn:A; inv H2
  rewrite X; auto
- destruct (Int64.eq i0 Int64.zero); auto
  destruct (valid_ptr b0 (Ptrofs.unsigned i) || valid_ptr b0 (Ptrofs.unsigned i - 1)) eqn:A; inv H2
  rewrite X; auto
- destruct (eq_block b0 b1)
+ destruct (valid_ptr b0 (Ptrofs.unsigned i) || valid_ptr b0 (Ptrofs.unsigned i - 1)) eqn:A; inv H2
  destruct (valid_ptr b1 (Ptrofs.unsigned i0) || valid_ptr b1 (Ptrofs.unsigned i0 - 1)) eqn:B; inv H1
  rewrite ! X; auto
+ destruct (valid_ptr b0 (Ptrofs.unsigned i) && valid_ptr b1 (Ptrofs.unsigned i0)) eqn:A; inv H2
  InvBooleans. rewrite ! H; auto
Qed

lemma of_optbool_lessdef :
  ∀ ob ob',
  (∀ b, ob = some b → ob' = some b) →
  lessdef (of_optbool ob) (of_optbool ob')
Proof
  intros. destruct ob; simpl; auto. rewrite (H b); auto
Qed

lemma longofwords_lessdef :
  ∀ v1 v2 v1' v2',
  lessdef v1 v1' → lessdef v2 v2' → lessdef (longofwords v1 v2) (longofwords v1' v2')
Proof
  intros. unfold longofwords. inv H; auto. inv H0; auto. destruct v1'; auto
Qed

lemma loword_lessdef :
  ∀ v v', lessdef v v' → lessdef (loword v) (loword v')
Proof
  intros. inv H; auto
Qed

lemma hiword_lessdef :
  ∀ v v', lessdef v v' → lessdef (hiword v) (hiword v')
Proof
  intros. inv H; auto
Qed

lemma offset_ptr_zero :
  ∀ v, lessdef (offset_ptr v Ptrofs.zero) v
Proof
  intros. destruct v; simpl; auto. rewrite Ptrofs.add_zero; auto
Qed

lemma offset_ptr_assoc :
  ∀ v d1 d2, offset_ptr (offset_ptr v d1) d2 = offset_ptr v (Ptrofs.add d1 d2)
Proof
  intros. destruct v; simpl; auto. f_equal. apply Ptrofs.add_assoc. 
Qed

/- * Values and memory injections -/

/- A memory injection [f] is a function from addresses to either [None]
  or [Some] of an address and an offset.  It defines a correspondence
  between the blocks of two memory states [m1] and [m2]:
- if [f b = None], the block [b] of [m1] has no equivalent in [m2];
- if [f b = Some(b', ofs)], the block [b] of [m2] corresponds to
  a sub-block at offset [ofs] of the block [b'] in [m2].
-/

def meminj : Type := block → option (block * ℤ)

/- A memory injection defines a relation between values that is the
  identity relation, except for pointer values which are shifted
  as prescribed by the memory injection.  Moreover, [Vundef] values
  inject into any other value. -/

inductive inject (mi : meminj) : val → val → Prop :=
| inject_int :
      ∀ i, inject mi (Vint i) (Vint i)
| inject_long :
      ∀ i, inject mi (Vlong i) (Vlong i)
| inject_float :
      ∀ f, inject mi (Vfloat f) (Vfloat f)
| inject_single :
      ∀ f, inject mi (Vsingle f) (Vsingle f)
| inject_ptr :
      ∀ b1 ofs1 b2 ofs2 delta,
      mi b1 = some (b2, delta) →
      ofs2 = Ptrofs.add ofs1 (Ptrofs.repr delta) →
      inject mi (Vptr b1 ofs1) (Vptr b2 ofs2)
| val_inject_undef : ∀ v,
      inject mi Vundef v

Hint Constructors inject

inductive inject_list (mi : meminj) : list val → list val→ Prop:=
| inject_list_nil :
      inject_list mi nil nil
| inject_list_cons : ∀ v v' vl vl' ,
      inject mi v v' → inject_list mi vl vl'→
      inject_list mi (v :: vl) (v' :: vl')

Hint Resolve inject_list_nil inject_list_cons

lemma inject_ptrofs :
  ∀ mi i, inject mi (Vptrofs i) (Vptrofs i)
Proof
  unfold Vptrofs; intros. destruct Archi.ptr64; auto. 
Qed

Hint Resolve inject_ptrofs

section VAL_INJ_OPS

parameter f : meminj

lemma load_result_inject :
  ∀ chunk v1 v2,
  inject f v1 v2 →
  inject f (Val.load_result chunk v1) (Val.load_result chunk v2)
Proof
  intros. inv H; destruct chunk; simpl; try constructor; destruct Archi.ptr64; econstructor; eauto. 
Qed

theorem add_inject :
  ∀ v1 v1' v2 v2',
  inject f v1 v1' →
  inject f v2 v2' →
  inject f (Val.add v1 v2) (Val.add v1' v2')
Proof
  intros. unfold Val.add. destruct Archi.ptr64 eqn:SF
- inv H; inv H0; constructor. 
- inv H; inv H0; simpl; auto
+ econstructor; eauto. 
  rewrite ! Ptrofs.add_assoc. decEq. apply Ptrofs.add_commut
+ econstructor; eauto. 
  rewrite ! Ptrofs.add_assoc. decEq. apply Ptrofs.add_commut
Qed

theorem sub_inject :
  ∀ v1 v1' v2 v2',
  inject f v1 v1' →
  inject f v2 v2' →
  inject f (Val.sub v1 v2) (Val.sub v1' v2')
Proof
  intros. unfold Val.sub. destruct Archi.ptr64 eqn:SF
- inv H; inv H0; constructor
- inv H; inv H0; simpl; auto
+ econstructor; eauto. 
  rewrite Ptrofs.sub_add_l. auto
+ destruct (eq_block b1 b0); auto
  subst. rewrite H1 in H. inv H. rewrite dec_eq_true
  rewrite Ptrofs.sub_shifted. auto
Qed

theorem addl_inject :
  ∀ v1 v1' v2 v2',
  inject f v1 v1' →
  inject f v2 v2' →
  inject f (Val.addl v1 v2) (Val.addl v1' v2')
Proof
  intros. unfold Val.addl. destruct Archi.ptr64 eqn:SF
- inv H; inv H0; simpl; auto
+ econstructor; eauto. 
  rewrite ! Ptrofs.add_assoc. decEq. apply Ptrofs.add_commut
+ econstructor; eauto. 
  rewrite ! Ptrofs.add_assoc. decEq. apply Ptrofs.add_commut
- inv H; inv H0; constructor. 
Qed

theorem subl_inject :
  ∀ v1 v1' v2 v2',
  inject f v1 v1' →
  inject f v2 v2' →
  inject f (Val.subl v1 v2) (Val.subl v1' v2')
Proof
  intros. unfold Val.subl. destruct Archi.ptr64 eqn:SF
- inv H; inv H0; simpl; auto
+ econstructor; eauto. 
  rewrite Ptrofs.sub_add_l. auto
+ destruct (eq_block b1 b0); auto
  subst. rewrite H1 in H. inv H. rewrite dec_eq_true
  rewrite Ptrofs.sub_shifted. auto
- inv H; inv H0; constructor
Qed

lemma offset_ptr_inject :
  ∀ v v' ofs, inject f v v' → inject f (offset_ptr v ofs) (offset_ptr v' ofs)
Proof
  intros. inv H; simpl; econstructor; eauto
  rewrite ! Ptrofs.add_assoc. f_equal. apply Ptrofs.add_commut
Qed

lemma cmp_bool_inject :
  ∀ c v1 v2 v1' v2' b,
  inject f v1 v1' →
  inject f v2 v2' →
  Val.cmp_bool c v1 v2 = some b →
  Val.cmp_bool c v1' v2' = some b
Proof
  intros. inv H; simpl in H1; try discriminate; inv H0; simpl in H1; try discriminate; simpl; auto
Qed

parameter (valid_ptr1 valid_ptr2 : block → ℤ → bool)

def weak_valid_ptr1 b ofs := valid_ptr1 b ofs || valid_ptr1 b (ofs - 1)
def weak_valid_ptr2 b ofs := valid_ptr2 b ofs || valid_ptr2 b (ofs - 1)

Hypothesis valid_ptr_inj :
  ∀ b1 ofs b2 delta,
  f b1 = some(b2, delta) →
  valid_ptr1 b1 (Ptrofs.unsigned ofs) = tt →
  valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = tt

Hypothesis weak_valid_ptr_inj :
  ∀ b1 ofs b2 delta,
  f b1 = some(b2, delta) →
  weak_valid_ptr1 b1 (Ptrofs.unsigned ofs) = tt →
  weak_valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = tt

Hypothesis weak_valid_ptr_no_overflow :
  ∀ b1 ofs b2 delta,
  f b1 = some(b2, delta) →
  weak_valid_ptr1 b1 (Ptrofs.unsigned ofs) = tt →
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned

Hypothesis valid_different_ptrs_inj :
  ∀ b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 ≠ b2 →
  valid_ptr1 b1 (Ptrofs.unsigned ofs1) = tt →
  valid_ptr1 b2 (Ptrofs.unsigned ofs2) = tt →
  f b1 = some (b1', delta1) →
  f b2 = some (b2', delta2) →
  b1' ≠ b2' ∨
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠ Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2))

lemma cmpu_bool_inject :
  ∀ c v1 v2 v1' v2' b,
  inject f v1 v1' →
  inject f v2 v2' →
  Val.cmpu_bool valid_ptr1 c v1 v2 = some b →
  Val.cmpu_bool valid_ptr2 c v1' v2' = some b
Proof
  Local Opaque Int.add Ptrofs.add
  intros
  unfold cmpu_bool in *; destruct Archi.ptr64; 
  inv H; simpl in H1; try discriminate; inv H0; simpl in H1; try discriminate; simpl; auto
- fold (weak_valid_ptr1 b1 (Ptrofs.unsigned ofs1)) in H1
  fold (weak_valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta))))
  destruct (Int.eq i Int.zero); auto
  destruct (weak_valid_ptr1 b1 (Ptrofs.unsigned ofs1)) eqn:E; try discriminate
  erewrite weak_valid_ptr_inj by eauto. auto
- fold (weak_valid_ptr1 b1 (Ptrofs.unsigned ofs1)) in H1
  fold (weak_valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta))))
  destruct (Int.eq i Int.zero); auto
  destruct (weak_valid_ptr1 b1 (Ptrofs.unsigned ofs1)) eqn:E; try discriminate
  erewrite weak_valid_ptr_inj by eauto. auto
- fold (weak_valid_ptr1 b1 (Ptrofs.unsigned ofs1)) in H1
  fold (weak_valid_ptr1 b0 (Ptrofs.unsigned ofs0)) in H1
  fold (weak_valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta))))
  fold (weak_valid_ptr2 b3 (Ptrofs.unsigned (Ptrofs.add ofs0 (Ptrofs.repr delta0))))
  destruct (eq_block b1 b0); subst
  rewrite H in H2. inv H2. rewrite dec_eq_true
  destruct (weak_valid_ptr1 b0 (Ptrofs.unsigned ofs1)) eqn:?; try discriminate
  destruct (weak_valid_ptr1 b0 (Ptrofs.unsigned ofs0)) eqn:?; try discriminate
  erewrite !weak_valid_ptr_inj by eauto. simpl
  rewrite <-H1. simpl. decEq. apply Ptrofs.translate_cmpu; eauto
  destruct (valid_ptr1 b1 (Ptrofs.unsigned ofs1)) eqn:?; try discriminate
  destruct (valid_ptr1 b0 (Ptrofs.unsigned ofs0)) eqn:?; try discriminate
  destruct (eq_block b2 b3); subst
  assert (valid_ptr_implies : ∀ b ofs, valid_ptr1 b ofs = tt → weak_valid_ptr1 b ofs = tt)
    intros. unfold weak_valid_ptr1. rewrite H0; auto
  erewrite !weak_valid_ptr_inj by eauto using valid_ptr_implies. simpl
  exploit valid_different_ptrs_inj; eauto. intros [?|?]; [congruence |]
  destruct c; simpl in H1; inv H1
  simpl; decEq. rewrite Ptrofs.eq_false; auto. congruence
  simpl; decEq. rewrite Ptrofs.eq_false; auto. congruence
  now erewrite !valid_ptr_inj by eauto
Qed

lemma cmplu_bool_inject :
  ∀ c v1 v2 v1' v2' b,
  inject f v1 v1' →
  inject f v2 v2' →
  Val.cmplu_bool valid_ptr1 c v1 v2 = some b →
  Val.cmplu_bool valid_ptr2 c v1' v2' = some b
Proof
  Local Opaque Int64.add Ptrofs.add
  intros
  unfold cmplu_bool in *; destruct Archi.ptr64;
  inv H; simpl in H1; try discriminate; inv H0; simpl in H1; try discriminate; simpl; auto
- fold (weak_valid_ptr1 b1 (Ptrofs.unsigned ofs1)) in H1
  fold (weak_valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta))))
  destruct (Int64.eq i Int64.zero); auto
  destruct (weak_valid_ptr1 b1 (Ptrofs.unsigned ofs1)) eqn:E; try discriminate
  erewrite weak_valid_ptr_inj by eauto. auto
- fold (weak_valid_ptr1 b1 (Ptrofs.unsigned ofs1)) in H1
  fold (weak_valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta))))
  destruct (Int64.eq i Int64.zero); auto
  destruct (weak_valid_ptr1 b1 (Ptrofs.unsigned ofs1)) eqn:E; try discriminate
  erewrite weak_valid_ptr_inj by eauto. auto
- fold (weak_valid_ptr1 b1 (Ptrofs.unsigned ofs1)) in H1
  fold (weak_valid_ptr1 b0 (Ptrofs.unsigned ofs0)) in H1
  fold (weak_valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta))))
  fold (weak_valid_ptr2 b3 (Ptrofs.unsigned (Ptrofs.add ofs0 (Ptrofs.repr delta0))))
  destruct (eq_block b1 b0); subst
  rewrite H in H2. inv H2. rewrite dec_eq_true
  destruct (weak_valid_ptr1 b0 (Ptrofs.unsigned ofs1)) eqn:?; try discriminate
  destruct (weak_valid_ptr1 b0 (Ptrofs.unsigned ofs0)) eqn:?; try discriminate
  erewrite !weak_valid_ptr_inj by eauto. simpl
  rewrite <-H1. simpl. decEq. apply Ptrofs.translate_cmpu; eauto
  destruct (valid_ptr1 b1 (Ptrofs.unsigned ofs1)) eqn:?; try discriminate
  destruct (valid_ptr1 b0 (Ptrofs.unsigned ofs0)) eqn:?; try discriminate
  destruct (eq_block b2 b3); subst
  assert (valid_ptr_implies : ∀ b ofs, valid_ptr1 b ofs = tt → weak_valid_ptr1 b ofs = tt)
    intros. unfold weak_valid_ptr1. rewrite H0; auto
  erewrite !weak_valid_ptr_inj by eauto using valid_ptr_implies. simpl
  exploit valid_different_ptrs_inj; eauto. intros [?|?]; [congruence |]
  destruct c; simpl in H1; inv H1
  simpl; decEq. rewrite Ptrofs.eq_false; auto. congruence
  simpl; decEq. rewrite Ptrofs.eq_false; auto. congruence
  now erewrite !valid_ptr_inj by eauto
Qed

lemma longofwords_inject :
  ∀ v1 v2 v1' v2',
  inject f v1 v1' → inject f v2 v2' → inject f (Val.longofwords v1 v2) (Val.longofwords v1' v2')
Proof
  intros. unfold Val.longofwords. inv H; auto. inv H0; auto
Qed

lemma loword_inject :
  ∀ v v', inject f v v' → inject f (Val.loword v) (Val.loword v')
Proof
  intros. unfold Val.loword; inv H; auto
Qed

lemma hiword_inject :
  ∀ v v', inject f v v' → inject f (Val.hiword v) (Val.hiword v')
Proof
  intros. unfold Val.hiword; inv H; auto
Qed

end VAL_INJ_OPS

end Val

Notation meminj := Val.meminj

/- Monotone evolution of a memory injection. -/

def inject_incr (f1 f2 : meminj) : Prop :=
  ∀ b b' delta, f1 b = some(b', delta) → f2 b = some(b', delta)

lemma inject_incr_refl :
   ∀ f , inject_incr f f 
Proof. unfold inject_incr. auto. Qed

lemma inject_incr_trans :
  ∀ f1 f2 f3,
  inject_incr f1 f2 → inject_incr f2 f3 → inject_incr f1 f3 
Proof
  unfold inject_incr; intros. eauto
Qed

lemma val_inject_incr :
  ∀ f1 f2 v v',
  inject_incr f1 f2 →
  Val.inject f1 v v' →
  Val.inject f2 v v'
Proof
  intros. inv H0; eauto
Qed

lemma val_inject_list_incr :
  ∀ f1 f2 vl vl' ,
  inject_incr f1 f2 → Val.inject_list f1 vl vl' →
  Val.inject_list f2 vl vl'
Proof
  induction vl; intros; inv H0. auto
  constructor. eapply val_inject_incr; eauto. auto
Qed

Hint Resolve inject_incr_refl val_inject_incr val_inject_list_incr

lemma val_inject_lessdef :
  ∀ v1 v2, Val.lessdef v1 v2 <→ Val.inject (fun b := some(b, 0)) v1 v2
Proof
  intros; split; intros
  inv H; auto. destruct v2; econstructor; eauto. rewrite Ptrofs.add_zero; auto
  inv H; auto. inv H0. rewrite Ptrofs.add_zero; auto
Qed

lemma val_inject_list_lessdef :
  ∀ vl1 vl2, Val.lessdef_list vl1 vl2 <→ Val.inject_list (fun b := some(b, 0)) vl1 vl2
Proof
  intros; split
  induction 1; constructor; auto. apply val_inject_lessdef; auto
  induction 1; constructor; auto. apply val_inject_lessdef; auto
Qed

/- The identity injection gives rise to the "less defined than" relation. -/

def inject_id : meminj := fun b := some(b, 0)

lemma val_inject_id :
  ∀ v1 v2,
  Val.inject inject_id v1 v2 <→ Val.lessdef v1 v2
Proof
  intros; split; intros
  inv H; auto
  unfold inject_id in H0. inv H0. rewrite Ptrofs.add_zero. constructor
  inv H. destruct v2; econstructor. unfold inject_id; reflexivity. rewrite Ptrofs.add_zero; auto
  constructor
Qed

/- Composing two memory injections -/

def compose_meminj (f f' : meminj) : meminj :=
  fun b :=
    match f b with
    | none := none
    | some(b', delta) :=
        match f' b' with
        | none := none
        | some(b'', delta') := some(b'', delta + delta')
        end
    end

lemma val_inject_compose :
  ∀ f f' v1 v2 v3,
  Val.inject f v1 v2 → Val.inject f' v2 v3 →
  Val.inject (compose_meminj f f') v1 v3
Proof
  intros. inv H; auto; inv H0; auto. econstructor
  unfold compose_meminj; rewrite H1; rewrite H3; eauto
  rewrite Ptrofs.add_assoc. decEq. unfold Ptrofs.add. apply Ptrofs.eqm_samerepr. auto with ints
Qed.

end values