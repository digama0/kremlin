
/- In-memory representation of values. -/

import .ast .integers .values

namespace memdata
open ast integers values word floats

inductive quantity : Type | Q32 | Q64
open quantity

instance quantity_eq : decidable_eq quantity := by tactic.mk_dec_eq_instance

def quantity.size : quantity → ℕ
| Q32 := 4
| Q64 := 8

lemma quantity.size_pos (q : quantity) : q.size > 0 :=
by cases q; exact dec_trivial


/- * Memory values -/

/- A ``memory value'' is a byte-sized quantity that describes the current
  content of a memory cell.  It can be either:
- a concrete 8-bit integer;
- a byte-sized fragment of an opaque value;
- the special constant [Undef] that represents uninitialized memory.
-/

/- Values stored in memory cells. -/

inductive memval : Type
| Undef : memval
| Byte : byte → memval
| Fragment : val → quantity → nat → memval.
open memval

/- * Encoding and decoding integers -/

/- We define functions to convert between integers and lists of bytes
  of a given length -/

def rev_if_be (l : list byte) : list byte :=
if archi.big_endian then l.reverse else l

def encode_int (sz : ℕ) (x : ℤ) : list byte :=
rev_if_be (words_of_int sz x)

def decode_int (b : list byte) : ℕ :=
nat_of_words (rev_if_be b)

/- Length properties -/

@[simp] lemma rev_if_be_length (l) : (rev_if_be l).length = l.length :=
by delta rev_if_be; by_cases (archi.big_endian : Prop); simp [h]

@[simp] lemma encode_int_length (sz x) : (encode_int sz x).length = sz :=
by simp [encode_int]

/- Decoding after encoding -/

lemma rev_if_be_involutive (l) : rev_if_be (rev_if_be l) = l :=
by delta rev_if_be; by_cases (archi.big_endian : Prop); simp [h]

lemma decode_encode_int (n x) : decode_int (encode_int n x) = x.nat_mod (2^(n * 8)) :=
by simp [decode_int, encode_int, rev_if_be_involutive]; refl

lemma decode_encode_int_1 (x : int32) :
  repr (decode_int (encode_int 1 (unsigned x))) = zero_ext 8 x := sorry'

lemma decode_encode_int_2 (x : int32) :
  repr (decode_int (encode_int 2 (unsigned x))) = zero_ext 16 x := sorry'

lemma decode_encode_int_4 (x : int32) :
  repr (decode_int (encode_int 4 (unsigned x))) = x := sorry'

lemma decode_encode_int_8 (x : int64) :
  repr (decode_int (encode_int 8 (unsigned x))) = x := sorry'

/- A length-[n] encoding depends only on the low [8*n] bits of the integer. -/

lemma encode_int_mod (n) {x y} (h : (repr x : word (8*n)) = repr y) :
  encode_int n x = encode_int n y :=
by delta encode_int; rw words_of_int_mod _ (mod_eq_of_repr_eq h)

lemma encode_int_8_mod (x y) : (repr x : byte) = repr y →
  encode_int 1 x = encode_int 1 y :=
encode_int_mod 1

lemma encode_int_16_mod (x y) : (repr x : word 16) = repr y →
  encode_int 2 x = encode_int 2 y :=
encode_int_mod 2

/- * Encoding and decoding values -/

def inj_bytes (bl : list byte) : list memval :=
bl.map Byte

def proj_bytes : list memval → option (list byte)
| []              := some []
| (Byte b :: vl') := list.cons b <$> proj_bytes vl'
| _               := none

theorem length_inj_bytes (bl) : (inj_bytes bl).length = bl.length :=
list.length_map _ _

theorem proj_inj_bytes (bl) : proj_bytes (inj_bytes bl) = some bl :=
begin
  simp [inj_bytes],
  induction bl with b bl IH; simp [inj_bytes, proj_bytes],
  simp [IH], refl
end

lemma inj_proj_bytes (cl bl) : proj_bytes cl = some bl → cl = inj_bytes bl := sorry'

def inj_value_rec (v : val) (q : quantity) : ℕ → list memval
| 0 := []
| (m + 1) := Fragment v q m :: inj_value_rec m

def inj_value (q : quantity) (v : val) : list memval :=
inj_value_rec v q q.size

def check_value (v : val) (q : quantity) : ℕ → list memval → bool
| 0 [] := tt
| (m + 1) (Fragment v' q' m' :: vl') :=
  v = v' ∧ q = q' ∧ m = m' ∧ check_value m vl'
| _ _ := ff

def proj_value (q : quantity) (vl : list memval) : val :=
match vl with
| Fragment v q' n :: vl' :=
      if check_value v q q.size vl then v else Vundef
| _ := Vundef
end

def encode_val : memory_chunk → val → list memval
| Mint8signed    (Vint n)     := inj_bytes (encode_int 1 (unsigned n))
| Mint8unsigned  (Vint n)     := inj_bytes (encode_int 1 (unsigned n))
| Mint16signed   (Vint n)     := inj_bytes (encode_int 2 (unsigned n))
| Mint16unsigned (Vint n)     := inj_bytes (encode_int 2 (unsigned n))
| Mint32         (Vint n)     := inj_bytes (encode_int 4 (unsigned n))
| Mint32         (Vptr b ofs) := if archi.ptr64 then list.repeat Undef 4 else inj_value Q32 (Vptr b ofs)
| Mint64         (Vlong n)    := inj_bytes (encode_int 8 (unsigned n))
| Mint64         (Vptr b ofs) := if archi.ptr64 then inj_value Q64 (Vptr b ofs) else list.repeat Undef 8
| Mfloat32       (Vsingle n)  := inj_bytes (encode_int 4 (unsigned n.to_bits))
| Mfloat64       (Vfloat n)   := inj_bytes (encode_int 8 (unsigned n.to_bits))
| Many32         v            := inj_value Q32 v
| Many64         v            := inj_value Q64 v
| chunk          _            := list.repeat Undef chunk.size

def decode_val (chunk : memory_chunk) (vl : list memval) : val :=
match proj_bytes vl, chunk with
| some bl, Mint8signed    := Vint (sign_ext W8 (repr (decode_int bl)))
| some bl, Mint8unsigned  := Vint (zero_ext 8 (repr (decode_int bl)))
| some bl, Mint16signed   := Vint (sign_ext W16 (repr (decode_int bl)))
| some bl, Mint16unsigned := Vint (zero_ext 16 (repr (decode_int bl)))
| some bl, Mint32         := Vint (repr (decode_int bl))
| some bl, Mint64         := Vlong (repr (decode_int bl))
| some bl, Mfloat32       := float32.of_bits (repr (decode_int bl))
| some bl, Mfloat64       := float.of_bits (repr (decode_int bl))
| some bl, Many32         := Vundef
| some bl, Many64         := Vundef
| none,    Mint32         := if archi.ptr64 then Vundef else val.load_result chunk (proj_value Q32 vl)
| none,    Many32         := val.load_result chunk (proj_value Q32 vl)
| none,    Mint64         := if archi.ptr64 then val.load_result chunk (proj_value Q64 vl) else Vundef
| none,    Many64         := val.load_result chunk (proj_value Q64 vl)
| none,    _              := Vundef
end

lemma encode_val_length (chunk v) : (encode_val chunk v).length = chunk.size := sorry'

lemma check_inj_value (v q n) : check_value v q n (inj_value_rec v q n) := sorry'

lemma proj_inj_value (q v) : proj_value q (inj_value q v) = v := sorry'

theorem in_inj_value (mv v q) : mv ∈ inj_value q v → ∃ n, mv = Fragment v q n := sorry'

lemma proj_inj_value_mismatch (q1 q2 v) : q1 ≠ q2 → proj_value q1 (inj_value q2 v) = Vundef := sorry'

def decode_encode_val : val → memory_chunk → memory_chunk → val → Prop
| (Vundef)      _               _               v2 := v2 = Vundef
| (Vint n)      Mint8signed     Mint8signed     v2 := v2 = Vint (sign_ext W8 n)
| (Vint n)      Mint8unsigned   Mint8signed     v2 := v2 = Vint (sign_ext W8 n)
| (Vint n)      Mint8signed     Mint8unsigned   v2 := v2 = Vint (zero_ext 8 n)
| (Vint n)      Mint8unsigned   Mint8unsigned   v2 := v2 = Vint (zero_ext 8 n)
| (Vint n)      Mint16signed    Mint16signed    v2 := v2 = Vint (sign_ext W16 n)
| (Vint n)      Mint16unsigned  Mint16signed    v2 := v2 = Vint (sign_ext W16 n)
| (Vint n)      Mint16signed    Mint16unsigned  v2 := v2 = Vint (zero_ext 16 n)
| (Vint n)      Mint16unsigned  Mint16unsigned  v2 := v2 = Vint (zero_ext 16 n)
| (Vint n)      Mint32          Mint32          v2 := v2 = Vint n
| (Vint n)      Many32          Many32          v2 := v2 = Vint n
| (Vint n)      Mint32          Mfloat32        v2 := v2 = float32.of_bits n
| (Vint n)      Many64          Many64          v2 := v2 = Vint n
| (Vint n)      Mint64          _               v2 := v2 = Vundef
| (Vint n)      Mfloat32        _               v2 := v2 = Vundef
| (Vint n)      Mfloat64        _               v2 := v2 = Vundef
| (Vint n)      Many64          _               v2 := v2 = Vundef
| (Vint n)      _               _               v2 := true /- nothing meaningful to say about v2 -/
| (Vptr b ofs)  Mint32          Mint32          v2 := v2 = if archi.ptr64 then Vundef else Vptr b ofs
| (Vptr b ofs)  Mint32          Many32          v2 := v2 = if archi.ptr64 then Vundef else Vptr b ofs
| (Vptr b ofs)  Many32          Mint32          v2 := v2 = if archi.ptr64 then Vundef else Vptr b ofs
| (Vptr b ofs)  Many32          Many32          v2 := v2 = if archi.ptr64 then Vundef else Vptr b ofs
| (Vptr b ofs)  Mint64          Mint64          v2 := v2 = if archi.ptr64 then Vptr b ofs else Vundef
| (Vptr b ofs)  Mint64          Many64          v2 := v2 = if archi.ptr64 then Vptr b ofs else Vundef
| (Vptr b ofs)  Many64          Many64          v2 := v2 = Vptr b ofs
| (Vptr b ofs)  Many64          Mint64          v2 := v2 = if archi.ptr64 then Vptr b ofs else Vundef
| (Vptr b ofs)  _               _               v2 := v2 = Vundef
| (Vlong n)     Mint64          Mint64          v2 := v2 = Vlong n
| (Vlong n)     Mint64          Mfloat64        v2 := v2 = float.of_bits n
| (Vlong n)     Many64          Many64          v2 := v2 = Vlong n
| (Vlong n)     Mint8signed     _               v2 := v2 = Vundef
| (Vlong n)     Mint8unsigned   _               v2 := v2 = Vundef
| (Vlong n)     Mint16signed    _               v2 := v2 = Vundef
| (Vlong n)     Mint16unsigned  _               v2 := v2 = Vundef
| (Vlong n)     Mint32          _               v2 := v2 = Vundef
| (Vlong n)     Mfloat32        _               v2 := v2 = Vundef
| (Vlong n)     Mfloat64        _               v2 := v2 = Vundef
| (Vlong n)     Many32          _               v2 := v2 = Vundef
| (Vlong n)     _               _               v2 := true /- nothing meaningful to say about v2 -/
| (Vfloat f)    Mfloat64        Mfloat64        v2 := v2 = Vfloat f
| (Vfloat f)    Mfloat64        Mint64          v2 := v2 = float.to_bits f
| (Vfloat f)    Many64          Many64          v2 := v2 = Vfloat f
| (Vfloat f)    Mint8signed     _               v2 := v2 = Vundef
| (Vfloat f)    Mint8unsigned   _               v2 := v2 = Vundef
| (Vfloat f)    Mint16signed    _               v2 := v2 = Vundef
| (Vfloat f)    Mint16unsigned  _               v2 := v2 = Vundef
| (Vfloat f)    Mint32          _               v2 := v2 = Vundef
| (Vfloat f)    Mfloat32        _               v2 := v2 = Vundef
| (Vfloat f)    Mint64          _               v2 := v2 = Vundef
| (Vfloat f)    Many32          _               v2 := v2 = Vundef
| (Vfloat f)    _               _               v2 := true   /- nothing interesting to say about v2 -/
| (Vsingle f)   Mfloat32        Mfloat32        v2 := v2 = Vsingle f
| (Vsingle f)   Mfloat32        Mint32          v2 := v2 = float32.to_bits f
| (Vsingle f)   Many32          Many32          v2 := v2 = Vsingle f
| (Vsingle f)   Many64          Many64          v2 := v2 = Vsingle f
| (Vsingle f)   Mint8signed     _               v2 := v2 = Vundef
| (Vsingle f)   Mint8unsigned   _               v2 := v2 = Vundef
| (Vsingle f)   Mint16signed    _               v2 := v2 = Vundef
| (Vsingle f)   Mint16unsigned  _               v2 := v2 = Vundef
| (Vsingle f)   Mint32          _               v2 := v2 = Vundef
| (Vsingle f)   Mint64          _               v2 := v2 = Vundef
| (Vsingle f)   Mfloat64        _               v2 := v2 = Vundef
| (Vsingle f)   Many64          _               v2 := v2 = Vundef
| (Vsingle f)   _               _               v2 := true /- nothing interesting to say about v2 -/

theorem decode_val_undef (bl chunk) : decode_val chunk (Undef :: bl) = Vundef := sorry'

theorem proj_bytes_inj_value (q v) : proj_bytes (inj_value q v) = none := sorry'

lemma decode_encode_val_general (v chunk1 chunk2) :
  decode_encode_val v chunk1 chunk2 (decode_val chunk2 (encode_val chunk1 v)) := sorry'

lemma decode_encode_val_similar {v1 chunk1 chunk2 v2} :
  decode_encode_val v1 chunk1 chunk2 v2 →
  chunk1.type = chunk2.type →
  chunk1.size = chunk2.size →
  v2 = val.load_result chunk2 v1 := sorry'

lemma decode_val_type (chunk cl) :
  val.has_type (decode_val chunk cl) chunk.type := sorry'

lemma encode_val_int8_signed_unsigned (v) : encode_val Mint8signed v = encode_val Mint8unsigned v := sorry'

lemma encode_val_int16_signed_unsigned (v) : encode_val Mint16signed v = encode_val Mint16unsigned v := sorry'

lemma encode_val_int8_zero_ext (n : int32) :
  encode_val Mint8unsigned (Vint (zero_ext 8 n)) = encode_val Mint8unsigned (Vint n) := sorry'

lemma encode_val_int8_sign_ext (n) :
  encode_val Mint8signed (Vint (sign_ext W8 n)) = encode_val Mint8signed (Vint n) := sorry'

lemma encode_val_int16_zero_ext (n) :
  encode_val Mint16unsigned (Vint (zero_ext 16 n)) = encode_val Mint16unsigned (Vint n) := sorry'

lemma encode_val_int16_sign_ext (n) :
  encode_val Mint16signed (Vint (sign_ext W16 n)) = encode_val Mint16signed (Vint n) := sorry'

lemma decode_val_cast_type (v : val) : memory_chunk → Prop
| Mint8signed    := v = val.sign_ext W8 v
| Mint8unsigned  := v = val.zero_ext 8 v
| Mint16signed   := v = val.sign_ext W16 v
| Mint16unsigned := v = val.zero_ext 16 v
| _              := true

lemma decode_val_cast (chunk l) : decode_val_cast_type (decode_val chunk l) chunk := sorry'

/- Pointers cannot be forged. -/

def quantity_chunk : memory_chunk → quantity
| Mint64   := Q64
| Mfloat64 := Q64
| Many64   := Q64
| _        := Q32

def shape_encoding.b.type : val → Prop
| (Vint _)    := true
| (Vlong _)   := true
| (Vfloat _)  := true
| (Vsingle _) := true
| _           := false

inductive shape_encoding (chunk : memory_chunk) (v : val) : list memval → Prop
| f (q i) : ∀ mvl,
      (chunk = Mint32 ∨ chunk = Many32 ∨ chunk = Mint64 ∨ chunk = Many64) →
      q = quantity_chunk chunk →
      i+1 = q.size →
      (∀ mv ∈ mvl, ∃ j, mv = Fragment v q j ∧ j+1 ≠ q.size) →
      shape_encoding (Fragment v q i :: mvl)
| b (b mvl) : memdata.shape_encoding.b.type v →
      (∀ mv ∈ mvl, ∃ b', mv = Byte b') → shape_encoding (Byte b :: mvl)
| u (mvl) : (∀ mv ∈ mvl, mv = Undef) → shape_encoding (Undef :: mvl)

lemma encode_val_shape (chunk v) : shape_encoding chunk v (encode_val chunk v) := sorry'

inductive shape_decoding (chunk : memory_chunk) : list memval → val → Prop
| f (v q i) : ∀ mvl,
      (chunk = Mint32 ∨ chunk = Many32 ∨ chunk = Mint64 ∨ chunk = Many64) →
      q = quantity_chunk chunk →
      i+1 = q.size →
      (∀ mv ∈ mvl, ∃ j, mv = Fragment v q j ∧ j+1 ≠ q.size) →
      shape_decoding (Fragment v q i :: mvl) (val.load_result chunk v)
| b (b mvl v) : shape_encoding.b.type v →
      (∀ mv ∈ mvl, ∃ b', mv = Byte b') →
      shape_decoding (Byte b :: mvl) v
| u (mvl) : shape_decoding mvl Vundef

lemma decode_val_shape (chunk mv1 mvl) :
  shape_decoding chunk (mv1 :: mvl) (decode_val chunk (mv1 :: mvl)) := sorry'

/- * Compatibility with memory injections -/

/- Relating two memory values according to a memory injection. -/

inductive memval_inject (f : meminj) : memval → memval → Prop
| byte (n) : memval_inject (Byte n) (Byte n)
| frag (v1 v2 q n) : inject f v1 v2 →
      memval_inject (Fragment v1 q n) (Fragment v2 q n)
| undef (mv) : memval_inject Undef mv

lemma memval_inject.incr (f f' v1 v2) :
  memval_inject f v1 v2 → inject_incr f f' → memval_inject f' v1 v2 := sorry'

/- [decode_val], applied to lists of memory values that are pairwise
  related by [memval_inject], returns values that are related by [inject]. -/

lemma proj_bytes_inject (f vl vl') :
  list.forall2 (memval_inject f) vl vl' →
  ∀ bl, proj_bytes vl = some bl → proj_bytes vl' = some bl := sorry'

lemma check_value_inject (f vl vl') :
  list.forall2 (memval_inject f) vl vl' →
  ∀ v v' q n,
  check_value v q n vl →
  inject f v v' → v ≠ Vundef →
  check_value v' q n vl' := sorry'

lemma proj_value_inject (f q vl1 vl2) :
  list.forall2 (memval_inject f) vl1 vl2 →
  inject f (proj_value q vl1) (proj_value q vl2) := sorry'

lemma proj_bytes_not_inject (f vl vl') :
  list.forall2 (memval_inject f) vl vl' →
  proj_bytes vl = none → proj_bytes vl' ≠ none → Undef ∈ vl := sorry'

lemma check_value_undef (n q v vl) :
  Undef ∈ vl → ¬ check_value v q n vl := sorry'

lemma proj_value_undef (q vl) : Undef ∈ vl → proj_value q vl = Vundef := sorry'

theorem decode_val_inject (f vl1 vl2 chunk) :
  list.forall2 (memval_inject f) vl1 vl2 →
  inject f (decode_val chunk vl1) (decode_val chunk vl2) := sorry'

/- Symmetrically, [encode_val], applied to values related by [inject],
  returns lists of memory values that are pairwise
  related by [memval_inject]. -/

lemma inj_bytes_inject (f bl) :
  list.forall2 (memval_inject f) (inj_bytes bl) (inj_bytes bl) := sorry'

lemma repeat_Undef_inject_any (f) (vl : list memval) :
  list.forall2 (memval_inject f) (list.repeat Undef vl.length) vl := sorry'

lemma repeat_Undef_inject_encode_val (f) (chunk : memory_chunk) (v) :
  list.forall2 (memval_inject f) (list.repeat Undef chunk.size) (encode_val chunk v) := sorry'

lemma repeat_Undef_inject_self (f n) :
  list.forall2 (memval_inject f) (list.repeat Undef n) (list.repeat Undef n) := sorry'

lemma inj_value_inject (f v1 v2 q) : inject f v1 v2 →
  list.forall2 (memval_inject f) (inj_value q v1) (inj_value q v2) := sorry'

theorem encode_val_inject (f v1 v2 chunk) : inject f v1 v2 →
  list.forall2 (memval_inject f) (encode_val chunk v1) (encode_val chunk v2) := sorry'

def memval_lessdef : memval → memval → Prop := memval_inject inject_id

lemma memval_lessdef_refl (mv) : memval_lessdef mv mv :=
by dsimp [memval_lessdef]; cases mv; constructor; apply val_inject_id.2; constructor

/- [memval_inject] and compositions -/

lemma memval_inject_compose {f f' v1 v2 v3} :
  memval_inject f v1 v2 → memval_inject f' v2 v3 →
  memval_inject (f.comp f') v1 v3 := sorry'

/- * Breaking 64-bit memory accesses into two 32-bit accesses -/

lemma length_proj_bytes {l b} : proj_bytes l = some b → b.length = l.length := sorry'

lemma proj_bytes_append (l2 l1) : proj_bytes (l1 ++ l2) =
  do b1 ← proj_bytes l1, b2 ← proj_bytes l2, some (b1 ++ b2) := sorry'

lemma decode_val_int64 {l1 l2 : list memval} : l1.length = 4 → l2.length = 4 → ¬ archi.ptr64 →
  lessdef (decode_val Mint64 (l1 ++ l2)) (long_of_words
    (decode_val Mint32 (if archi.big_endian then l1 else l2))
    (decode_val Mint32 (if archi.big_endian then l2 else l1))) := sorry'

lemma encode_val_int64 (v) : ¬ archi.ptr64 → encode_val Mint64 v =
     encode_val Mint32 (if archi.big_endian then hiword v else loword v)
  ++ encode_val Mint32 (if archi.big_endian then loword v else hiword v) := sorry'

end memdata