import .ast .errors .linking

/- Type expressions for the Compcert C and Clight languages -/

namespace ctypes
open ast maps errors linking
open ast.external_function ast.memory_chunk

/- Compcert C types are similar to those of C.  They include numeric types,
  pointers, arrays, function types, and composite types (struct and
  union).  Numeric types (integers and floats) fully specify the
  bit size of the type.  An integer type is a pair of a signed/unsigned
  flag and a bit size: 8, 16, or 32 bits, or the special [IBool] size
  standing for the C99 [_Bool] type.  64-bit integers are treated separately. -/


inductive signedness : Type
| Signed : signedness
| Unsigned : signedness
open signedness

inductive intsize : Type
| I8 : intsize
| I16 : intsize
| I32 : intsize
| IBool : intsize
open intsize

/- Float types come in two sizes: 32 bits (single precision)
  and 64-bit (double precision). -/

inductive floatsize : Type
| F32 : floatsize
| F64 : floatsize
open floatsize

/- Every type carries a set of attributes.  Currently, only two
  attributes are modeled: [volatile] and [_Alignas(n)] (from ISO C 2011). -/

structure attr : Type :=
(attr_volatile : bool)
(attr_alignas : option ℕ)  /- log2 of required alignment -/

instance attr_eq : decidable_eq attr := by tactic.mk_dec_eq_instance

def noattr : attr := { attr_volatile := false, attr_alignas := none }

/- The syntax of type expressions.  some points to note:
- Array types [Tarray n] carry the size [n] of the array.
  Arrays with unknown sizes are represented by pointer types.
- Function types [Tfunction targs tres] specify the number and types
  of the function arguments (list [targs]), and the type of the
  function result ([tres]).  Variadic functions and old-style unprototyped
  functions are not supported.
-/

inductive type : Type
| Tvoid : type                                    /- the [void] type -/
| Tint : intsize → signedness → attr → type    /- integer types -/
| Tlong : signedness → attr → type              /- 64-bit integer types -/
| Tfloat : floatsize → attr → type              /- floating-point types -/
| Tpointer : type → attr → type                 /- pointer types ([*ty]) -/
| Tarray : type → ℕ → attr → type              /- array types ([ty[len]]) -/
| Tfunction : list type → type → calling_convention → type    /- function types -/
| Tstruct : ident → attr → type                 /- struct types -/
| Tunion : ident → attr → type                  /- union types -/
export type

instance intsize_eq : decidable_eq intsize := by tactic.mk_dec_eq_instance

instance type_eq : decidable_eq type := sorry' --by tactic.mk_dec_eq_instance

/- Extract the attributes of a type. -/

def attr_of_type : type → attr
| Tvoid                   := noattr
| (Tint sz si a)          := a
| (Tlong si a)            := a
| (Tfloat sz a)           := a
| (Tpointer elt a)        := a
| (Tarray elt sz a)       := a
| (Tfunction args res cc) := noattr
| (Tstruct id a)          := a
| (Tunion id a)           := a

/- Change the top-level attributes of a type -/

def change_attributes (f : attr → attr) : type → type
| (Tint sz si a)          := Tint sz si (f a)
| (Tlong si a)            := Tlong si (f a)
| (Tfloat sz a)           := Tfloat sz (f a)
| (Tpointer elt a)        := Tpointer elt (f a)
| (Tarray elt sz a)       := Tarray elt sz (f a)
| (Tstruct id a)          := Tstruct id (f a)
| (Tunion id a)           := Tunion id (f a)
| ty                      := ty

/- Erase the top-level attributes of a type -/

def remove_attributes (ty : type) : type :=
  change_attributes (λ_, noattr) ty

/- Add extra attributes to the top-level attributes of a type -/

def attr_union (a1 a2 : attr) : attr :=
{ attr_volatile := a1.attr_volatile || a2.attr_volatile,
  attr_alignas :=
    match a1.attr_alignas, a2.attr_alignas with
    | none, al := al
    | al, none := al
    | some n1, some n2 := some (max n1 n2)
    end }

def merge_attributes (ty : type) (a : attr) : type :=
change_attributes (attr_union a) ty


/- Syntax for [struct] and [union] definitions.  [struct] and [union]
  are collectively called "composites".  Each compilation unit
  comes with a list of top-level definitions of composites. -/

inductive struct_or_union : Type | struct | union

instance struct_or_union_eq : decidable_eq struct_or_union := by tactic.mk_dec_eq_instance

def members : Type := list (ident × type).
instance : has_mem (ident × type) members := ⟨@has_mem.mem _ (list _) _⟩

structure composite_definition : Type :=
(id : ident) (su : struct_or_union) (m : members) (a : attr)

def name_composite_def : composite_definition → ident :=
composite_definition.id

instance composite_def_eq : decidable_eq composite_definition := by tactic.mk_dec_eq_instance

/- For type-checking, compilation and semantics purposes, the composite
  definitions are collected in the following [composite_env] environment.
  The [composite] record contains additional information compared with
  the [composite_definition], such as size and alignment information. -/

structure composite : Type :=
(co_su : struct_or_union)
(co_members : members)
(co_attr : attr)
(co_sizeof : ℕ)
(co_alignof : ℕ)
(co_rank : ℕ)
(co_alignof_two_p : ∃ n, co_alignof = 2^n)
(co_sizeof_alignof : co_alignof ∣ co_sizeof)
open composite

def composite_env : Type := PTree composite

/- * Operations over types -/

/- ** Conversions -/

def type_int32s := Tint I32 Signed noattr
def type_bool := Tint IBool Signed noattr

/- The usual unary conversion.  Promotes small integer types to [signed int32]
  and degrades array types and function types to pointer types.
  Attributes are erased. -/

def typeconv (ty : type) : type :=
match ty with
| Tint I8 _ _     := Tint I32 Signed noattr
| Tint I16 _ _    := Tint I32 Signed noattr
| Tint IBool _ _  := Tint I32 Signed noattr
| Tarray t sz a   := Tpointer t noattr
| Tfunction _ _ _ := Tpointer ty noattr
| _               := remove_attributes ty
end

/- Default conversion for arguments to an unprototyped or variadic function.
  Like [typeconv] but also converts single floats to double floats. -/

def default_argument_conversion (ty : type) : type :=
match ty with
| Tint I8 _ _     := Tint I32 Signed noattr
| Tint I16 _ _    := Tint I32 Signed noattr
| Tint IBool _ _  := Tint I32 Signed noattr
| Tfloat _ _      := Tfloat F64 noattr
| Tarray t sz a   := Tpointer t noattr
| Tfunction _ _ _ := Tpointer ty noattr
| _               := remove_attributes ty
end

/- ** Complete types -/

/- A type is complete if it fully describes an object.
  All struct and union names appearing in the type must be defined,
  unless they occur under a pointer or function type.  [void] and
  function types are incomplete types. -/

def complete_type (env : composite_env) : type → bool
| Tvoid             := ff
| (Tint _ _ _)      := tt
| (Tlong _ _)       := tt
| (Tfloat _ _)      := tt
| (Tpointer _ _)    := tt
| (Tarray t' _ _)   := complete_type t'
| (Tfunction _ _ _) := ff
| (Tstruct id _)    := (env^!id).is_some
| (Tunion id _)     := (env^!id).is_some

def complete_or_function_type (env : composite_env) : type → bool
| (Tfunction _ _ _) := true
| t := complete_type env t

/- ** Alignment of a type -/

/- Adjust the natural alignment [al] based on the attributes [a] attached
  to the type.  If an "alignas" attribute is given, use it as alignment
  in preference to [al]. -/

def align_attr (a : attr) (al : ℕ) : ℕ :=
match a.attr_alignas with
| some l := 2^l
| none := al
end

/- In the ISO C standard, alignment is defined only for complete
  types.  However, it is convenient that [alignof] is a total
  function.  For incomplete types, it returns 1. -/

def alignof_inner (env : composite_env) : type → ℕ
| Tvoid             := 1
| (Tint I8 _ _)     := 1
| (Tint I16 _ _)    := 2
| (Tint I32 _ _)    := 4
| (Tint IBool _ _)  := 1
| (Tlong _ _)       := archi.align_int64
| (Tfloat F32 _)    := 4
| (Tfloat F64 _)    := archi.align_float64
| (Tpointer _ _)    := if archi.ptr64 then 8 else 4
| (Tarray t' _ _)   := align_attr (attr_of_type t') (alignof_inner t')
| (Tfunction _ _ _) := 1
| (Tstruct id _)    := match env^!id with some co := co_alignof co | none := 1 end
| (Tunion id _)     := match env^!id with some co := co_alignof co | none := 1 end

def alignof (env : composite_env) (t : type) : ℕ :=
align_attr (attr_of_type t) (alignof_inner env t)

theorem align_attr_two_p (al a) :
  (∃ n, al = 2^n) →
  (∃ n, align_attr a al = 2^n) := sorry'

theorem alignof_two_p (env t) : ∃ n, alignof env t = 2^n := sorry'

theorem alignof_pos (env t) : alignof env t > 0 := sorry'

/- ** Size of a type -/

/- In the ISO C standard, size is defined only for complete
  types.  However, it is convenient that [sizeof] is a total
  function.  For [void] and function types, we follow GCC and define
  their size to be 1.  For undefined structures and unions, the size is
  arbitrarily taken to be 0.
-/

def sizeof (env: composite_env) : type → ℕ
| Tvoid             := 1
| (Tint I8 _ _)     := 1
| (Tint I16 _ _)    := 2
| (Tint I32 _ _)    := 4
| (Tint IBool _ _)  := 1
| (Tlong _ _)       := 8
| (Tfloat F32 _)    := 4
| (Tfloat F64 _)    := 8
| (Tpointer _ _)    := if archi.ptr64 then 8 else 4
| (Tarray t' n _)   := sizeof t' * n
| (Tfunction _ _ _) := 1
| (Tstruct id _)    := match env^!id with some co := co_sizeof co | none := 0 end
| (Tunion id _)     := match env^!id with some co := co_sizeof co | none := 0 end


lemma sizeof_pos (env t) : sizeof env t >= 0 := sorry'

/- The size of a type is an integral multiple of its alignment,
  unless the alignment was artificially increased with the [__Alignas]
  attribute. -/

def naturally_aligned : type → Prop
| (Tarray t' _ a) := attr.attr_alignas a = none ∧ naturally_aligned t'
| t := attr.attr_alignas (attr_of_type t) = none

lemma sizeof_alignof_compat (env t) (h : naturally_aligned t) :
  alignof env t ∣ sizeof env t := sorry'

/- ** Size and alignment for composite definitions -/

/- The alignment for a structure or union is the max of the alignment
  of its members. -/

def alignof_composite (env : composite_env) : members → ℕ
| [] := 1
| ((id, t) :: m') := max (alignof env t) (alignof_composite m')


/- The size of a structure corresponds to its layout: fields are
  laid out consecutively, and padding is inserted to align
  each field to the alignment for its type. -/

def sizeof_struct (env : composite_env) : ℕ → members → ℕ
| cur [] := cur
| cur ((id, t) :: m') := sizeof_struct (align cur (alignof env t) + sizeof env t) m'

/- The size of an union is the max of the sizes of its members. -/

def sizeof_union (env : composite_env) : members → ℕ
| [] := 0
| ((id, t) :: m') := max (sizeof env t) (sizeof_union m')

lemma alignof_composite_two_p (env m) : ∃ n, alignof_composite env m = 2^n := sorry'

lemma alignof_composite_pos (env m a) : align_attr a (alignof_composite env m) > 0 := sorry'

lemma sizeof_struct_incr (env m cur) : cur ≤ sizeof_struct env cur m := sorry'

lemma sizeof_union_pos (env m) : 0 ≤ sizeof_union env m := sorry'

/- ** Byte offset for a field of a structure -/

/- [field_offset env id fld] returns the byte offset for field [id]
  in a structure whose members are [fld].  Fields are laid out
  consecutively, and padding is inserted to align each field to the
  alignment for its type. -/

def field_offset_rec (env : composite_env) (id : ident) : members → ℕ → res ℕ
| []                 pos := error [MSG "Unknown field ", CTX id]
| ((id', t) :: fld') pos :=
      if id = id'
      then OK (align pos (alignof env t))
      else field_offset_rec fld' (align pos (alignof env t) + sizeof env t)

def field_offset (env : composite_env) (id : ident) (fld : members) : res ℕ :=
field_offset_rec env id fld 0

def field_type (id : ident) : members → res type
| []                 := error [MSG "Unknown field ", CTX id]
| ((id', t) :: fld') := if id = id' then OK t else field_type fld'

/- some sanity checks about field offsets.  First, field offsets are
  within the range of acceptable offsets. -/

theorem field_offset_rec_in_range (env id ofs ty fld pos) :
  field_offset_rec env id fld pos = OK ofs → field_type id fld = OK ty →
  pos ≤ ofs ∧ ofs + sizeof env ty ≤ sizeof_struct env pos fld := sorry'

lemma field_offset_in_range (env fld id ofs ty) :
  field_offset env id fld = OK ofs → field_type id fld = OK ty →
  0 ≤ ofs ∧ ofs + sizeof env ty ≤ sizeof_struct env 0 fld := sorry'

/- Second, two distinct fields do not overlap -/

lemma field_offset_no_overlap (env id1 ofs1 ty1 id2 ofs2 ty2 fld) :
  field_offset env id1 fld = OK ofs1 → field_type id1 fld = OK ty1 →
  field_offset env id2 fld = OK ofs2 → field_type id2 fld = OK ty2 →
  id1 ≠ id2 → ofs1 + sizeof env ty1 ≤ ofs2 ∨ ofs2 + sizeof env ty2 ≤ ofs1 := sorry'

/- Third, if a struct is a prefix of another, the offsets of common fields
    are the same. -/

lemma field_offset_prefix (env id ofs fld2 fld1) :
  field_offset env id fld1 = OK ofs →
  field_offset env id (fld1 ++ fld2 : list _) = OK ofs := sorry'

/- Fourth, the position of each field respects its alignment. -/

lemma field_offset_aligned (env id fld ofs ty) :
  field_offset env id fld = OK ofs → field_type id fld = OK ty →
  ↑(alignof env ty) ∣ ofs := sorry'

/- ** Access modes -/

/- The [access_mode] function describes how a l-value of the given
type must be accessed:
- [By_value ch]: access by value, i.e. by loading from the address
  of the l-value using the memory chunk [ch];
- [By_reference]: access by reference, i.e. by just returning
  the address of the l-value (used for arrays and functions);
- [By_copy]: access is by reference, assignment is by copy
  (used for [struct] and [union] types)
- [By_nothing]: no access is possible, e.g. for the [void] type.
-/

inductive mode : Type
| By_value : memory_chunk → mode
| By_reference : mode
| By_copy : mode
| By_nothing : mode
open mode ast.memory_chunk

def access_mode : type → mode
| (Tint I8 Signed _)    := By_value Mint8signed
| (Tint I8 Unsigned _)  := By_value Mint8unsigned
| (Tint I16 Signed _)   := By_value Mint16signed
| (Tint I16 Unsigned _) := By_value Mint16unsigned
| (Tint I32 _ _)        := By_value Mint32
| (Tint IBool _ _)      := By_value Mint8unsigned
| (Tlong _ _)           := By_value Mint64
| (Tfloat F32 _)        := By_value Mfloat32
| (Tfloat F64 _)        := By_value Mfloat64
| (Tvoid)               := By_nothing
| (Tpointer _ _)        := By_value Mptr
| (Tarray _ _ _)        := By_reference
| (Tfunction _ _ _)     := By_reference
| (Tstruct _ _)         := By_copy
| (Tunion _ _)          := By_copy

/- For the purposes of the semantics and the compiler, a type denotes
  a volatile access if it carries the [volatile] attribute and it is
  accessed by value. -/

def type_is_volatile (ty: type) : bool :=
  match access_mode ty with
  | By_value _ := attr.attr_volatile (attr_of_type ty)
  | _          := false
  end.

/- ** Alignment for block copy operations -/

/- A variant of [alignof] for use in block copy operations.
  Block copy operations do not support alignments greater than 8,
  and require the size to be an integral multiple of the alignment. -/

def alignof_blockcopy (env : composite_env) : type → ℤ
| Tvoid             := 1
| (Tint I8 _ _)     := 1
| (Tint I16 _ _)    := 2
| (Tint I32 _ _)    := 4
| (Tint IBool _ _)  := 1
| (Tlong _ _)       := 8
| (Tfloat F32 _)    := 4
| (Tfloat F64 _)    := 8
| (Tpointer _ _)    := if archi.ptr64 then 8 else 4
| (Tarray t' _ _)   := alignof_blockcopy t'
| (Tfunction _ _ _) := 1
| (Tstruct id _ )   := match env^!id with some co := min 8 (co_alignof co) | none := 1 end
| (Tunion id _)     := match env^!id with some co := min 8 (co_alignof co) | none := 1 end

lemma alignof_blockcopy_1248 (env ty) :
  let a := alignof_blockcopy env ty in
  a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 8 := sorry'

lemma alignof_blockcopy_pos (env ty) : alignof_blockcopy env ty > 0 := sorry'

lemma sizeof_alignof_blockcopy_compat (env ty) :
  alignof_blockcopy env ty ∣ sizeof env ty := sorry'

/- Type ranks -/

/- The rank of a type is a nonnegative integer that measures the direct nesting
  of arrays, struct and union types.  It does not take into account indirect
  nesting such as a struct type that appears under a pointer or function type.
  Type ranks ensure that type expressions (ignoring pointer and function types)
  have an inductive structure. -/

def rank_type (ce : composite_env) : type → nat
| (Tarray t' _ _) := rank_type t' + 1
| (Tstruct id _) :=
  match ce^!id with
  | none := 0
  | some co := co_rank co + 1
  end
| (Tunion id _) :=
  match ce^!id with
  | none := 0
  | some co := co_rank co + 1
  end
| _ := 0

def rank_members (ce : composite_env) : members → nat
| [] := 0
| ((id, t) :: m) := max (rank_type ce t) (rank_members m)

/- ** C types and back-end types -/

/- Extracting a type list from a function parameter declaration. -/

def type_of_params : list (ident × type) → list type
| [] := []
| ((id, ty) :: rem) := ty :: type_of_params rem

/- Translating C types to Cminor types and function signatures. -/

def typ_of_type : type → ast.typ
| Tvoid             := ast.typ.Tint
| (Tint _ _ _)      := ast.typ.Tint
| (Tlong _ _)       := ast.typ.Tlong
| (Tfloat F32 _)    := ast.typ.Tsingle
| (Tfloat F64 _)    := ast.typ.Tfloat
| (Tpointer _ _)    := ast.typ.Tptr
| (Tarray _ _ _)    := ast.typ.Tptr
| (Tfunction _ _ _) := ast.typ.Tptr
| (Tstruct _ _)     := ast.typ.Tptr
| (Tunion _ _)      := ast.typ.Tptr

def opttyp_of_type (t : type) : option ast.typ :=
  if t = Tvoid then none else some (typ_of_type t)

def typlist_of_typelist (l : list type) : list ast.typ := l.map typ_of_type

def signature_of_type (args : list type) (res : type) (cc : calling_convention) : signature :=
signature.mk (args.map typ_of_type) (opttyp_of_type res) cc

/- * Construction of the composite environment -/

def sizeof_composite (env : composite_env) : struct_or_union → members → ℕ
| struct_or_union.struct := sizeof_struct env 0
| struct_or_union.union  := sizeof_union env


lemma sizeof_composite_pos (env su m) : 0 ≤ sizeof_composite env su m := sorry'

def complete_members (env : composite_env) : members → bool
| [] := true
| ((id, t) :: m') := complete_type env t && complete_members m'

lemma complete_member (env) (id : ident) (t m) :
  (id, t) ∈ m →
  complete_members env m = true →
  complete_type env t = true := sorry'

/- Convert a composite def to its internal representation.
  The size and alignment of the composite are determined at this time.
  The alignment takes into account the [__Alignas] attributes
  associated with the def.  The size is rounded up to a multiple
  of the alignment.

  The conversion fails if a type of a member is not complete.  This rules
  out incorrect recursive definitions such as
<<
    struct s { int x; struct s next; }
>>
  Here, when we process the def of [struct s], the identifier [s]
  is not bound yet in the composite environment, hence field [next]
  has an incomplete type.  However, recursions that go through a pointer type
  are correctly handled:
<<
    struct s { int x; struct s * next; }
>>
  Here, [next] has a pointer type, which is always complete, even though
  [s] is not yet bound to a composite.
-/

def composite_of_def (env : composite_env) (id : ident) (su : struct_or_union)
   (m : members) (a : attr) : res composite :=
match env^!id, complete_members env m with
| some _, _ :=
    error [MSG "Multiple definitions of struct or union ", CTX id]
| none, ff :=
    error [MSG "Incomplete struct or union ", CTX id]
| none, tt :=
    let al := align_attr a (alignof_composite env m) in
    OK { co_su := su,
         co_members := m,
         co_attr := a,
         co_sizeof := align (sizeof_composite env su m) al,
         co_alignof := al,
         co_rank := rank_members env m,
         co_alignof_two_p := sorry',
         co_sizeof_alignof := sorry' }
end

/- The composite environment for a program is obtained by entering
  its composite definitions in sequence.  The definitions are assumed
  to be listed in dependency order: the def of a composite
  must precede all uses of this composite, unless the use is under
  a pointer or function type. -/

def add_composite_definitions : composite_env →
  list composite_definition → res composite_env
| env [] := OK env
| env (⟨id, su, m, a⟩ :: defs) :=
    do co ← composite_of_def env id su m a,
    add_composite_definitions (PTree.set id co env) defs

def build_composite_env (defs: list composite_definition) :=
add_composite_definitions (∅ : PTree _) defs.

/- Stability properties for alignments, sizes, and ranks.  If the type is
  complete in a composite environment [env], its size, alignment, and rank
  are unchanged if we add more definitions to [env]. -/

section stability

variables env env': composite_env
variable h : ∀ id co, (env^!id) = some co → (env'^!id) = some co

lemma alignof_stable (t) : complete_type env t →
  alignof env' t = alignof env t := sorry'

lemma sizeof_stable (t) : complete_type env t →
  sizeof env' t = sizeof env t := sorry'

lemma complete_type_stable (t) : complete_type env t →
  complete_type env' t := sorry'

lemma rank_type_stable (t) : complete_type env t →
  rank_type env' t = rank_type env t := sorry'

lemma alignof_composite_stable (m) : complete_members env m →
  alignof_composite env' m = alignof_composite env m := sorry'

lemma sizeof_struct_stable (m pos) : complete_members env m →
  sizeof_struct env' pos m = sizeof_struct env pos m := sorry'

lemma sizeof_union_stable (m) : complete_members env m →
  sizeof_union env' m = sizeof_union env m := sorry'

lemma sizeof_composite_stable (su m) : complete_members env m →
  sizeof_composite env' su m = sizeof_composite env su m := sorry'

lemma complete_members_stable (m) : complete_members env m →
  complete_members env' m := sorry'

lemma rank_members_stable (m) : complete_members env m →
  rank_members env' m = rank_members env m := sorry'

end stability

lemma add_composite_definitions_incr (id co defs env1 env2) :
  add_composite_definitions env1 defs = OK env2 →
  (env1^!id) = some co → (env2^!id) = some co := sorry'

/- It follows that the sizes and alignments contained in the composite
  environment produced by [build_composite_env] are consistent with
  the sizes and alignments of the members of the composite types. -/

structure composite_consistent (env : composite_env) (co : composite) : Prop :=
(co_consistent_complete :
    complete_members env (co_members co))
(co_consistent_alignof :
    co_alignof co = align_attr (co_attr co) (alignof_composite env (co_members co)))
(co_consistent_sizeof:
    co_sizeof co = align (sizeof_composite env (co_su co) (co_members co)) (co_alignof co))
(co_consistent_rank:
    co_rank co = rank_members env (co_members co))

def composite_env_consistent (env: composite_env) : Prop :=
  ∀ id co, (env^!id) = some co → composite_consistent env co

lemma composite_consistent_stable (env env': composite_env)
  (ext : ∀ id co, (env^!id) = some co → (env'^!id) = some co)
  (co) : composite_consistent env co → composite_consistent env' co := sorry'

lemma composite_of_def_consistent (env id su m a co) :
  composite_of_def env id su m a = OK co →
  composite_consistent env co := sorry'

theorem build_composite_env_consistent (defs env) :
  build_composite_env defs = OK env → composite_env_consistent env := sorry'

/- Moreover, every composite def is reflected in the composite environment. -/

theorem build_composite_env_charact (id su m a defs env) :
  build_composite_env defs = OK env →
  composite_definition.mk id su m a ∈ defs →
  ∃ co, (env^!id) = some co ∧ co_members co = m ∧
        co_attr co = a ∧ co_su co = su := sorry'

theorem build_composite_env_domain (env defs id co) :
  build_composite_env defs = OK env →
  (env^!id) = some co →
  composite_definition.mk id (co_su co) (co_members co) (co_attr co) ∈ defs := sorry'

/- As a corollay, in a consistent environment, the rank of a composite type
  is strictly greater than the ranks of its member types. -/

theorem rank_type_members (ce id t m) : (id, t) ∈ m →
  rank_type ce t ≤ rank_members ce m := sorry'

lemma rank_struct_member (ce id a co id1 t1) :
  composite_env_consistent ce →
  (ce^!id) = some co →
  (id1, t1) ∈ co_members co →
  rank_type ce t1 < rank_type ce (Tstruct id a) := sorry'

lemma rank_union_member (ce id a co id1 t1) :
  composite_env_consistent ce →
  (ce^!id) = some co →
  (id1, t1) ∈ co_members co →
  rank_type ce t1 < rank_type ce (Tunion id a) := sorry'

/- * Programs and compilation units -/

/- The definitions in this section are parameterized over a type [F] of 
  internal function definitions, so that they apply both to CompCert C and to Clight. -/

section programs

/- Functions can either be defined ([Internal]) or declared as
  external functions ([External]). -/

inductive fundef (F : Type) : Type
| Internal : F → fundef
| External {} : external_function → list type → type → calling_convention → fundef

/- A program, or compilation unit, is composed of:
- a list of definitions of functions and global variables;
- the names of functions and global variables that are public (not static);
- the name of the function that acts as entry point ("main" function).
- a list of definitions for structure and union names
- the corresponding composite environment
- a proof that this environment is consistent with the definitions. -/

structure program (F : Type) : Type :=
(defs: list (ident × globdef (fundef F) type))
(public: list ident)
(main: ident)
(types: list composite_definition)
(comp_env: composite_env)
(comp_env_eq: build_composite_env types = OK comp_env)

def program_of_program {F} (p : program F) : ast.program (fundef F) type :=
{ defs := p.defs,
  public := p.public,
  main := p.main }

instance {F} : has_coe (program F) (ast.program (fundef F) type) := ⟨program_of_program⟩

def make_program {F} (types: list composite_definition)
                     (defs: list (ident × globdef (fundef F) type))
                     (public: list ident)
                     (main: ident) : res (program F) :=
match _, rfl : ∀ r, build_composite_env types = r → _ with
| error e, h := error e
| OK ce, h :=
  OK { defs := defs,
       public := public,
       main := main,
       types := types,
       comp_env := ce,
       comp_env_eq := h }
end

end programs
open fundef

/- * Separate compilation and linking -/

/- ** Linking types -/

instance linker_types : linker type :=
{ link := λ t1 t2, if t1 = t2 then some t1 else none,
  linkorder := (=),
  linkorder_refl := eq.refl,
  linkorder_trans := @eq.trans _,
  link_linkorder := λt1 t2 t3, begin
    by_cases (t1 = t2) with h1; intro h2; simp [h1] at h2,
    { injection h2, exact ⟨h1.trans h, h⟩ },
    { contradiction } end }

/- ** Linking composite definitions -/

def check_compat_composite (l : list composite_definition) (cd : composite_definition) : bool :=
l.all (λ cd', if name_composite_def cd' = name_composite_def cd then cd = cd' else tt)

def filter_redefs (l1 l2 : list composite_definition) :=
let names1 := l1.map name_composite_def in
l2.filter (λ cd, name_composite_def cd ∉ names1)

def link_composite_defs (l1 l2 : list composite_definition) : option (list composite_definition) :=
if l1.all (check_compat_composite l2)
then some (l1 ++ filter_redefs l1 l2)
else none

lemma link_composite_def_inv {l1 l2 l} (h : link_composite_defs l1 l2 = some l) :
    (∀ cd1 ∈ l1, ∀ cd2 ∈ l2, name_composite_def cd2 = name_composite_def cd1 → cd2 = cd1)
  ∧ l = l1 ++ filter_redefs l1 l2
  ∧ (∀ {x}, x ∈ l ↔ x ∈ l1 ∨ x ∈ l2) := sorry'

instance Linker_composite_defs : linker (list composite_definition) :=
{ link := link_composite_defs,
  linkorder := (⊆),
  linkorder_refl := list.subset.refl,
  linkorder_trans := @list.subset.trans _,
  link_linkorder := λl1 l2 l h,
    let ⟨_, _, C⟩ := link_composite_def_inv h in
    ⟨λx h, C.2 (or.inl h), λx h, C.2 (or.inr h)⟩ }

/- Connections with [build_composite_env]. -/

lemma add_composite_definitions_append (l1 l2 env env'') :
  add_composite_definitions env (l1 ++ l2) = OK env'' ↔
  ∃ env', add_composite_definitions env l1 = OK env' ∧
          add_composite_definitions env' l2 = OK env'' := sorry'

lemma composite_of_def_eq (env id co) :
  composite_consistent env co →
  (env^!id) = none →
  composite_of_def env id (co_su co) (co_members co) (co_attr co) = OK co := sorry'

lemma composite_consistent_unique {env co1 co2} :
  composite_consistent env co1 →
  composite_consistent env co2 →
  co_su co1 = co_su co2 →
  co_members co1 = co_members co2 →
  co_attr co1 = co_attr co2 →
  co1 = co2 := sorry'

lemma composite_of_def_stable {env env'}
  (ext : ∀ id co, (env^!id) = some co → (env'^!id) = some co)
  {id su m a co}
  (hn : (env'^!id) = none)
  (ce : composite_of_def env id su m a = OK co) :
  composite_of_def env' id su m a = OK co := sorry'

def link_add_composite_definitions {l0 env0}
  (hl0 : build_composite_env l0 = OK env0) :
  ∀ {l env1 env1' env2}
  (acd : add_composite_definitions env1 l = OK env1')
  (agree1 : ∀ id co, (env1^!id) = some co → (env2^!id) = some co)
  (agree0 : ∀ id co, (env0^!id) = some co → (env2^!id) = some co)
  (agree2 : ∀ id : ident, (env2^!id) = if id ∈ l0.map name_composite_def then env0^!id else env1^!id)
  (uniq : ∀ cd1 ∈ l0, ∀ cd2 ∈ l, name_composite_def cd2 = name_composite_def cd1 → cd2 = cd1),
  {env2' // add_composite_definitions env2 (filter_redefs l0 l) = OK env2' ∧
    (∀ (id : ident) co, (env1'^!id) = some co → (env2'^!id) = some co) ∧
    (∀ (id : ident) co, (env0^!id) = some co → (env2'^!id) = some co)} :=
begin
  dsimp [filter_redefs], intro l, induction l with co l IH; intros,
  { note : OK env1 = OK env1' := acd, injection this with this,
    rw -this, exact ⟨env2, rfl, agree1, agree0⟩ },
  cases co with id su m a,
  simp [add_composite_definitions] at acd,
  revert acd,
  ginduction composite_of_def env1 id su m a with h co; intro,
  { by_cases name_composite_def ⟨id, su, m, a⟩ ∉ list.map name_composite_def l0 with hel;
    simp [hel, list.filter, add_composite_definitions];
    simp [name_composite_def] at hel,
    { note i2 := agree2 id,
      simp [name_composite_def, hel] at i2,
      exact let ⟨env2', _⟩ := @IH _ _ (PTree.set id co env2) acd sorry' sorry' sorry' sorry' in
      ⟨env2', sorry'⟩
    },
    { note i2 := agree2 id,
      simp [name_composite_def, decidable.by_contradiction hel] at i2,
      exact let ⟨env2', _⟩ := @IH _ _ env2 acd sorry' sorry' sorry' sorry' in
      ⟨env2', sorry'⟩ } },
  { note := (acd : error _ = OK _), contradiction }
end

def link_build_composite_env {l1 l2 l env1 env2}
  (hl1 : build_composite_env l1 = OK env1)
  (hl2 : build_composite_env l2 = OK env2)
  (hl : link l1 l2 = some l) :
  {env // build_composite_env l = OK env ∧
    (∀ (id : ident) co, (env1^!id) = some co → (env^!id) = some co) ∧
    (∀ (id : ident) co, (env2^!id) = some co → (env^!id) = some co)} :=
let ⟨A, B, C⟩ := link_composite_def_inv hl in
let ⟨env, P, Q, R⟩ := begin
  apply link_add_composite_definitions,
  { exact hl1 },
  { exact hl2 },
  { intros, rw PTree.gempty at a, contradiction },
  { intros, assumption },
  { intros,
    by_cases (id ∈ list.map name_composite_def l1) with hel; simp [hel],
    { rw PTree.gempty, exact sorry' } },
  { assumption }
end in
⟨env, sorry', R, Q⟩

/- ** Linking function definitions -/

def link_fundef {F : Type} : fundef F → fundef F → option (fundef F)
| (Internal _) (Internal _) := none
| (External ef1 targs1 tres1 cc1) (External ef2 targs2 tres2 cc2) :=
    if ef1 = ef2 ∧ targs1 = targs2 ∧ tres1 = tres2 ∧ cc1 = cc2
    then some (External ef1 targs1 tres1 cc1)
    else none
| (Internal f) (External (EF_external id sg) targs tres cc) := some (Internal f)
| (Internal f) (External _ targs tres cc) := none
| (External (EF_external id sg) targs tres cc) (Internal f) := some (Internal f)
| (External _ targs tres cc) (Internal f) := none

inductive linkorder_fundef {F : Type} : fundef F → fundef F → Prop
| refl (fd) : linkorder_fundef fd fd
| ext_int (f id sg targs tres cc) :
  linkorder_fundef (External (EF_external id sg) targs tres cc) (Internal f)

instance Linker_fundef (F: Type) : linker (fundef F) :=
{ link := link_fundef,
  linkorder := linkorder_fundef,
  linkorder_refl := linkorder_fundef.refl,
  linkorder_trans := λ x y z h1 h2, begin
    induction h1, exact h2,
    revert h2, generalize2 (Internal f) If hif, intro h2,
    induction h2,
    { rw -hif, apply linkorder_fundef.ext_int },
    { contradiction }
  end,
  link_linkorder := sorry' }

theorem link_fundef_either {F : Type} {f1 f2 f : fundef F} : link f1 f2 = some f → f = f1 ∨ f = f2 := sorry'

/- ** Linking programs -/

def lift_option {A : Type} : Π (opt : option A), psum { x // opt = some x } (opt = none)
| (some x) := psum.inl ⟨x, rfl⟩
| none := psum.inr rfl

def link_program {F} (p1 p2 : program F) : option (program F) :=
match link (program_of_program p1) (program_of_program p2) with
| none := none
| some p :=
  match _, rfl : ∀ o, link p1.types p2.types = o → _ with
  | none, _ := none
  | some typs, EQ :=
    let ⟨env, P, Q⟩ := link_build_composite_env p1.comp_env_eq p2.comp_env_eq EQ in
    some { defs := p.defs,
           public := p.public,
           main := p.main,
           types := typs,
           comp_env := env,
           comp_env_eq := P }
  end
end

def linkorder_program {F} (p1 p2: program F) : Prop :=
     linkorder (program_of_program p1) (program_of_program p2)
  ∧ ∀ id co, (p1.comp_env^!id) = some co → (p2.comp_env^!id) = some co

instance linker_program (F) : linker (program F) :=
{ link := link_program,
  linkorder := linkorder_program,
  linkorder_refl := λx, ⟨@linker.linkorder_refl _ _ _, λid co h, h⟩,
  linkorder_trans := λx y z ⟨p1, a1⟩ ⟨p2, a2⟩, ⟨linker.linkorder_trans p1 p2,
    λid co, a2 id co ∘ a1 id co⟩,
  link_linkorder := sorry' }

/- ** Commutation between linking and program transformations -/

section link_match_program

parameters {F G : Type}.
parameter match_fundef : fundef F → fundef G → Prop

variable link_match_fundef : ∀ {f1 tf1 f2 tf2 f},
  link f1 f2 = some f →
  match_fundef f1 tf1 → match_fundef f2 tf2 →
  ∃ tf, link tf1 tf2 = some tf ∧ match_fundef f tf.

def match_program (p : program F) (tp : program G) : Prop :=
@linking.match_program _ type _ type _ _ (λctx f tf, match_fundef f tf) eq p tp ∧
tp.types = p.types

theorem link_match_program {p1 p2 tp1 tp2 p} :
  link p1 p2 = some p → match_program p1 tp1 → match_program p2 tp2 →
  ∃ tp, link tp1 tp2 = some tp ∧ match_program p tp := sorry'

end link_match_program

end ctypes
