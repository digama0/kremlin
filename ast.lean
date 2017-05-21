import .lib .integers .maps

namespace ast
open integers maps

/- * Syntactic elements -/

/- Identifiers (names of local variables, of global symbols and functions,
  etc) are represented by the type [positive] of positive integers. -/

def ident := pos_num

instance pos_num_eq : decidable_eq pos_num := by tactic.mk_dec_eq_instance
instance ident_eq : decidable_eq ident := by tactic.mk_dec_eq_instance

/- The intermediate languages are weakly typed, using the following types: -/

inductive typ : Type
| Tint                /- 32-bit integers or pointers -/
| Tfloat              /- 64-bit double-precision floats -/
| Tlong               /- 64-bit integers -/
| Tsingle             /- 32-bit single-precision floats -/
| Tany32              /- any 32-bit value -/
| Tany64              /- any 64-bit value, i.e. any value -/

def typ.Tptr : typ := if archi.ptr64 then typ.Tlong else typ.Tint
open typ

instance typ_eq : decidable_eq typ := by tactic.mk_dec_eq_instance

def typesize : typ → ℤ
| Tint    := 4
| Tfloat  := 8
| Tlong   := 8
| Tsingle := 4
| Tany32  := 4
| Tany64  := 8

lemma typesize_pos (ty) : typesize ty > 0 :=
by cases ty; exact dec_trivial

lemma typesize_Tptr : typesize Tptr = if archi.ptr64 then 8 else 4 :=
rfl

/- All values of size 32 bits are also of type [Tany32].  All values
  are of type [Tany64].  This corresponds to the following subtyping
  relation over types. -/

def subtype : typ → typ → bool
| Tint    Tint    := tt
| Tlong   Tlong   := tt
| Tfloat  Tfloat  := tt
| Tsingle Tsingle := tt
| Tint    Tany32  := tt
| Tsingle Tany32  := tt
| Tany32  Tany32  := tt
| _       Tany64  := tt
| _       _       := ff

def subtype_list : list typ → list typ → bool
| [] [] := tt
| (ty1::tys1) (ty2::tys2) := subtype ty1 ty2 && subtype_list tys1 tys2
| _ _ := ff

/- Additionally, function definitions and function calls are annotated
  by function signatures indicating:
- the number and types of arguments;
- the type of the returned value, if any;
- additional information on which calling convention to use.

These signatures are used in particular to determine appropriate
calling conventions for the function. -/

structure calling_convention : Type := mkcallconv ::
(cc_vararg : bool)                      /- variable-arity function -/
(cc_unproto : bool)                     /- old-style unprototyped function -/
(cc_structret : bool)                   /- function returning a struct  -/

instance calling_convention_eq : decidable_eq calling_convention := by tactic.mk_dec_eq_instance

def cc_default : calling_convention :=
{ cc_vararg := false, cc_unproto := false, cc_structret := false }

structure signature : Type :=
(sig_args : list typ)
(sig_res : option typ)
(sig_cc : calling_convention)

instance signature_eq : decidable_eq signature := by tactic.mk_dec_eq_instance

/- Memory accesses (load and store instructions) are annotated by
  a ``memory chunk'' indicating the type, size and signedness of the
  chunk of memory being accessed. -/

inductive memory_chunk : Type
| Mint8signed     /- 8-bit signed integer -/
| Mint8unsigned   /- 8-bit unsigned integer -/
| Mint16signed    /- 16-bit signed integer -/
| Mint16unsigned  /- 16-bit unsigned integer -/
| Mint32          /- 32-bit integer, or pointer -/
| Mint64          /- 64-bit integer -/
| Mfloat32        /- 32-bit single-precision float -/
| Mfloat64        /- 64-bit double-precision float -/
| Many32          /- any value that fits in 32 bits -/
| Many64          /- any value -/
open memory_chunk

instance chunk_eq : decidable_eq memory_chunk := by tactic.mk_dec_eq_instance

def Mptr : memory_chunk := if archi.ptr64 then Mint64 else Mint32.

/- The type (integer/pointer or float) of a chunk. -/

def type_of_chunk : memory_chunk → typ
| Mint8signed    := Tint
| Mint8unsigned  := Tint
| Mint16signed   := Tint
| Mint16unsigned := Tint
| Mint32         := Tint
| Mint64         := Tlong
| Mfloat32       := Tsingle
| Mfloat64       := Tfloat
| Many32         := Tany32
| Many64         := Tany64

lemma type_of_Mptr : type_of_chunk Mptr = Tptr := rfl

def chunk_of_type : typ → memory_chunk
| Tint    := Mint32
| Tfloat  := Mfloat64
| Tlong   := Mint64
| Tsingle := Mfloat32
| Tany32  := Many32
| Tany64  := Many64

lemma chunk_of_Tptr : chunk_of_type Tptr = Mptr := rfl

/- Initialization data for global variables. -/

inductive init_data : Type
| int8    : int32 → init_data
| int16   : int32 → init_data
| int32   : int32 → init_data
| int64   : int64 → init_data
| float32 : float32 → init_data
| float64 : float → init_data
| space   : ℤ → init_data
| addrof  : ident → ptrofs → init_data.  /- address of symbol + offset -/

def init_data_size : init_data → ℤ
| (init_data.int8 _)     := 1
| (init_data.int16 _)    := 2
| (init_data.int32 _)    := 4
| (init_data.int64 _)    := 8
| (init_data.float32 _)  := 4
| (init_data.float64 _)  := 8
| (init_data.addrof _ _) := if archi.ptr64 then 8 else 4
| (init_data.space n)    := max n 0

def init_data_list_size : list init_data → ℤ
| [] := 0
| (i :: il') := init_data_size i + init_data_list_size il'

lemma init_data_size_pos (i) : init_data_size i ≥ 0 := sorry

lemma init_data_list_size_pos (il) : init_data_list_size il ≥ 0 := sorry

/- Information attached to global variables. -/

structure globvar (V : Type) : Type :=
(gvar_info : V)                    /- language-dependent info, e.g. a type -/
(gvar_init : list init_data)       /- initialization data -/
(gvar_readonly : bool)             /- read-only variable? (const) -/
(gvar_volatile : bool)              /- volatile variable? -/

/- Whole programs consist of:
- a collection of global definitions (name and description);
- a set of public names (the names that are visible outside
  this compilation unit);
- the name of the ``main'' function that serves as entry point in the program.

A global definition is either a global function or a global variable.
The type of function descriptions and that of additional information
for variables vary among the various intermediate languages and are
taken as parameters to the [program] type.  The other parts of whole
programs are common to all languages. -/

inductive globdef (F V : Type) : Type
| Gfun {} (f : F) : globdef
| Gvar {} (v : globvar V) : globdef
export globdef (Gfun Gvar)

structure program (F V : Type) : Type :=
(prog_defs : list (ident × globdef F V))
(prog_public : list ident)
(prog_main : ident)

def prog_defs_names {F V : Type} (p : program F V) : list ident :=
p.prog_defs.map prod.fst

/- The "definition map" of a program maps names of globals to their definitions.
  If several definitions have the same name, the one appearing last in [p.(prog_defs)] wins. -/

def prog_defmap {F V : Type} (p : program F V) : PTree.t (globdef F V) :=
PTree.of_list p.prog_defs

section defmap

variables F V : Type
variable p : program F V

lemma in_prog_defmap {id : ident} {g} : (prog_defmap p ^! id) = some g →
  (id, g) ∈ p.prog_defs := sorry

lemma prog_defmap_dom {id : ident} : id ∈ prog_defs_names p →
  ∃ g, (prog_defmap p^!id) = some g := sorry

lemma prog_defmap_unique (defs1 id g defs2) :
  p.prog_defs = defs1 ++ (id, g) :: defs2 →
  id ∉ defs2.map prod.fst →
  (prog_defmap p^!id) = some g := sorry

lemma prog_defmap_nodup {id : ident} {g} :
  (prog_defs_names p).nodup →
  (id, g) ∈ p.prog_defs →
  (prog_defmap p ^! id) = some g := sorry

end defmap

/- * External functions -/

/- For most languages, the functions composing the program are either
  internal functions, defined within the language, or external functions,
  defined outside.  External functions include system calls but also
  compiler built-in functions.  We define a type for external functions
  and associated operations. -/

inductive external_function : Type
| EF_external (name: string) (sg: signature)
   /- A system call or library function.  Produces an event
       in the trace. -/
| EF_builtin (name: string) (sg: signature)
   /- A compiler built-in function.  Behaves like an external, but
       can be inlined by the compiler. -/
| EF_runtime (name: string) (sg: signature)
   /- A function from the run-time library.  Behaves like an
       external, but must not be redefined. -/
| EF_vload (chunk: memory_chunk)
   /- A volatile read operation.  If the adress given as first argument
       points within a volatile global variable, generate an
       event and return the value found in this event.  Otherwise,
       produce no event and behave like a regular memory load. -/
| EF_vstore (chunk: memory_chunk)
   /- A volatile store operation.   If the adress given as first argument
       points within a volatile global variable, generate an event.
       Otherwise, produce no event and behave like a regular memory store. -/
| EF_malloc
   /- Dynamic memory allocation.  Takes the requested size in bytes
       as argument; returns a pointer to a fresh block of the given size.
       Produces no observable event. -/
| EF_free
   /- Dynamic memory deallocation.  Takes a pointer to a block
       allocated by an [EF_malloc] external call and frees the
       corresponding block.
       Produces no observable event. -/
| EF_memcpy (sz: ℤ) (al: ℤ)
   /- Block copy, of [sz] bytes, between addresses that are [al]-aligned. -/
| EF_annot (text: string) (targs: list typ)
   /- A programmer-supplied annotation.  Takes zero, one or several arguments,
       produces an event carrying the text and the values of these arguments,
       and returns no value. -/
| EF_annot_val (text: string) (targ: typ)
   /- Another form of annotation that takes one argument, produces
       an event carrying the text and the value of this argument,
       and returns the value of the argument. -/
| EF_inline_asm (text: string) (sg: signature) (clobbers: list string)
   /- Inline [asm] statements.  Semantically, treated like an
       annotation with no parameters ([EF_annot text nil]).  To be
       used with caution, as it can invalidate the semantic
       preservation theorem.  Generated only if [-finline-asm] is
       given. -/
| EF_debug (kind: pos_num) (text: ident) (targs: list typ)
   /- Transport debugging information from the front-end to the generated
       assembly.  Takes zero, one or several arguments like [EF_annot].
       Unlike [EF_annot], produces no observable event. -/
open external_function

/- The type signature of an external function. -/

def ef_sig : external_function → signature
| (EF_external name sg)        := sg
| (EF_builtin name sg)         := sg
| (EF_runtime name sg)         := sg
| (EF_vload chunk)             := ⟨[Tptr], some (type_of_chunk chunk), cc_default⟩
| (EF_vstore chunk)            := ⟨[Tptr, type_of_chunk chunk], none, cc_default⟩
| (EF_malloc)                  := ⟨[Tptr], some Tptr, cc_default⟩
| (EF_free)                    := ⟨[Tptr], none, cc_default⟩
| (EF_memcpy sz al)            := ⟨[Tptr, Tptr], none, cc_default⟩
| (EF_annot text targs)        := ⟨targs, none, cc_default⟩
| (EF_annot_val text targ)     := ⟨[Tptr], some targ, cc_default⟩
| (EF_inline_asm text sg clob) := sg
| (EF_debug kind text targs)   := ⟨targs, none, cc_default⟩

/- Whether an external function should be inlined by the compiler. -/

def ef_inline : external_function → bool
| (EF_external name sg)        := ff
| (EF_builtin name sg)         := tt
| (EF_runtime name sg)         := ff
| (EF_vload chunk)             := tt
| (EF_vstore chunk)            := tt
| (EF_malloc)                  := ff
| (EF_free)                    := ff
| (EF_memcpy sz al)            := tt
| (EF_annot text targs)        := tt
| (EF_annot_val text targ)     := tt
| (EF_inline_asm text sg clob) := tt
| (EF_debug kind text targs)   := tt

/- Whether an external function must reload its arguments. -/

def ef_reloads : external_function → bool
| (EF_annot text targs) := ff
| (EF_debug kind text targs) := ff
| _ := tt

/- Equality between external functions.  Used in module [Allocation]. -/

instance external_function_eq : decidable_eq external_function := by tactic.mk_dec_eq_instance

end ast