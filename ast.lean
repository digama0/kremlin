import .lib .integers .floats .maps .errors

namespace ast
open integers maps errors floats

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
by delta Tptr; cases archi.ptr64; refl

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

def proj_sig_res (s : signature) : typ :=
s.sig_res.get_or_else Tint

instance signature_eq : decidable_eq signature := by tactic.mk_dec_eq_instance

def signature_main : signature :=
{ sig_args := [], sig_res := some Tint, sig_cc := cc_default }

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
export memory_chunk

instance chunk_eq : decidable_eq memory_chunk := by tactic.mk_dec_eq_instance

def Mptr : memory_chunk := if archi.ptr64 then Mint64 else Mint32.

/- The type (integer/pointer or float) of a chunk. -/

def memory_chunk.type : memory_chunk → typ
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

lemma memory_chunk.Mptr.type : Mptr.type = Tptr :=
by delta Mptr Tptr; cases archi.ptr64; refl

def chunk_of_type : typ → memory_chunk
| Tint    := Mint32
| Tfloat  := Mfloat64
| Tlong   := Mint64
| Tsingle := Mfloat32
| Tany32  := Many32
| Tany64  := Many64

lemma chunk_of_Tptr : chunk_of_type Tptr = Mptr :=
by delta Mptr Tptr; cases archi.ptr64; refl

/- * Properties of memory chunks -/

/- Memory reads and writes are performed by quantities called memory chunks,
  encoding the type, size and signedness of the chunk being addressed.
  The following functions extract the size information from a chunk. -/

def memory_chunk.size : memory_chunk → ℕ
| Mint8signed    := 1
| Mint8unsigned  := 1
| Mint16signed   := 2
| Mint16unsigned := 2
| Mint32         := 4
| Mint64         := 8
| Mfloat32       := 4
| Mfloat64       := 8
| Many32         := 4
| Many64         := 8

lemma memory_chunk.size_pos (chunk) : memory_chunk.size chunk > 0 :=
by cases chunk; exact dec_trivial

lemma memory_chunk.Mptr.size : Mptr.size = if archi.ptr64 then 8 else 4 :=
by delta Mptr; cases archi.ptr64; refl

/- Memory reads and writes must respect alignment constraints:
  the byte offset of the location being addressed should be an exact
  multiple of the natural alignment for the chunk being addressed.
  This natural alignment is defined by the following
  [align_chunk] function.  Some target architectures
  (e.g. PowerPC and x86) have no alignment constraints, which we could
  reflect by taking [align_chunk chunk = 1].  However, other architectures
  have stronger alignment requirements.  The following definition is
  appropriate for PowerPC, ARM and x86. -/

def memory_chunk.align : memory_chunk → ℕ
| Mint8signed    := 1
| Mint8unsigned  := 1
| Mint16signed   := 2
| Mint16unsigned := 2
| Mint32         := 4
| Mint64         := 8
| Mfloat32       := 4
| Mfloat64       := 4
| Many32         := 4
| Many64         := 4

lemma memory_chunk.align_pos (chunk) : memory_chunk.align chunk > 0 :=
by cases chunk; exact dec_trivial

lemma memory_chunk.Mptr.align : Mptr.align = if archi.ptr64 then 8 else 4 :=
by delta Mptr; cases archi.ptr64; refl

lemma align_size_chunk_dvd (chunk : memory_chunk) : chunk.align ∣ chunk.size := sorry

lemma align_le_dvd (chunk1 chunk2 : memory_chunk) (h : chunk1.align ≤ chunk2.align) :
  chunk1.align ∣ chunk2.align := sorry

/- Initialization data for global variables. -/

inductive init_data : Type
| int8    : int32 → init_data
| int16   : int32 → init_data
| int32   : int32 → init_data
| int64   : int64 → init_data
| float32 : float32 → init_data
| float64 : float → init_data
| space   : ℤ → init_data
| addrof  : ident → ptrofs → init_data  /- address of symbol + offset -/

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
export globdef

structure program (F V : Type) : Type :=
(prog_defs : list (ident × globdef F V))
(prog_public : list ident)
(prog_main : ident)

def prog_defs_names {F V : Type} (p : program F V) : list ident :=
p.prog_defs.map prod.fst

/- The "definition map" of a program maps names of globals to their definitions.
  If several definitions have the same name, the one appearing last in [p.(prog_defs)] wins. -/

section defmap

variables {F V : Type}
variable p : program F V

def prog_defmap : PTree.t (globdef F V) :=
PTree.of_list p.prog_defs

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

/- * Generic transformations over programs -/

/- We now define a general iterator over programs that applies a given
  code transformation function to all function descriptions and leaves
  the other parts of the program unchanged. -/

section transf_program

parameters {A B V : Type} (transf : A → B)

def transform_program_globdef : ident × globdef A V → ident × globdef B V
| (id, Gfun f) := (id, Gfun (transf f))
| (id, Gvar v) := (id, Gvar v)

def transform_program : program A V → program B V
| ⟨defs, pub, main⟩ := ⟨defs.map transform_program_globdef, pub, main⟩

end transf_program

/- The following is a more general presentation of [transform_program]:
- Global variable information can be transformed, in addition to function
  definitions.
- The transformation functions can fail and return an error message.
- The transformation for function definitions receives a global context
  (derived from the compilation unit being transformed) as additiona
  argument.
- The transformation functions receive the name of the global as
  additional argument. -/

section transf_program_gen

parameters {A B V W : Type}
parameter transf_fun : ident → A → res B.
parameter transf_var : ident → V → res W.

def transf_globvar (i : ident) : globvar V → res (globvar W)
| ⟨info, init, ro, vo⟩ := do info' ← transf_var i info, OK ⟨info', init, ro, vo⟩

def transf_globdefs : list (ident × globdef A V) → res (list (ident × globdef B W))
| [] := OK []
| ((id, Gfun f) :: l') :=
  match transf_fun id f with
  | error msg := error (MSG "In function " :: CTX id :: MSG ": " :: msg)
  | OK tf :=
      do tl' ← transf_globdefs l', OK ((id, Gfun tf) :: tl')
  end
| ((id, Gvar v) :: l') :=
  match transf_globvar id v with
  | error msg := error (MSG "In variable " :: CTX id :: MSG ": " :: msg)
  | OK tv :=
      do tl' ← transf_globdefs l', OK ((id, Gvar tv) :: tl')
  end

def transform_partial_program2 : program A V → res (program B W)
| ⟨defs, pub, main⟩ := do gl' ← transf_globdefs defs, OK ⟨gl', pub, main⟩

end transf_program_gen

/- The following is a special case of [transform_partial_program2],
  where only function definitions are transformed, but not variable definitions. -/

def transform_partial_program {A B V} (transf_fun : A → res B) : program A V → res (program B V) :=
transform_partial_program2 (λ i, transf_fun) (λ i, OK)

lemma transform_program_partial_program {A B V} (transf_fun: A → B) (p: program A V) :
  transform_partial_program (λ f, OK (transf_fun f)) p = OK (transform_program transf_fun p) := sorry

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
| (EF_vload chunk)             := ⟨[Tptr], some chunk.type, cc_default⟩
| (EF_vstore chunk)            := ⟨[Tptr, chunk.type], none, cc_default⟩
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
| (EF_annot text targs)      := ff
| (EF_debug kind text targs) := ff
| _                          := tt

/- Equality between external functions.  Used in module [Allocation]. -/

instance external_function_eq : decidable_eq external_function := by tactic.mk_dec_eq_instance

/- Function definitions are the union of internal and external functions. -/

inductive fundef (F : Type) : Type
| Internal {} : F → fundef
| External {} : external_function → fundef
open fundef

section transf_fundef

parameters {A B : Type} (transf : A → B)

def transf_fundef : fundef A → fundef B
| (Internal f)  := Internal (transf f)
| (External ef) := External ef

end transf_fundef

section transf_partial_fundef

parameters {A B : Type} (transf_partial : A → res B)

def transf_partial_fundef : fundef A → res (fundef B)
| (Internal f)  := do f' ← transf_partial f, OK (Internal f')
| (External ef) := OK (External ef)

end transf_partial_fundef

/- * Register pairs -/

/- In some intermediate languages (LTL, Mach), 64-bit integers can be
  split into two 32-bit halves and held in a pair of registers.  
  Syntactically, this is captured by the type [rpair] below. -/

inductive rpair (A : Type) : Type
| One (r : A) : rpair
| Twolong (rhi rlo : A) : rpair
open rpair

def typ_rpair {A} (typ_of : A → typ) : rpair A → typ
| (One r) := typ_of r
| (Twolong rhi rlo) := Tlong

def map_rpair {A B} (f: A → B) : rpair A → rpair B
| (One r) := One (f r)
| (Twolong rhi rlo) := Twolong (f rhi) (f rlo)

def regs_of_rpair {A} : rpair A → list A
| (One r) := [r]
| (Twolong rhi rlo) := [rhi, rlo]

def regs_of_rpairs {A} : list (rpair A) → list A
| [] := []
| (p :: l) := regs_of_rpair p ++ regs_of_rpairs l

lemma in_regs_of_rpair {A} (x : A) (p) (hm : x ∈ regs_of_rpair p) (l : list (rpair A)) (hp : p ∈ l) :
  x ∈ regs_of_rpairs l := sorry

lemma in_regs_of_rpairs_inv {A} (x: A) (l : list (rpair A)) (hm : x ∈ regs_of_rpairs l) :
  ∃ p, p ∈ l ∧ x ∈ regs_of_rpair p := sorry

def forall_rpair {A} (P : A → Prop) : rpair A → Prop
| (One r) := P r
| (Twolong rhi rlo) := P rhi ∧ P rlo

/- * Arguments and results to builtin functions -/

inductive builtin_arg (A : Type) : Type
| BA            {} (x : A)                                            : builtin_arg
| BA_int        {} (n : int)                                          : builtin_arg
| BA_long       {} (n : int64)                                        : builtin_arg
| BA_float      {} (f : float)                                        : builtin_arg
| BA_single     {} (f : float32)                                      : builtin_arg
| BA_loadstack  {} (chunk : memory_chunk) (ofs : ptrofs)              : builtin_arg
| BA_addrstack  {} (ofs : ptrofs)                                     : builtin_arg
| BA_loadglobal {} (chunk : memory_chunk) (id : ident) (ofs : ptrofs) : builtin_arg
| BA_addrglobal {} (id : ident) (ofs : ptrofs)                        : builtin_arg
| BA_splitlong  {} (hi lo : builtin_arg)                              : builtin_arg
export builtin_arg

inductive builtin_res (A : Type) : Type
| BR           {} (x : A)               : builtin_res
| BR_none      {}                       : builtin_res
| BR_splitlong {} (hi lo : builtin_res) : builtin_res
open builtin_res

def globals_of_builtin_arg {A : Type} : builtin_arg A → list ident
| (BA_loadglobal chunk id ofs) := [id]
| (BA_addrglobal id ofs)       := [id]
| (BA_splitlong hi lo)         := globals_of_builtin_arg hi ++ globals_of_builtin_arg lo
| _ := []

def globals_of_builtin_args {A} (al : list (builtin_arg A)) : list ident :=
al.foldr (λ a l, globals_of_builtin_arg a ++ l) []

def params_of_builtin_arg {A} : builtin_arg A → list A
| (BA x) := [x]
| (BA_splitlong hi lo) := params_of_builtin_arg hi ++ params_of_builtin_arg lo
| _ := []

def params_of_builtin_args {A} (al : list (builtin_arg A)) : list A :=
al.foldr (λ a l, params_of_builtin_arg a ++ l) []

def params_of_builtin_res {A} : builtin_res A → list A
| (BR x)               := [x]
| BR_none              := []
| (BR_splitlong hi lo) := params_of_builtin_res hi ++ params_of_builtin_res lo

def map_builtin_arg {A B} (f : A → B) : builtin_arg A → builtin_arg B
| (BA x)                       := BA (f x)
| (BA_int n)                   := BA_int n
| (BA_long n)                  := BA_long n
| (BA_float n)                 := BA_float n
| (BA_single n)                := BA_single n
| (BA_loadstack chunk ofs)     := BA_loadstack chunk ofs
| (BA_addrstack ofs)           := BA_addrstack ofs
| (BA_loadglobal chunk id ofs) := BA_loadglobal chunk id ofs
| (BA_addrglobal id ofs)       := BA_addrglobal id ofs
| (BA_splitlong hi lo)         := BA_splitlong (map_builtin_arg hi) (map_builtin_arg lo)

def map_builtin_res {A B} (f : A → B) : builtin_res A → builtin_res B
| (BR x)               := BR (f x)
| BR_none              := BR_none
| (BR_splitlong hi lo) := BR_splitlong (map_builtin_res hi) (map_builtin_res lo)

/- Which kinds of builtin arguments are supported by which external function. -/

inductive builtin_arg_constraint : Type
| OK_default
| OK_const
| OK_addrstack
| OK_addrglobal
| OK_addrany
| OK_all
open builtin_arg_constraint

def builtin_arg_ok {A} : builtin_arg A → builtin_arg_constraint → bool
| (BA _)                       _             := tt
| (BA_splitlong (BA _) (BA _)) _             := tt
| (BA_int _)                   OK_const      := tt
| (BA_long _)                  OK_const      := tt
| (BA_float _)                 OK_const      := tt
| (BA_single _)                OK_const      := tt
| (BA_addrstack _)             OK_addrstack  := tt
| (BA_addrstack _)             OK_addrany    := tt
| (BA_addrglobal _ _)          OK_addrglobal := tt
| (BA_addrglobal _ _)          OK_addrany    := tt
| _                            OK_all        := tt
| _                            _             := ff

end ast