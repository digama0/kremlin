import .ctypes .cop .globalenvs

/- The Clight language: a simplified version of Compcert C where all
  expressions are pure and assignments and function calls are
  statements, not expressions. -/

namespace clight
open ctypes integers ast maps floats values memory word cop globalenvs
     errors ctypes.fundef ctypes.mode

/- * Abstract syntax -/

/- ** Expressions -/

/- Clight expressions correspond to the "pure" subset of C expressions.
  The main omissions are string literals and assignment operators
  ([=], [+=], [++], etc).  In Clight, assignment is a statement,
  not an expression.  Additionally, an expression can also refer to
  temporary variables, which are a separate class of local variables
  that do not reside in memory and whose address cannot be taken.

  As in Compcert C, all expressions are annotated with their types,
  as needed to resolve operator overloading and type-dependent behaviors. -/

inductive expr : Type
| Econst_int : int32 → type → expr       /- integer literal -/
| Econst_float : float → type → expr   /- double float literal -/
| Econst_single : float32 → type → expr /- single float literal -/
| Econst_long : int64 → type → expr    /- long integer literal -/
| Evar : ident → type → expr           /- variable -/
| Etempvar : ident → type → expr       /- temporary variable -/
| Ederef : expr → type → expr          /- pointer dereference (unary [*]) -/
| Eaddrof : expr → type → expr         /- address-of operator ([&]) -/
| Eunop : unary_operation → expr → type → expr  /- unary operation -/
| Ebinop : binary_operation → expr → expr → type → expr /- binary operation -/
| Ecast : expr → type → expr   /- type cast ([(ty) e]) -/
| Efield : expr → ident → type → expr /- access to a member of a struct or union -/
| Esizeof : type → type → expr         /- size of a type -/
| Ealignof : type → type → expr        /- alignment of a type -/
open clight.expr

/- Extract the type part of a type-annotated Clight expression. -/

def typeof : expr → type
| (Econst_int _ ty)    := ty
| (Econst_float _ ty)  := ty
| (Econst_single _ ty) := ty
| (Econst_long _ ty)   := ty
| (Evar _ ty)          := ty
| (Etempvar _ ty)      := ty
| (Ederef _ ty)        := ty
| (Eaddrof _ ty)       := ty
| (Eunop _ _ ty)       := ty
| (Ebinop _ _ _ ty)    := ty
| (Ecast _ ty)         := ty
| (Efield _ _ ty)      := ty
| (Esizeof _ ty)       := ty
| (Ealignof _ ty)      := ty

/- ** Statements -/

/- Clight statements are similar to those of Compcert C, with the addition
  of assigment (of a rvalue to a lvalue), assignment to a temporary,
  and function call (with assignment of the result to a temporary).
  The three C loops are replaced by a single infinite loop [Sloop s1
  s2] that executes [s1] then [s2] repeatedly.  A [continue] in [s1]
  branches to [s2]. -/

def label := ident

inductive statement : Type
| Sskip       : statement                    /- do nothing -/
| Sassign     : expr → expr → statement      /- assignment [lvalue = rvalue] -/
| Sset        : ident → expr → statement     /- assignment [tempvar = rvalue] -/
| Scall       : option ident → expr → list expr → statement
                                             /- function call -/
| Sbuiltin    : option ident → external_function → list type → list expr → statement
                                             /- builtin invocation -/
| Ssequence   : statement → statement → statement
                                             /- sequence -/
| Sifthenelse : expr → statement → statement → statement
                                             /- conditional -/
| Sloop       : statement → statement → statement
                                             /- infinite loop -/
| Sbreak      : statement                    /- [break] statement -/
| Scontinue   : statement                    /- [continue] statement -/
| Sreturn     : option expr → statement      /- [return] statement -/
| Sswitch     : expr → list (option ℤ × statement) → statement
                                             /- [switch] statement -/
                                             /- [None] is [default], [Some x] is [case x] -/
| Slabel      : label → statement → statement
| Sgoto       : label → statement
open statement

/- The C loops are derived forms. -/

def Swhile (e : expr) (s : statement) :=
Sloop (Ssequence (Sifthenelse e Sskip Sbreak) s) Sskip

def Sdowhile (s : statement) (e : expr) :=
Sloop s (Sifthenelse e Sskip Sbreak)

def Sfor (s1 : statement) (e2 : expr) (s3 : statement) (s4 : statement) :=
Ssequence s1 (Sloop (Ssequence (Sifthenelse e2 Sskip Sbreak) s3) s4)

/- ** Functions -/

/- A function definition is composed of its return type ([fn_return]),
  the names and types of its parameters ([fn_params]), the names
  and types of its local variables ([fn_vars]), and the body of the
  function (a statement, [fn_body]). -/

structure function : Type :=
(return : type)
(callconv : calling_convention)
(params : list (ident × type))
(vars : list (ident × type))
(temps : list (ident × type))
(body : statement)


def var_names (vars : list (ident × type)) : list ident :=
list.map prod.fst vars

/- Functions can either be defined ([Internal]) or declared as
  external functions ([External]). -/

def fundef := ctypes.fundef function

/- The type of a function definition. -/

def type_of_function (f : function) : type :=
Tfunction (type_of_params f.params) f.return f.callconv

def type_of_fundef : fundef → type
| (Internal fd) := type_of_function fd
| (External id args res cc) := Tfunction args res cc

/- ** Programs -/

/- As defined in module [Ctypes], a program, or compilation unit, is
  composed of:
- a list of definitions of functions and global variables;
- the names of functions and global variables that are public (not static);
- the name of the function that acts as entry point ("main" function).
- a list of definitions for structure and union names
- the corresponding composite environment
- a proof that this environment is consistent with the definitions. -/

def program := ctypes.program function

/- * Operational semantics -/

/- The semantics uses two environments.  The global environment
  maps names of functions and global variables to memory block references,
  and function pointers to their definitions.  (See module [Globalenvs].)
  It also contains a composite environment, used by type-dependent operations. -/

structure genv :=
(genv : Genv fundef type)
(cenv : composite_env)

instance coe_genv_genv : has_coe genv (Genv fundef type) := ⟨genv.genv⟩
instance coe_genv_cenv : has_coe genv composite_env := ⟨genv.cenv⟩

def globalenv (p : program) : genv :=
{ genv := Genv.globalenv (program_of_program p),
  cenv := p.comp_env }

/- The local environment maps local variables to block references and
  types.  The current value of the variable is stored in the
  associated memory block. -/

def env := PTree (block × type). /- map variable -> location & type -/

def empty_env : env := (∅ : PTree (block × type))

/- The temporary environment maps local temporaries to values. -/

def temp_env := PTree val

/- [deref_loc ty m b ofs v] computes the value of a datum
  of type [ty] residing in memory [m] at block [b], offset [ofs].
  If the type [ty] indicates an access by value, the corresponding
  memory load is performed.  If the type [ty] indicates an access by
  reference or by copy, the pointer [Vptr b ofs] is returned. -/

inductive deref_loc (ty : type) (m : mem) (b : block) (ofs : ptrofs) : val → Prop
| deref_loc_value (chunk v) :
      access_mode ty = By_value chunk →
      loadv chunk m (Vptr b ofs) = some v →
      deref_loc v
| deref_loc_reference :
      access_mode ty = By_reference →
      deref_loc (Vptr b ofs)
| deref_loc_copy :
      access_mode ty = By_copy →
      deref_loc (Vptr b ofs)

/- Symmetrically, [assign_loc ty m b ofs v m'] returns the
  memory state after storing the value [v] in the datum
  of type [ty] residing in memory [m] at block [b], offset [ofs].
  This is allowed only if [ty] indicates an access by value or by copy.
  [m'] is the updated memory state. -/

inductive assign_loc (ce : composite_env) (ty : type) (m : mem) (b : block) (ofs : ptrofs) :
                                            val → mem → Prop
| assign_loc_value (v chunk m') :
      access_mode ty = By_value chunk →
      storev chunk m (Vptr b ofs) v = some m' →
      assign_loc v m'
| assign_loc_copy (b' ofs' bytes m') :
      access_mode ty = By_copy →
      (sizeof ce ty > 0 →
        alignof_blockcopy ce ty ∣ unsigned ofs' ∧ 
        alignof_blockcopy ce ty ∣ unsigned ofs) →
      b' ≠ b ∨ unsigned ofs' = unsigned ofs
              ∨ unsigned ofs' + sizeof ce ty ≤ unsigned ofs
              ∨ unsigned ofs + sizeof ce ty ≤ unsigned ofs' →
      load_bytes m b' (unsigned ofs') (sizeof ce ty) = some bytes →
      store_bytes m b (unsigned ofs) bytes = some m' →
      assign_loc (Vptr b' ofs') m'

section semantics

parameter (ge : genv)

/- Allocation of function-local variables.
  [alloc_variables e1 m1 vars e2 m2] allocates one memory block
  for each variable declared in [vars], and associates the variable
  name with this block.  [e1] and [m1] are the initial local environment
  and memory state.  [e2] and [m2] are the final local environment
  and memory state. -/

inductive alloc_variables : env → mem → list (ident × type) → env → mem → Prop
| nil (e m) : alloc_variables e m [] e m
| cons (e) (m : mem) (id ty vars m2 e2) :
      alloc_variables (PTree.set id (m.nextblock, ty) e)
        (m.alloc 0 (sizeof ge ty)) vars e2 m2 →
      alloc_variables e m ((id, ty) :: vars) e2 m2

/- Initialization of local variables that are parameters to a function.
  [bind_parameters e m1 params args m2] stores the values [args]
  in the memory blocks corresponding to the variables [params].
  [m1] is the initial memory state and [m2] the final memory state. -/

inductive bind_parameters (e : env) : mem → list (ident × type) → list val → mem → Prop
| nil (m) : bind_parameters m [] [] m
| cons (m id ty params v1 vl b m1 m2) :
      PTree.get id e = some (b, ty) →
      assign_loc ge ty m b 0 v1 m1 →
      bind_parameters m1 params vl m2 →
      bind_parameters m ((id, ty) :: params) (v1 :: vl) m2

/- Initialization of temporary variables -/

def create_undef_temps : list (ident × type) → temp_env
| [] := (∅ : PTree val)
| ((id, t) :: temps') := PTree.set id Vundef (create_undef_temps temps')

/- Initialization of temporary variables that are parameters to a function. -/

def bind_parameter_temps : list (ident × type) → list val → temp_env → option temp_env
 | []              []        le := some le
 | ((id, t) :: xl) (v :: vl) le := bind_parameter_temps xl vl (PTree.set id v le)
 | _               _         _  := none

/- Return the list of blocks in the codomain of [e], with low and high bounds. -/

def block_of_binding : ident × block × type → block × ℕ × ℕ
| (id, b, ty) := (b, 0, sizeof ge ty)

def blocks_of_env (e : env) : list (block × ℕ × ℕ) :=
(PTree.elements e).map block_of_binding

/- Optional assignment to a temporary -/

def set_opttemp : option ident → val → temp_env → temp_env
| none      v le := le
| (some id) v le := PTree.set id v le

/- Selection of the appropriate case of a [switch], given the value [n]
  of the selector expression. -/

def labeled_statements := list (option ℤ × statement)

def select_switch_default : labeled_statements → labeled_statements
| [] := []
| ((none, s) :: sl')   := ((none, s) :: sl')
| ((some i, s) :: sl') := select_switch_default sl'

def select_switch_case (n : ℤ) : labeled_statements → option labeled_statements
| []                   := none
| ((none, s) :: sl')   := select_switch_case sl'
| ((some i, s) :: sl') := if i = n then some ((some i, s) :: sl') else select_switch_case sl'

def select_switch (n : ℤ) (sl : labeled_statements) : labeled_statements :=
(select_switch_case n sl).get_or_else (select_switch_default sl)

/- Turn a labeled statement into a sequence -/

def seq_of_labeled_statement : labeled_statements → statement
| [] := Sskip
| ((_, s) :: sl') := Ssequence s (seq_of_labeled_statement sl')

/- ** Evaluation of expressions -/

section expr

parameters (e : env) (le : temp_env) (m : mem)

/- [eval_expr ge e m a v] defines the evaluation of expression [a]
  in r-value position.  [v] is the value of the expression.
  [e] is the current environment and [m] is the current memory state. -/

mutual inductive eval_expr, eval_lvalue
with eval_expr : expr → val → Prop
| eval_Econst_int (i ty)    : eval_expr (Econst_int i ty) (Vint i)
| eval_Econst_float (f ty)  : eval_expr (Econst_float f ty) (Vfloat f)
| eval_Econst_single (f ty) : eval_expr (Econst_single f ty) (Vsingle f)
| eval_Econst_long (i ty)   : eval_expr (Econst_long i ty) (Vlong i)
| eval_Etempvar (id ty v)   :
      (le^!id) = some v →
      eval_expr (Etempvar id ty) v
| eval_Eaddrof (a ty loc ofs) :
      eval_lvalue a loc ofs →
      eval_expr (Eaddrof a ty) (Vptr loc ofs)
| eval_Eunop (op a ty v1 v) :
      eval_expr a v1 →
      sem_unary_operation op m v1 (typeof a) = some v →
      eval_expr (Eunop op a ty) v
| eval_Ebinop (op a1 a2 ty v1 v2 v) :
      eval_expr a1 v1 →
      eval_expr a2 v2 →
      sem_binary_operation ge op m v1 (typeof a1) v2 (typeof a2) = some v →
      eval_expr (Ebinop op a1 a2 ty) v
| eval_Ecast (a ty v1 v) :
      eval_expr a v1 →
      sem_cast m v1 (typeof a) ty = some v →
      eval_expr (Ecast a ty) v
| eval_Esizeof (ty1 ty) :
      eval_expr (Esizeof ty1 ty) (Vptrofs (repr (sizeof ge ty1)))
| eval_Ealignof (ty1 ty) :
      eval_expr (Ealignof ty1 ty) (Vptrofs (repr (alignof ge ty1)))
| eval_Elvalue (a loc ofs v) :
      eval_lvalue a loc ofs →
      deref_loc (typeof a) m loc ofs v →
      eval_expr a v

/- [eval_lvalue ge e m a b ofs] defines the evaluation of expression [a]
  in l-value position.  The result is the memory location [b, ofs]
  that contains the value of the expression [a]. -/

with eval_lvalue : expr → block → ptrofs → Prop
| eval_Evar_local (id l ty) :
      (e^!id) = some (l, ty) →
      eval_lvalue (Evar id ty) l 0
| eval_Evar_global (id l ty) :
      (e^!id) = none →
      Genv.find_symbol ge.genv id = some l →
      eval_lvalue (Evar id ty) l 0
| eval_Ederef (a ty l ofs) :
      eval_expr a (Vptr l ofs) →
      eval_lvalue (Ederef a ty) l ofs
 | eval_Efield_struct (a i ty l ofs id co att delta) :
      eval_expr a (Vptr l ofs) →
      typeof a = Tstruct id att →
      (ge.cenv^!id) = some co →
      field_offset ge i co.co_members = OK delta →
      eval_lvalue (Efield a i ty) l (ofs + repr delta)
 | eval_Efield_union (a i ty l ofs id co att) :
      eval_expr a (Vptr l ofs) →
      typeof a = Tunion id att →
      (ge.cenv^!id) = some co →
      eval_lvalue (Efield a i ty) l ofs

/- [eval_exprlist ge e m al tyl vl] evaluates a list of r-value
  expressions [al], cast their values to the types given in [tyl],
  and produces the list of cast values [vl].  It is used to
  evaluate the arguments of function calls. -/

inductive eval_exprlist : list expr → list type → list val → Prop
| nil : eval_exprlist [] [] []
| cons (a bl ty tyl v1 v2 vl) :
      eval_expr a v1 →
      sem_cast m v1 (typeof a) ty = some v2 →
      eval_exprlist bl tyl vl →
      eval_exprlist (a :: bl) (ty :: tyl) (v2 :: vl)

end expr

/- ** Transition semantics for statements and functions -/

/- Continuations -/

inductive cont : Type
| Kstop : cont
| Kseq : statement → cont → cont       /- [Kseq s2 k] = after [s1] in [s1;s2] -/
| Kloop1 : statement → statement → cont → cont /- [Kloop1 s1 s2 k] = after [s1] in [Sloop s1 s2] -/
| Kloop2 : statement → statement → cont → cont /- [Kloop1 s1 s2 k] = after [s2] in [Sloop s1 s2] -/
| Kswitch : cont → cont       /- catches [break] statements arising out of [switch] -/
| Kcall : option ident →                  /- where to store result -/
          function →                      /- calling function -/
          env →                           /- local env of calling function -/
          temp_env →                      /- temporary env of calling function -/
          cont → cont
open cont

/- Pop continuation until a call or stop -/

def call_cont : cont → cont
| (Kseq s k)       := call_cont k
| (Kloop1 s1 s2 k) := call_cont k
| (Kloop2 s1 s2 k) := call_cont k
| (Kswitch k)      := call_cont k
| k                := k

def is_call_cont : cont → bool
| Kstop             := tt
| (Kcall _ _ _ _ _) := tt
| _                 := ff

/- States -/

inductive state : Type
| State
      (f : function)
      (s : statement)
      (k : cont)
      (e : env)
      (le : temp_env)
      (m : mem)
| Callstate
      (fd : fundef)
      (args : list val)
      (k : cont)
      (m : mem)
| Returnstate
      (res : val)
      (k : cont)
      (m : mem)

/- Find the statement and manufacture the continuation
  corresponding to a label -/

mutual def find_label, find_label_ls (lbl : label)
with find_label : statement → cont → option (statement × cont)
| (Ssequence s1 s2)     := λk, find_label s1 (Kseq s2 k) <|> find_label s2 k
| (Sifthenelse a s1 s2) := λk, find_label s1 k <|> find_label s2 k
| (Sloop s1 s2)         := λk, find_label s1 (Kloop1 s1 s2 k) <|> find_label s2 (Kloop2 s1 s2 k)
| (Sswitch e sl)        := λk, find_label_ls sl (Kswitch k)
| (Slabel lbl' s')      := λk, if lbl = lbl' then some (s', k) else find_label s' k
| _                     := λk, none
with find_label_ls : list (option ℤ × statement) → cont → option (statement × cont)
| []                    := λk, none
| ((_, s) :: sl')       := λk, find_label s (Kseq (seq_of_labeled_statement sl') k) <|> find_label_ls sl' k

#exit
/- Semantics for allocation of variables and binding of parameters at
  function entry.  Two semantics are supported: one where
  parameters are local variables, reside in memory, and can have their address
  taken; the other where parameters are temporary variables and do not reside
  in memory.  We parameterize the [step] transition relation over the
  parameter binding semantics, then instantiate it later to give the two
  semantics described above. -/

parameter function_entry : function → list val → mem → env → temp_env → mem → Prop

/- Transition relation -/

inductive step : state → trace → state → Prop :=

| step_assign :   ∀ f a1 a2 k e le m loc ofs v2 v m',
      eval_lvalue e le m a1 loc ofs →
      eval_expr e le m a2 v2 →
      sem_cast v2 (typeof a2) (typeof a1) m = some v →
      assign_loc ge (typeof a1) m loc ofs v m' →
      step (State f (Sassign a1 a2) k e le m)
        E0 (State f Sskip k e le m')

| step_set :   ∀ f id a k e le m v,
      eval_expr e le m a v →
      step (State f (Sset id a) k e le m)
        E0 (State f Sskip k e (PTree.set id v le) m)

| step_call :   ∀ f optid a al k e le m tyargs tyres cconv vf vargs fd,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv →
      eval_expr e le m a vf →
      eval_exprlist e le m al tyargs vargs →
      Genv.find_funct ge vf = some fd →
      type_of_fundef fd = Tfunction tyargs tyres cconv →
      step (State f (Scall optid a al) k e le m)
        E0 (Callstate fd vargs (Kcall optid f e le k) m)

| step_builtin :   ∀ f optid ef tyargs al k e le m vargs t vres m',
      eval_exprlist e le m al tyargs vargs →
      external_call ef ge vargs m t vres m' →
      step (State f (Sbuiltin optid ef tyargs al) k e le m)
         t (State f Sskip k e (set_opttemp optid vres le) m')

| step_seq :  ∀ f s1 s2 k e le m,
      step (State f (Ssequence s1 s2) k e le m)
        E0 (State f s1 (Kseq s2 k) e le m)
| step_skip_seq : ∀ f s k e le m,
      step (State f Sskip (Kseq s k) e le m)
        E0 (State f s k e le m)
| step_continue_seq : ∀ f s k e le m,
      step (State f Scontinue (Kseq s k) e le m)
        E0 (State f Scontinue k e le m)
| step_break_seq : ∀ f s k e le m,
      step (State f Sbreak (Kseq s k) e le m)
        E0 (State f Sbreak k e le m)

| step_ifthenelse :  ∀ f a s1 s2 k e le m v1 b,
      eval_expr e le m a v1 →
      bool_val v1 (typeof a) m = some b →
      step (State f (Sifthenelse a s1 s2) k e le m)
        E0 (State f (if b then s1 else s2) k e le m)

| step_loop : ∀ f s1 s2 k e le m,
      step (State f (Sloop s1 s2) k e le m)
        E0 (State f s1 (Kloop1 s1 s2 k) e le m)
| step_skip_or_continue_loop1 :  ∀ f s1 s2 k e le m x,
      x = Sskip ∨ x = Scontinue →
      step (State f x (Kloop1 s1 s2 k) e le m)
        E0 (State f s2 (Kloop2 s1 s2 k) e le m)
| step_break_loop1 :  ∀ f s1 s2 k e le m,
      step (State f Sbreak (Kloop1 s1 s2 k) e le m)
        E0 (State f Sskip k e le m)
| step_skip_loop2 : ∀ f s1 s2 k e le m,
      step (State f Sskip (Kloop2 s1 s2 k) e le m)
        E0 (State f (Sloop s1 s2) k e le m)
| step_break_loop2 : ∀ f s1 s2 k e le m,
      step (State f Sbreak (Kloop2 s1 s2 k) e le m)
        E0 (State f Sskip k e le m)

| step_return_0 : ∀ f k e le m m',
      Mem.free_list m (blocks_of_env e) = some m' →
      step (State f (Sreturn none) k e le m)
        E0 (Returnstate Vundef (call_cont k) m')
| step_return_1 : ∀ f a k e le m v v' m',
      eval_expr e le m a v →
      sem_cast v (typeof a) f.(fn_return) m = some v' →
      Mem.free_list m (blocks_of_env e) = some m' →
      step (State f (Sreturn (some a)) k e le m)
        E0 (Returnstate v' (call_cont k) m')
| step_skip_call : ∀ f k e le m m',
      is_call_cont k →
      Mem.free_list m (blocks_of_env e) = some m' →
      step (State f Sskip k e le m)
        E0 (Returnstate Vundef k m')

| step_switch : ∀ f a sl k e le m v n,
      eval_expr e le m a v →
      sem_switch_arg v (typeof a) = some n →
      step (State f (Sswitch a sl) k e le m)
        E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le m)
| step_skip_break_switch : ∀ f x k e le m,
      x = Sskip ∨ x = Sbreak →
      step (State f x (Kswitch k) e le m)
        E0 (State f Sskip k e le m)
| step_continue_switch : ∀ f k e le m,
      step (State f Scontinue (Kswitch k) e le m)
        E0 (State f Scontinue k e le m)

| step_label : ∀ f lbl s k e le m,
      step (State f (Slabel lbl s) k e le m)
        E0 (State f s k e le m)

| step_goto : ∀ f lbl k e le m s' k',
      find_label lbl f.(fn_body) (call_cont k) = some (s', k') →
      step (State f (Sgoto lbl) k e le m)
        E0 (State f s' k' e le m)

| step_internal_function : ∀ f vargs k m e le m1,
      function_entry f vargs m e le m1 →
      step (Callstate (Internal f) vargs k m)
        E0 (State f f.(fn_body) k e le m1)

| step_external_function : ∀ ef targs tres cconv vargs k m vres t m',
      external_call ef ge vargs m t vres m' →
      step (Callstate (External ef targs tres cconv) vargs k m)
         t (Returnstate vres k m')

| step_returnstate : ∀ v optid f e le k m,
      step (Returnstate v (Kcall optid f e le k) m)
        E0 (State f Sskip k e (set_opttemp optid v le) m)

/- ** Whole-program semantics -/

/- Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty continuation. -/

inductive initial_state (p : program) : state → Prop :=
| initial_state_intro : ∀ b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = some m0 →
      Genv.find_symbol ge p.(prog_main) = some b →
      Genv.find_funct_ptr ge b = some f →
      type_of_fundef f = Tfunction Tnil type_int32s cc_default →
      initial_state p (Callstate f nil Kstop m0)

/- A final state is a [Returnstate] with an empty continuation. -/

inductive final_state : state → int32 → Prop :=
| final_state_intro : ∀ r m,
      final_state (Returnstate (Vint r) Kstop m) r

end SEMANTICS

/- The two semantics for function parameters.  First, parameters as local variables. -/

inductive function_entry1 (ge : genv) (f : function) (vargs : list val) (m : mem) (e : env) (le : temp_env) (m' : mem) : Prop :=
| function_entry1_intro : ∀ m1,
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) →
      alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 →
      bind_parameters ge e m1 f.(fn_params) vargs m' →
      le = create_undef_temps f.(fn_temps) →
      function_entry1 ge f vargs m e le m'

def step1 (ge : genv) := step ge (function_entry1 ge)

/- Second, parameters as temporaries. -/

inductive function_entry2 (ge : genv)  (f : function) (vargs : list val) (m : mem) (e : env) (le : temp_env) (m' : mem) : Prop :=
| function_entry2_intro :
      list_norepet (var_names f.(fn_vars)) →
      list_norepet (var_names f.(fn_params)) →
      list_disjoint (var_names f.(fn_params)) (var_names f.(fn_temps)) →
      alloc_variables ge empty_env m f.(fn_vars) e m' →
      bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = some le →
      function_entry2 ge f vargs m e le m'

def step2 (ge : genv) := step ge (function_entry2 ge)

/- Wrapping up these definitions in two small-step semantics. -/

def semantics1 (p : program) :=
  let ge := globalenv p in
  Semantics_gen step1 (initial_state p) final_state ge ge

def semantics2 (p : program) :=
  let ge := globalenv p in
  Semantics_gen step2 (initial_state p) final_state ge ge

/- This semantics is receptive to changes in events. -/

lemma semantics_receptive :
  ∀ (p : program), receptive (semantics1 p)
Proof
  intros. unfold semantics1
  set (ge := globalenv p). constructor; simpl; intros
/- receptiveness -/
  assert (t1 = E0 → ∃ s2, step1 ge s t2 s2)
    intros. subst. inv H0. ∃ s1; auto
  inversion H; subst; auto
  /- builtin -/
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]]
  econstructor; econstructor; eauto
  /- external -/
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]]
  ∃ (Returnstate vres2 k m2). econstructor; eauto
/- trace length -/
  red; simpl; intros. inv H; simpl; try omega
  eapply external_call_trace_length; eauto
  eapply external_call_trace_length; eauto
Qed.