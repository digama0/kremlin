import .events .switch

namespace cminor
open integers ast floats maps values memory events globalenvs switch
     ast.fundef

/- Abstract syntax and semantics for the Cminor language. -/

/- * Abstract syntax -/

/- Cminor is a low-level imperative language structured in expressions,
  statements, functions and programs.  We first define the consts
  and operators that occur within expressions. -/

inductive const : Type
| Ointconst    : int32 → const        /- integer const -/
| Ofloatconst  : float → const        /- double-precision floating-point const -/
| Osingleconst : float32 → const      /- single-precision floating-point const -/
| Olongconst   : int64 → const        /- long integer const -/
| Oaddrsymbol  : ident → ptrofs → const /- address of the symbol plus the offset -/
| Oaddrstack   : ptrofs → const       /- stack pointer plus the given offset -/
open const

inductive unary_operation : Type
| Ocast8unsigned  : unary_operation   /- 8-bit zero extension  -/
| Ocast8signed    : unary_operation   /- 8-bit sign extension  -/
| Ocast16unsigned : unary_operation   /- 16-bit zero extension  -/
| Ocast16signed   : unary_operation   /- 16-bit sign extension -/
| Onegint         : unary_operation   /- integer opposite -/
| Onotint         : unary_operation   /- bitwise complement  -/
| Onegf           : unary_operation   /- float64 opposite -/
| Oabsf           : unary_operation   /- float64 absolute value -/
| Onegfs          : unary_operation   /- float32 opposite -/
| Oabsfs          : unary_operation   /- float32 absolute value -/
| Osingleoffloat  : unary_operation   /- float truncation to float32 -/
| Ofloatofsingle  : unary_operation   /- float extension to float64 -/
| Ointoffloat     : unary_operation   /- signed integer to float64 -/
| Ointuoffloat    : unary_operation   /- unsigned integer to float64 -/
| Ofloatofint     : unary_operation   /- float64 to signed integer -/
| Ofloatofintu    : unary_operation   /- float64 to unsigned integer -/
| Ointofsingle    : unary_operation   /- signed integer to float32 -/
| Ointuofsingle   : unary_operation   /- unsigned integer to float32 -/
| Osingleofint    : unary_operation   /- float32 to signed integer -/
| Osingleofintu   : unary_operation   /- float32 to unsigned integer -/
| Onegl           : unary_operation   /- long integer opposite -/
| Onotl           : unary_operation   /- long bitwise complement -/
| Ointoflong      : unary_operation   /- long to int -/
| Olongofint      : unary_operation   /- signed int to long -/
| Olongofintu     : unary_operation   /- unsigned int to long -/
| Olongoffloat    : unary_operation   /- float64 to signed long -/
| Olonguoffloat   : unary_operation   /- float64 to unsigned long -/
| Ofloatoflong    : unary_operation   /- signed long to float64 -/
| Ofloatoflongu   : unary_operation   /- unsigned long to float64 -/
| Olongofsingle   : unary_operation   /- float32 to signed long -/
| Olonguofsingle  : unary_operation   /- float32 to unsigned long -/
| Osingleoflong   : unary_operation   /- signed long to float32 -/
| Osingleoflongu  : unary_operation   /- unsigned long to float32 -/
export unary_operation

inductive binary_operation : Type
| Oadd   : binary_operation              /- integer addition -/
| Osub   : binary_operation              /- integer subtraction -/
| Omul   : binary_operation              /- integer multiplication -/
| Odiv   : binary_operation              /- integer signed division -/
| Odivu  : binary_operation              /- integer unsigned division -/
| Omod   : binary_operation              /- integer signed modulus -/
| Omodu  : binary_operation              /- integer unsigned modulus -/
| Oand   : binary_operation              /- integer bitwise ``and'' -/
| Oor    : binary_operation              /- integer bitwise ``or'' -/
| Oxor   : binary_operation              /- integer bitwise ``xor'' -/
| Oshl   : binary_operation              /- integer left shift -/
| Oshr   : binary_operation              /- integer right signed shift -/
| Oshru  : binary_operation              /- integer right unsigned shift -/
| Oaddf  : binary_operation              /- float64 addition -/
| Osubf  : binary_operation              /- float64 subtraction -/
| Omulf  : binary_operation              /- float64 multiplication -/
| Odivf  : binary_operation              /- float64 division -/
| Oaddfs : binary_operation              /- float32 addition -/
| Osubfs : binary_operation              /- float32 subtraction -/
| Omulfs : binary_operation              /- float32 multiplication -/
| Odivfs : binary_operation              /- float32 division -/
| Oaddl  : binary_operation              /- long addition -/
| Osubl  : binary_operation              /- long subtraction -/
| Omull  : binary_operation              /- long multiplication -/
| Odivl  : binary_operation              /- long signed division -/
| Odivlu : binary_operation              /- long unsigned division -/
| Omodl  : binary_operation              /- long signed modulus -/
| Omodlu : binary_operation              /- long unsigned modulus -/
| Oandl  : binary_operation              /- long bitwise ``and'' -/
| Oorl   : binary_operation              /- long bitwise ``or'' -/
| Oxorl  : binary_operation              /- long bitwise ``xor'' -/
| Oshll  : binary_operation              /- long left shift -/
| Oshrl  : binary_operation              /- long right signed shift -/
| Oshrlu : binary_operation              /- long right unsigned shift -/
| Ocmp   : comparison → binary_operation /- integer signed comparison -/
| Ocmpu  : comparison → binary_operation /- integer unsigned comparison -/
| Ocmpf  : comparison → binary_operation /- float64 comparison -/
| Ocmpfs : comparison → binary_operation /- float32 comparison -/
| Ocmpl  : comparison → binary_operation /- long signed comparison -/
| Ocmplu : comparison → binary_operation /- long unsigned comparison -/
open binary_operation

/- Expressions include reading local variables, constants,
  arithmetic operations, and memory loads. -/

inductive expr : Type
| Evar   : ident → expr
| Econst : const → expr
| Eunop  : unary_operation → expr → expr
| Ebinop : binary_operation → expr → expr → expr
| Eload  : memory_chunk → expr → expr
open cminor.expr

/- Statements include expression evaluation, assignment to local variables,
  memory stores, function calls, an if/then/else conditional, infinite
  loops, blocks and early block exits, and early function returns.
  [Sexit n] terminates prematurely the execution of the [n+1]
  enclosing [Sblock] statements. -/

def label := ident

inductive stmt : Type
| Sskip       : stmt
| Sassign     : ident → expr → stmt
| Sstore      : memory_chunk → expr → expr → stmt
| Scall       : option ident → signature → expr → list expr → stmt
| Stailcall   : signature → expr → list expr → stmt
| Sbuiltin    : option ident → external_function → list expr → stmt
| Sseq        : stmt → stmt → stmt
| Sifthenelse : expr → stmt → stmt → stmt
| Sloop       : stmt → stmt
| Sblock      : stmt → stmt
| Sexit       : ℕ → stmt
| Sswitch     : bool → expr → list (ℤ × ℕ) → ℕ → stmt
| Sreturn     : option expr → stmt
| Slabel      : label → stmt → stmt
| Sgoto       : label → stmt
open stmt

/- Functions are composed of a signature, a list of parameter names,
  a list of local variables, and a  statement representing
  the function body.  Each function can allocate a memory block of
  size [fn_stackspace] on entrance.  This block will be deallocated
  automatically before the function returns.  Pointers into this block
  can be taken with the [Oaddrstack] operator. -/

structure function : Type :=
(sig : signature)
(params : list ident)
(vars : list ident)
(stackspace : ℕ)
(body : stmt)

def fundef := ast.fundef function.
def program := ast.program fundef unit.

def funsig : fundef → signature
| (fundef.Internal f) := f.sig
| (fundef.External ef) := ef_sig ef

/- * Operational semantics (small-step) -/

/- Two kinds of evaluation environments are involved:
- [genv]: global environments, define symbols and functions;
- [env]: local environments, map local variables to values.
-/

def genv := globalenvs.genv fundef unit
def env := PTree val
instance : has_coe genv senv := ⟨genv.to_senv⟩

/- The following functions build the initial local environment at
  function entry, binding parameters to the provided arguments and
  initializing local variables to [Vundef]. -/

def set_params : list ident → list val → env
| []         _  := (∅ : PTree _)
| (i1 :: is) vs := (set_params is vs.tail).set i1 vs.head

def set_locals (e : env) : list ident → env
| [] := e
| (i1 :: is) := (set_locals is).set i1 Vundef

def set_optvar (e : env) : option ident → val → env
| none      v := e
| (some id) v := e.set id v

/- Continuations -/

inductive cont : Type
| Kstop : cont                         /- stop program execution -/
| Kseq : stmt → cont → cont            /- execute stmt, then cont -/
| Kblock : cont → cont                 /- exit a block, then do cont -/
| Kcall : option ident → function → val → env → cont → cont
                                       /- return to caller -/
open cont

/- States -/

inductive state : Type
| State                       /- Execution within a function -/
  (f : function)              /- currently executing function  -/
  (s : stmt)                  /- statement under consideration -/
  (k : cont)                  /- its continuation -- what to do next -/
  (sp : val)                  /- current stack pointer -/
  (e : env)                   /- current local environment -/
  (m : mem)                   /- current memory state -/
  : state
| Callstate                   /- Invocation of a function -/
  (f : fundef)                /- function to invoke -/
  (args : list val)           /- arguments provided by caller -/
  (k : cont)                  /- what to do next  -/
  (m : mem)                   /- memory state -/
  : state
| Returnstate                 /- Return from a function -/
  (v : val)                   /- Return value -/
  (k : cont)                  /- what to do next -/
  (m : mem)                   /- memory state -/
  : state
open cminor.state

section relsem

parameter (ge : genv)

/- Evaluation of constants and operator applications.
    [None] is returned when the computation is undefined, e.g.
    if arguments are of the wrong types, or in case of an integer division
    by zero. -/

def eval_const (sp : val) : const → val
| (Ointconst n)       := Vint n
| (Ofloatconst n)     := Vfloat n
| (Osingleconst n)    := Vsingle n
| (Olongconst n)      := Vlong n
| (Oaddrsymbol s ofs) := ge.symbol_address s ofs
| (Oaddrstack ofs)    := offset_ptr sp ofs

def eval_unop (arg : val) : unary_operation → option val
| Ocast8unsigned  := some (zero_ext 8 arg)
| Ocast8signed    := some (sign_ext 8 arg)
| Ocast16unsigned := some (zero_ext 16 arg)
| Ocast16signed   := some (sign_ext 16 arg)
| Onegint         := some (negint arg)
| Onotint         := some (notint arg)
| Onegf           := some (negf arg)
| Oabsf           := some (absf arg)
| Onegfs          := some (negfs arg)
| Oabsfs          := some (absfs arg)
| Osingleoffloat  := some (single_of_float arg)
| Ofloatofsingle  := some (float_of_single arg)
| Ointoffloat     := int_of_float arg
| Ointuoffloat    := intu_of_float arg
| Ofloatofint     := float_of_int arg
| Ofloatofintu    := float_of_intu arg
| Ointofsingle    := int_of_single arg
| Ointuofsingle   := intu_of_single arg
| Osingleofint    := single_of_int arg
| Osingleofintu   := single_of_intu arg
| Onegl           := some (negl arg)
| Onotl           := some (notl arg)
| Ointoflong      := some (loword arg)
| Olongofint      := some (long_of_int arg)
| Olongofintu     := some (long_of_intu arg)
| Olongoffloat    := long_of_float arg
| Olonguoffloat   := longu_of_float arg
| Ofloatoflong    := float_of_long arg
| Ofloatoflongu   := float_of_longu arg
| Olongofsingle   := long_of_single arg
| Olonguofsingle  := longu_of_single arg
| Osingleoflong   := single_of_long arg
| Osingleoflongu  := single_of_longu arg

def eval_binop (arg1 arg2 : val) (m : mem) : binary_operation → option val
| Oadd       := some (arg1 + arg2)
| Osub       := some (arg1 - arg2)
| Omul       := some (arg1 * arg2)
| Odiv       := divs arg1 arg2
| Odivu      := divu arg1 arg2
| Omod       := mods arg1 arg2
| Omodu      := modu arg1 arg2
| Oand       := some (val.and arg1 arg2)
| Oor        := some (val.or arg1 arg2)
| Oxor       := some (val.xor arg1 arg2)
| Oshl       := some (shl arg1 arg2)
| Oshr       := some (shr arg1 arg2)
| Oshru      := some (shru arg1 arg2)
| Oaddf      := some (addf arg1 arg2)
| Osubf      := some (subf arg1 arg2)
| Omulf      := some (mulf arg1 arg2)
| Odivf      := some (divf arg1 arg2)
| Oaddfs     := some (addfs arg1 arg2)
| Osubfs     := some (subfs arg1 arg2)
| Omulfs     := some (mulfs arg1 arg2)
| Odivfs     := some (divfs arg1 arg2)
| Oaddl      := some (addl arg1 arg2)
| Osubl      := some (subl arg1 arg2)
| Omull      := some (mull arg1 arg2)
| Odivl      := divls arg1 arg2
| Odivlu     := divlu arg1 arg2
| Omodl      := modls arg1 arg2
| Omodlu     := modlu arg1 arg2
| Oandl      := some (andl arg1 arg2)
| Oorl       := some (orl arg1 arg2)
| Oxorl      := some (xorl arg1 arg2)
| Oshll      := some (shll arg1 arg2)
| Oshrl      := some (shrl arg1 arg2)
| Oshrlu     := some (shrlu arg1 arg2)
| (Ocmp c)   := some (cmp c arg1 arg2)
| (Ocmpu c)  := some (cmpu (valid_pointer m) c arg1 arg2)
| (Ocmpf c)  := some (cmpf c arg1 arg2)
| (Ocmpfs c) := some (cmpfs c arg1 arg2)
| (Ocmpl c)  := cmpl c arg1 arg2
| (Ocmplu c) := cmplu (valid_pointer m) c arg1 arg2

/- Evaluation of an expression: [eval_expr ge sp e m a = some v]
  states that expression [a] evaluates to value [v].
  [ge] is the global environment, [e] the local environment,
  and [m] the current memory state.  They are unchanged during evaluation.
  [sp] is the pointer to the memory block allocated for this function
  (stack frame).
-/

section eval_expr

parameters (sp : val) (e : env) (m : mem)

def eval_expr : expr → option val
| (Evar id)          := PTree.get id e
| (Econst cst)       := eval_const sp cst
| (Eunop op a1)      := do v1 ← eval_expr a1, eval_unop v1 op
| (Ebinop op a1 a2)  := do v1 ← eval_expr a1, v2 ← eval_expr a2, eval_binop v1 v2 m op
| (Eload chunk addr) := do vaddr ← eval_expr addr, loadv chunk m vaddr

end eval_expr

/- Pop continuation until a call or stop -/

def call_cont : cont → cont
| (Kseq s k) := call_cont k
| (Kblock k) := call_cont k
| k := k

def is_call_cont : cont → bool
| Kstop             := tt
| (Kcall _ _ _ _ _) := tt
| _ := ff

/- Find the statement and manufacture the continuation
  corresponding to a label -/

def find_label (lbl : label) : stmt → cont → option (stmt × cont)
| (Sseq s1 s2)          k := find_label s1 (Kseq s2 k) <|> find_label s2 k
| (Sifthenelse a s1 s2) k := find_label s1 k <|> find_label s2 k
| (Sloop s1)            k := find_label s1 (Kseq (Sloop s1) k)
| (Sblock s1)           k := find_label s1 (Kblock k)
| (Slabel lbl' s')      k := if lbl = lbl' then some (s', k) else find_label s' k
| _                     k := none

/- One step of execution -/

inductive step : state → list event → state → Prop
| step_skip_seq (f s k sp e m) :
  step (State f Sskip (Kseq s k) sp e m)
    [] (State f s k sp e m)
| step_skip_block (f k sp e m) :
  step (State f Sskip (Kblock k) sp e m)
    [] (State f Sskip k sp e m)
| step_skip_call (f : function) (k sp e m m') :
  is_call_cont k →
  free m sp 0 f.stackspace = some m' →
  step (State f Sskip k (Vptr sp 0) e m)
    [] (Returnstate Vundef k m')

| step_assign (f id a k sp e m v) :
  eval_expr sp e m a = some v →
  step (State f (Sassign id a) k sp e m)
    [] (State f Sskip k sp (PTree.set id v e) m)

| step_store (f chunk addr a k sp e m vaddr v m') :
  eval_expr sp e m addr = some vaddr →
  eval_expr sp e m a = some v →
  storev chunk m vaddr v = some m' →
  step (State f (Sstore chunk addr a) k sp e m)
    [] (State f Sskip k sp e m')

| step_call (f optid a bl k sp e m vf vargs fd) :
  eval_expr sp e m a = some vf →
  mmap (eval_expr sp e m) bl = some vargs →
  ge.find_funct vf = some fd →
  step (State f (Scall optid (funsig fd) a bl) k sp e m)
    [] (Callstate fd vargs (Kcall optid f sp e k) m)

| step_tailcall (f : function) (a bl k sp e m vf vargs fd m') :
  eval_expr (Vptr sp 0) e m a = some vf →
  mmap (eval_expr (Vptr sp 0) e m) bl = some vargs →
  ge.find_funct vf = some fd →
  free m sp 0 f.stackspace = some m' →
  step (State f (Stailcall (funsig fd) a bl) k (Vptr sp 0) e m)
    [] (Callstate fd vargs (call_cont k) m')

| step_builtin (f optid ef bl k sp e m vargs t vres m') :
  mmap (eval_expr sp e m) bl = some vargs →
  external_call ef ge vargs m t vres m' →
  step (State f (Sbuiltin optid ef bl) k sp e m)
     t (State f Sskip k sp (set_optvar e optid vres) m')

| step_seq (f s1 s2 k sp e m) :
  step (State f (Sseq s1 s2) k sp e m)
    [] (State f s1 (Kseq s2 k) sp e m)

| step_ifthenelse (f a s1 s2 k sp e m b) :
  eval_expr sp e m a >>= to_bool = some b →
  step (State f (Sifthenelse a s1 s2) k sp e m)
    [] (State f (if b then s1 else s2) k sp e m)

| step_loop (f s k sp e m) :
  step (State f (Sloop s) k sp e m)
    [] (State f s (Kseq (Sloop s) k) sp e m)

| step_block (f s k sp e m) :
  step (State f (Sblock s) k sp e m)
    [] (State f s (Kblock k) sp e m)

| step_exit_seq (f n s k sp e m) :
  step (State f (Sexit n) (Kseq s k) sp e m)
    [] (State f (Sexit n) k sp e m)
| step_exit_block_0 (f k sp e m) :
  step (State f (Sexit 0) (Kblock k) sp e m)
    [] (State f Sskip k sp e m)
| step_exit_block_S (f n k sp e m) :
  step (State f (Sexit (n + 1)) (Kblock k) sp e m)
    [] (State f (Sexit n) k sp e m)

| step_switch (f islong a cases default k sp e m v w n) :
  eval_expr sp e m a = some v →
  switch_argument islong v w n →
  step (State f (Sswitch islong a cases default) k sp e m)
    [] (State f (Sexit (switch_target' w n default cases)) k sp e m)

| step_return_0 (f : function) (k sp e m m') :
  free m sp 0 f.stackspace = some m' →
  step (State f (Sreturn none) k (Vptr sp 0) e m)
    [] (Returnstate Vundef (call_cont k) m')
| step_return_1 (f : function) (a k sp e m v m') :
  eval_expr (Vptr sp 0) e m a = some v →
  free m sp 0 f.stackspace = some m' →
  step (State f (Sreturn (some a)) k (Vptr sp 0) e m)
    [] (Returnstate v (call_cont k) m')

| step_label (f lbl s k sp e m) :
  step (State f (Slabel lbl s) k sp e m)
    [] (State f s k sp e m)

| step_goto (f : function) (lbl k sp e m s' k') :
  find_label lbl f.body (call_cont k) = some (s', k') →
  step (State f (Sgoto lbl) k sp e m)
    [] (State f s' k' sp e m)

| step_internal_function (f : function) (vargs k) (m : mem) :
  step (Callstate (Internal f) vargs k m)
    [] (State f f.body k (Vptr m.nextblock 0)
         (set_locals (set_params f.params vargs) f.vars)
         (m.alloc 0 f.stackspace))
| step_external_function (ef vargs k m t vres m') :
  external_call ef ge vargs m t vres m' →
  step (Callstate (External ef) vargs k m)
     t (Returnstate vres k m')

| step_return (v optid f sp e k m) :
  step (Returnstate v (Kcall optid f sp e k) m)
    [] (State f Sskip k sp (set_optvar e optid v) m)

end relsem

/- Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty continuation. -/

inductive initial_state (p : program) : state → Prop
| mk (b f m0) :
  genv.init_mem p = some m0 →
  genv.find_symbol (genv.globalenv p) p.main = some b →
  genv.find_funct_ptr (genv.globalenv p) b = some f →
  funsig f = signature_main →
  initial_state (Callstate f [] Kstop m0)

/- A final state is a [Returnstate] with an empty continuation. -/

inductive final_state : state → int32 → Prop
| mk (r m) : final_state (Returnstate (Vint r) Kstop m) r

/- * Alternate operational semantics (big-step) -/

/- We now define another semantics for Cminor without [goto] that follows
  the ``big-step'' style of semantics, also known as natural semantics.
  In this style, just like expressions evaluate to values,
  statements evaluate to``outcomes'' indicating how execution should
  proceed afterwards. -/

inductive outcome : Type
| normal          : outcome              /- continue in sequence -/
| exit            : ℕ → outcome          /- terminate [n+1] enclosing blocks -/
| return          : option val → outcome /- return immediately to caller -/
| tailcall_return : val → outcome        /- already returned to caller via a tailcall -/

def outcome_block : outcome → outcome
| (outcome.exit 0) := outcome.normal
| (outcome.exit (n+1)) := outcome.exit n
| out := out

def outcome_result_value (retsig : option typ) (vres : val) : outcome → Prop
| outcome.normal              := vres = Vundef
| (outcome.return none)       := vres = Vundef
| (outcome.return (some v))   := retsig ≠ none ∧ vres = v
| (outcome.tailcall_return v) := vres = v
| _                           := false

def outcome_free_mem (m : mem) (sp : block) (sz : ℕ) (m' : mem) : outcome → Prop
| (outcome.tailcall_return _) := m' = m
| _                           := free m sp 0 sz = some m'

section naturalsem

parameter (ge : genv)

/- Evaluation of a function invocation: [eval_funcall ge m f args t m' res]
  means that the function [f], applied to the arguments [args] in
  memory state [m], returns the value [res] in modified memory state [m'].
  [t] is the trace of observable events generated during the invocation.
-/

mutual inductive eval_funcall, exec_stmt
with eval_funcall :
        mem → fundef → list val → list event →
        mem → val → Prop
| eval_funcall_internal (m : mem) (f : function) (vargs m1 sp e t e2 m2 out vres m3) :
      m.alloc 0 f.stackspace = m1 → m.nextblock = sp →
      set_locals (set_params f.params vargs) f.vars = e →
      exec_stmt f (Vptr sp 0) e m1 f.body t e2 m2 out →
      outcome_result_value f.sig.sig_res vres out →
      outcome_free_mem m2 sp f.stackspace m3 out →
      eval_funcall m (Internal f) vargs t m3 vres
| eval_funcall_external :
      ∀ ef m args t res m',
      external_call ef ge args m t res m' →
      eval_funcall m (External ef) args t m' res

/- Execution of a statement: [exec_stmt ge f sp e m s t e' m' out]
  means that statement [s] executes with outcome [out].
  [e] is the initial environment and [m] is the initial memory state.
  [e'] is the final environment, reflecting variable assignments performed
  by [s].  [m'] is the final memory state, reflecting memory stores
  performed by [s].  [t] is the trace of I/O events performed during
  the execution.  The other parameters are as in [eval_expr]. -/

with exec_stmt :
         function → val →
         env → mem → stmt → list event →
         env → mem → outcome → Prop
| exec_Sskip (f sp e m) : exec_stmt f sp e m Sskip [] e m outcome.normal
| exec_Sassign (f sp e m id a v) :
      eval_expr ge sp e m a = some v →
      exec_stmt f sp e m (Sassign id a) [] (PTree.set id v e) m outcome.normal
| exec_Sstore (f sp e m chunk addr a vaddr v m') :
      eval_expr ge sp e m addr = some vaddr →
      eval_expr ge sp e m a = some v →
      storev chunk m vaddr v = some m' →
      exec_stmt f sp e m (Sstore chunk addr a) [] e m' outcome.normal
| exec_Scall (f sp e m optid sig a bl vf vargs fd t m' vres e') :
      eval_expr ge sp e m a = some vf →
      mmap (eval_expr ge sp e m) bl = some vargs →
      genv.find_funct ge vf = some fd →
      funsig fd = sig →
      eval_funcall m fd vargs t m' vres →
      e' = set_optvar e optid vres →
      exec_stmt f sp e m (Scall optid sig a bl) t e' m' outcome.normal
| exec_Sbuiltin (f sp e m optid ef bl t m' vargs vres e') :
      mmap (eval_expr ge sp e m) bl = some vargs →
      external_call ef ge vargs m t vres m' →
      e' = set_optvar e optid vres →
      exec_stmt f sp e m (Sbuiltin optid ef bl) t e' m' outcome.normal
| exec_Sifthenelse (f sp e m a s1 s2 v b t e' m' out) :
      eval_expr ge sp e m a = some v →
      v.to_bool = some b →
      exec_stmt f sp e m (if b then s1 else s2) t e' m' out →
      exec_stmt f sp e m (Sifthenelse a s1 s2) t e' m' out
| exec_Sseq_continue (f sp e m s1 t1 e1 m1 s2 t2 e2 m2 out) :
      exec_stmt f sp e m s1 t1 e1 m1 outcome.normal →
      exec_stmt f sp e1 m1 s2 t2 e2 m2 out →
      exec_stmt f sp e m (Sseq s1 s2) (t1 ++ t2) e2 m2 out
| exec_Sseq_stop (f sp e m t s1 s2 e1 m1 out) :
      exec_stmt f sp e m s1 t e1 m1 out →
      out ≠ outcome.normal →
      exec_stmt f sp e m (Sseq s1 s2) t e1 m1 out
| exec_Sloop_loop (f sp e m s t1 e1 m1 t2 e2 m2 out) :
      exec_stmt f sp e m s t1 e1 m1 outcome.normal →
      exec_stmt f sp e1 m1 (Sloop s) t2 e2 m2 out →
      exec_stmt f sp e m (Sloop s) (t1 ++ t2) e2 m2 out
| exec_Sloop_stop (f sp e m t s e1 m1 out) :
      exec_stmt f sp e m s t e1 m1 out →
      out ≠ outcome.normal →
      exec_stmt f sp e m (Sloop s) t e1 m1 out
| exec_Sblock (f sp e m s t e1 m1 out) :
      exec_stmt f sp e m s t e1 m1 out →
      exec_stmt f sp e m (Sblock s) t e1 m1 (outcome_block out)
| exec_Sexit (f sp e m n) :
      exec_stmt f sp e m (Sexit n) [] e m (outcome.exit n)
| exec_Sswitch (f sp e m islong a cases default v w n) :
      eval_expr ge sp e m a = some v →
      switch_argument islong v w n →
      exec_stmt f sp e m (Sswitch islong a cases default)
                [] e m (outcome.exit (switch_target' w n default cases))
| exec_Sreturn_none (f sp e m) :
      exec_stmt f sp e m (Sreturn none) [] e m (outcome.return none)
| exec_Sreturn_some (f sp e m a v) :
      eval_expr ge sp e m a = some v →
      exec_stmt f sp e m (Sreturn (some a)) [] e m (outcome.return (some v))
| exec_Stailcall (f : function) (sp e m sig a bl vf vargs fd t m' m'' vres) :
      eval_expr ge (Vptr sp 0) e m a = some vf →
      mmap (eval_expr ge (Vptr sp 0) e m) bl = some vargs →
      genv.find_funct ge vf = some fd →
      funsig fd = sig →
      free m sp 0 f.stackspace = some m' →
      eval_funcall m' fd vargs t m'' vres →
      exec_stmt f (Vptr sp 0) e m (Stailcall sig a bl) t e m'' (outcome.tailcall_return vres)

end naturalsem

/- Big-step execution of a whole program -/

inductive bigstep_program_terminates (p : program) : list event → int32 → Prop
| mk (b f m0 t m r) :
      genv.init_mem p = some m0 →
      genv.find_symbol (genv.globalenv p) p.main = some b →
      genv.find_funct_ptr (genv.globalenv p) b = some f →
      funsig f = signature_main →
      eval_funcall (genv.globalenv p) m0 f [] t m (Vint r) →
      bigstep_program_terminates t r


end cminor