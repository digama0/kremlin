import .integers .lib .ast .globalenvs

namespace cminor
open integers ast floats maps values

/- Abstract syntax and semantics for the Cminor language. -/

/- * Abstract syntax -/

/- Cminor is a low-level imperative language structured in expressions,
  statements, functions and programs.  We first define the consts
  and operators that occur within expressions. -/

inductive const : Type
| Ointconst    : int → const          /- integer const -/
| Ofloatconst  : float → const        /- double-precision floating-point const -/
| Osingleconst : float32 → const      /- single-precision floating-point const -/
| Olongconst   : int64 → const        /- long integer const -/
| Oaddrsymbol  : ident → ptrofs → const /- address of the symbol plus the offset -/
| Oaddrstack   : ptrofs → const       /- stack pointer plus the given offset -/

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

/- Expressions include reading local variables, constants,
  arithmetic operations, and memory loads. -/

inductive expr : Type
| Evar : ident → expr
| Econst : const → expr
| Eunop : unary_operation → expr → expr
| Ebinop : binary_operation → expr → expr → expr
| Eload : memory_chunk → expr → expr

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
(stackspace : ℤ)
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

/- The following functions build the initial local environment at
  function entry, binding parameters to the provided arguments and
  initializing local variables to [Vundef]. -/

def set_params : list val → list ident → env
| _  []         := (∅ : PTree _)
| vs (i1 :: is) := PTree.set i1 vs.head (set_params vs.tail is)

def set_locals (il : list ident) (e : env) {struct il} : env :=
  match il with
| nil := e
| i1 :: is := PTree.set i1 Vundef (set_locals is e)
  end

def set_optvar (optid : option ident) (v : val) (e : env) : env :=
  match optid with
| none := e
| some id := PTree.set id v e
  end

/- Continuations -/

inductive cont : Type :=
| Kstop : cont                         /- stop program execution -/
| Kseq : stmt → cont → cont          /- execute stmt, then cont -/
| Kblock : cont → cont                /- exit a block, then do cont -/
| Kcall : option ident → function → val → env → cont → cont
                                        /- return to caller -/

/- States -/

inductive state : Type :=
| State :                      /- Execution within a function -/
      ∀ (f : function)              /- currently executing function  -/
             (s : stmt)                  /- statement under consideration -/
             (k : cont)                  /- its continuation -- what to do next -/
             (sp : val)                  /- current stack pointer -/
             (e : env)                   /- current local environment -/
             (m : mem),                  /- current memory state -/
      state
| Callstate :                  /- Invocation of a function -/
      ∀ (f : fundef)                /- function to invoke -/
             (args : list val)           /- arguments provided by caller -/
             (k : cont)                  /- what to do next  -/
             (m : mem),                  /- memory state -/
      state
| Returnstate :                /- Return from a function -/
      ∀ (v : val)                   /- Return value -/
             (k : cont)                  /- what to do next -/
             (m : mem),                  /- memory state -/
      state

section RELSEM

parameter ge : genv

/- Evaluation of constants and operator applications.
    [None] is returned when the computation is undefined, e.g.
    if arguments are of the wrong types, or in case of an integer division
    by zero. -/

def eval_constant (sp : val) (cst : constant) : option val :=
  match cst with
| Ointconst n := some (Vint n)
| Ofloatconst n := some (Vfloat n)
| Osingleconst n := some (Vsingle n)
| Olongconst n := some (Vlong n)
| Oaddrsymbol s ofs := some (Genv.symbol_address ge s ofs)
| Oaddrstack ofs := some (Val.offset_ptr sp ofs)
  end

def eval_unop (op : unary_operation) (arg : val) : option val :=
  match op with
| Ocast8unsigned := some (Val.zero_ext 8 arg)
| Ocast8signed := some (Val.sign_ext 8 arg)
| Ocast16unsigned := some (Val.zero_ext 16 arg)
| Ocast16signed := some (Val.sign_ext 16 arg)
| Onegint := some (Val.negint arg)
| Onotint := some (Val.notint arg)
| Onegf := some (Val.negf arg)
| Oabsf := some (Val.absf arg)
| Onegfs := some (Val.negfs arg)
| Oabsfs := some (Val.absfs arg)
| Osingleoffloat := some (Val.singleoffloat arg)
| Ofloatofsingle := some (Val.floatofsingle arg)
| Ointoffloat := Val.intoffloat arg
| Ointuoffloat := Val.intuoffloat arg
| Ofloatofint := Val.floatofint arg
| Ofloatofintu := Val.floatofintu arg
| Ointofsingle := Val.intofsingle arg
| Ointuofsingle := Val.intuofsingle arg
| Osingleofint := Val.singleofint arg
| Osingleofintu := Val.singleofintu arg
| Onegl := some (Val.negl arg)
| Onotl := some (Val.notl arg)
| Ointoflong := some (Val.loword arg)
| Olongofint := some (Val.longofint arg)
| Olongofintu := some (Val.longofintu arg)
| Olongoffloat := Val.longoffloat arg
| Olonguoffloat := Val.longuoffloat arg
| Ofloatoflong := Val.floatoflong arg
| Ofloatoflongu := Val.floatoflongu arg
| Olongofsingle := Val.longofsingle arg
| Olonguofsingle := Val.longuofsingle arg
| Osingleoflong := Val.singleoflong arg
| Osingleoflongu := Val.singleoflongu arg
  end

def eval_binop
            (op : binary_operation) (arg1 arg2 : val) (m : mem) : option val :=
  match op with
| Oadd := some (Val.add arg1 arg2)
| Osub := some (Val.sub arg1 arg2)
| Omul := some (Val.mul arg1 arg2)
| Odiv := Val.divs arg1 arg2
| Odivu := Val.divu arg1 arg2
| Omod := Val.mods arg1 arg2
| Omodu := Val.modu arg1 arg2
| Oand := some (Val.and arg1 arg2)
| Oor := some (Val.or arg1 arg2)
| Oxor := some (Val.xor arg1 arg2)
| Oshl := some (Val.shl arg1 arg2)
| Oshr := some (Val.shr arg1 arg2)
| Oshru := some (Val.shru arg1 arg2)
| Oaddf := some (Val.addf arg1 arg2)
| Osubf := some (Val.subf arg1 arg2)
| Omulf := some (Val.mulf arg1 arg2)
| Odivf := some (Val.divf arg1 arg2)
| Oaddfs := some (Val.addfs arg1 arg2)
| Osubfs := some (Val.subfs arg1 arg2)
| Omulfs := some (Val.mulfs arg1 arg2)
| Odivfs := some (Val.divfs arg1 arg2)
| Oaddl := some (Val.addl arg1 arg2)
| Osubl := some (Val.subl arg1 arg2)
| Omull := some (Val.mull arg1 arg2)
| Odivl := Val.divls arg1 arg2
| Odivlu := Val.divlu arg1 arg2
| Omodl := Val.modls arg1 arg2
| Omodlu := Val.modlu arg1 arg2
| Oandl := some (Val.andl arg1 arg2)
| Oorl := some (Val.orl arg1 arg2)
| Oxorl := some (Val.xorl arg1 arg2)
| Oshll := some (Val.shll arg1 arg2)
| Oshrl := some (Val.shrl arg1 arg2)
| Oshrlu := some (Val.shrlu arg1 arg2)
| Ocmp c := some (Val.cmp c arg1 arg2)
| Ocmpu c := some (Val.cmpu (Mem.valid_pointer m) c arg1 arg2)
| Ocmpf c := some (Val.cmpf c arg1 arg2)
| Ocmpfs c := some (Val.cmpfs c arg1 arg2)
| Ocmpl c := Val.cmpl c arg1 arg2
| Ocmplu c := Val.cmplu (Mem.valid_pointer m) c arg1 arg2
  end

/- Evaluation of an expression: [eval_expr ge sp e m a v]
  states that expression [a] evaluates to value [v].
  [ge] is the global environment, [e] the local environment,
  and [m] the current memory state.  They are unchanged during evaluation.
  [sp] is the pointer to the memory block allocated for this function
  (stack frame).
-/

section EVAL_EXPR

parameter sp : val
parameter e : env
parameter m : mem

inductive eval_expr : expr → val → Prop :=
| eval_Evar : ∀ id v,
      PTree.get id e = some v →
      eval_expr (Evar id) v
| eval_Econst : ∀ cst v,
      eval_constant sp cst = some v →
      eval_expr (Econst cst) v
| eval_Eunop : ∀ op a1 v1 v,
      eval_expr a1 v1 →
      eval_unop op v1 = some v →
      eval_expr (Eunop op a1) v
| eval_Ebinop : ∀ op a1 a2 v1 v2 v,
      eval_expr a1 v1 →
      eval_expr a2 v2 →
      eval_binop op v1 v2 m = some v →
      eval_expr (Ebinop op a1 a2) v
| eval_Eload : ∀ chunk addr vaddr v,
      eval_expr addr vaddr →
      Mem.loadv chunk m vaddr = some v →
      eval_expr (Eload chunk addr) v

inductive eval_exprlist : list expr → list val → Prop :=
| eval_Enil :
      eval_exprlist nil nil
| eval_Econs : ∀ a1 al v1 vl,
      eval_expr a1 v1 → eval_exprlist al vl →
      eval_exprlist (a1 :: al) (v1 :: vl)

end EVAL_EXPR

/- Pop continuation until a call or stop -/

def call_cont (k : cont) : cont :=
  match k with
| Kseq s k := call_cont k
| Kblock k := call_cont k
| _ := k
  end

def is_call_cont (k : cont) : Prop :=
  match k with
| Kstop := true
| Kcall _ _ _ _ _ := true
| _ := false
  end

/- Find the statement and manufacture the continuation
  corresponding to a label -/

def find_label (lbl : label) (s : stmt) (k : cont)
                    {struct s} : option (stmt * cont) :=
  match s with
| Sseq s1 s2 :=
      match find_label lbl s1 (Kseq s2 k) with
      | some sk := some sk
      | none := find_label lbl s2 k
      end
| Sifthenelse a s1 s2 :=
      match find_label lbl s1 k with
      | some sk := some sk
      | none := find_label lbl s2 k
      end
| Sloop s1 :=
      find_label lbl s1 (Kseq (Sloop s1) k)
| Sblock s1 :=
      find_label lbl s1 (Kblock k)
| Slabel lbl' s' :=
      if ident_eq lbl lbl' then some(s', k) else find_label lbl s' k
| _ := none
  end

/- One step of execution -/

inductive step : state → trace → state → Prop :=

| step_skip_seq : ∀ f s k sp e m,
      step (State f Sskip (Kseq s k) sp e m)
        E0 (State f s k sp e m)
| step_skip_block : ∀ f k sp e m,
      step (State f Sskip (Kblock k) sp e m)
        E0 (State f Sskip k sp e m)
| step_skip_call : ∀ f k sp e m m',
      is_call_cont k →
      Mem.free m sp 0 f.(fn_stackspace) = some m' →
      step (State f Sskip k (Vptr sp Ptrofs.zero) e m)
        E0 (Returnstate Vundef k m')

| step_assign : ∀ f id a k sp e m v,
      eval_expr sp e m a v →
      step (State f (Sassign id a) k sp e m)
        E0 (State f Sskip k sp (PTree.set id v e) m)

| step_store : ∀ f chunk addr a k sp e m vaddr v m',
      eval_expr sp e m addr vaddr →
      eval_expr sp e m a v →
      Mem.storev chunk m vaddr v = some m' →
      step (State f (Sstore chunk addr a) k sp e m)
        E0 (State f Sskip k sp e m')

| step_call : ∀ f optid sig a bl k sp e m vf vargs fd,
      eval_expr sp e m a vf →
      eval_exprlist sp e m bl vargs →
      Genv.find_funct ge vf = some fd →
      funsig fd = sig →
      step (State f (Scall optid sig a bl) k sp e m)
        E0 (Callstate fd vargs (Kcall optid f sp e k) m)

| step_tailcall : ∀ f sig a bl k sp e m vf vargs fd m',
      eval_expr (Vptr sp Ptrofs.zero) e m a vf →
      eval_exprlist (Vptr sp Ptrofs.zero) e m bl vargs →
      Genv.find_funct ge vf = some fd →
      funsig fd = sig →
      Mem.free m sp 0 f.(fn_stackspace) = some m' →
      step (State f (Stailcall sig a bl) k (Vptr sp Ptrofs.zero) e m)
        E0 (Callstate fd vargs (call_cont k) m')

| step_builtin : ∀ f optid ef bl k sp e m vargs t vres m',
      eval_exprlist sp e m bl vargs →
      external_call ef ge vargs m t vres m' →
      step (State f (Sbuiltin optid ef bl) k sp e m)
         t (State f Sskip k sp (set_optvar optid vres e) m')

| step_seq : ∀ f s1 s2 k sp e m,
      step (State f (Sseq s1 s2) k sp e m)
        E0 (State f s1 (Kseq s2 k) sp e m)

| step_ifthenelse : ∀ f a s1 s2 k sp e m v b,
      eval_expr sp e m a v →
      Val.bool_of_val v b →
      step (State f (Sifthenelse a s1 s2) k sp e m)
        E0 (State f (if b then s1 else s2) k sp e m)

| step_loop : ∀ f s k sp e m,
      step (State f (Sloop s) k sp e m)
        E0 (State f s (Kseq (Sloop s) k) sp e m)

| step_block : ∀ f s k sp e m,
      step (State f (Sblock s) k sp e m)
        E0 (State f s (Kblock k) sp e m)

| step_exit_seq : ∀ f n s k sp e m,
      step (State f (Sexit n) (Kseq s k) sp e m)
        E0 (State f (Sexit n) k sp e m)
| step_exit_block_0 : ∀ f k sp e m,
      step (State f (Sexit O) (Kblock k) sp e m)
        E0 (State f Sskip k sp e m)
| step_exit_block_S : ∀ f n k sp e m,
      step (State f (Sexit (S n)) (Kblock k) sp e m)
        E0 (State f (Sexit n) k sp e m)

| step_switch : ∀ f islong a cases default k sp e m v n,
      eval_expr sp e m a v →
      switch_argument islong v n →
      step (State f (Sswitch islong a cases default) k sp e m)
        E0 (State f (Sexit (switch_target n default cases)) k sp e m)

| step_return_0 : ∀ f k sp e m m',
      Mem.free m sp 0 f.(fn_stackspace) = some m' →
      step (State f (Sreturn none) k (Vptr sp Ptrofs.zero) e m)
        E0 (Returnstate Vundef (call_cont k) m')
| step_return_1 : ∀ f a k sp e m v m',
      eval_expr (Vptr sp Ptrofs.zero) e m a v →
      Mem.free m sp 0 f.(fn_stackspace) = some m' →
      step (State f (Sreturn (some a)) k (Vptr sp Ptrofs.zero) e m)
        E0 (Returnstate v (call_cont k) m')

| step_label : ∀ f lbl s k sp e m,
      step (State f (Slabel lbl s) k sp e m)
        E0 (State f s k sp e m)

| step_goto : ∀ f lbl k sp e m s' k',
      find_label lbl f.(fn_body) (call_cont k) = some(s', k') →
      step (State f (Sgoto lbl) k sp e m)
        E0 (State f s' k' sp e m)

| step_internal_function : ∀ f vargs k m m' sp e,
      Mem.alloc m 0 f.(fn_stackspace) = (m', sp) →
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e →
      step (Callstate (Internal f) vargs k m)
        E0 (State f f.(fn_body) k (Vptr sp Ptrofs.zero) e m')
| step_external_function : ∀ ef vargs k m t vres m',
      external_call ef ge vargs m t vres m' →
      step (Callstate (External ef) vargs k m)
         t (Returnstate vres k m')

| step_return : ∀ v optid f sp e k m,
      step (Returnstate v (Kcall optid f sp e k) m)
        E0 (State f Sskip k sp (set_optvar optid v e) m)

end RELSEM

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
      funsig f = signature_main →
      initial_state p (Callstate f nil Kstop m0)

/- A final state is a [Returnstate] with an empty continuation. -/

inductive final_state : state → int32 → Prop :=
| final_state_intro : ∀ r m,
      final_state (Returnstate (Vint r) Kstop m) r

/- The corresponding small-step semantics. -/

def semantics (p : program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p)

/- This semantics is receptive to changes in events. -/

lemma semantics_receptive :
  ∀ (p : program), receptive (semantics p)
Proof
  intros. constructor; simpl; intros
/- receptiveness -/
  assert (t1 = E0 → ∃ s2, step (Genv.globalenv p) s t2 s2)
    intros. subst. inv H0. ∃ s1; auto
  inversion H; subst; auto
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]]
  ∃ (State f Sskip k sp (set_optvar optid vres2 e) m2). econstructor; eauto
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]]
  ∃ (Returnstate vres2 k m2). econstructor; eauto
/- trace length -/
  red; intros; inv H; simpl; try omega; eapply external_call_trace_length; eauto
Qed

/- * Alternate operational semantics (big-step) -/

/- We now define another semantics for Cminor without [goto] that follows
  the ``big-step'' style of semantics, also known as natural semantics.
  In this style, just like expressions evaluate to values,
  statements evaluate to``outcomes'' indicating how execution should
  proceed afterwards. -/

inductive outcome : Type :=
| Out_normal : outcome                /- continue in sequence -/
| Out_exit : ℕ → outcome           /- terminate [n+1] enclosing blocks -/
| Out_return : option val → outcome  /- return immediately to caller -/
| Out_tailcall_return : val → outcome. /- already returned to caller via a tailcall -/

def outcome_block (out : outcome) : outcome :=
  match out with
| Out_exit O := Out_normal
| Out_exit (S n) := Out_exit n
| out := out
  end

def outcome_result_value
    (out : outcome) (retsig : option typ) (vres : val) : Prop :=
  match out with
| Out_normal := vres = Vundef
| Out_return none := vres = Vundef
| Out_return (some v) := retsig ≠ none ∧ vres = v
| Out_tailcall_return v := vres = v
| _ := false
  end

def outcome_free_mem
    (out : outcome) (m : mem) (sp : block) (sz : ℤ) (m' : mem) :=
  match out with
| Out_tailcall_return _ := m' = m
| _ := Mem.free m sp 0 sz = some m'
  end

section NATURALSEM

parameter ge : genv

/- Evaluation of a function invocation: [eval_funcall ge m f args t m' res]
  means that the function [f], applied to the arguments [args] in
  memory state [m], returns the value [res] in modified memory state [m'].
  [t] is the trace of observable events generated during the invocation.
-/

inductive eval_funcall :
        mem → fundef → list val → trace →
        mem → val → Prop :=
| eval_funcall_internal :
      ∀ m f vargs m1 sp e t e2 m2 out vres m3,
      Mem.alloc m 0 f.(fn_stackspace) = (m1, sp) →
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e →
      exec_stmt f (Vptr sp Ptrofs.zero) e m1 f.(fn_body) t e2 m2 out →
      outcome_result_value out f.(fn_sig).(sig_res) vres →
      outcome_free_mem out m2 sp f.(fn_stackspace) m3 →
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
         env → mem → stmt → trace →
         env → mem → outcome → Prop :=
| exec_Sskip :
      ∀ f sp e m,
      exec_stmt f sp e m Sskip E0 e m Out_normal
| exec_Sassign :
      ∀ f sp e m id a v,
      eval_expr ge sp e m a v →
      exec_stmt f sp e m (Sassign id a) E0 (PTree.set id v e) m Out_normal
| exec_Sstore :
      ∀ f sp e m chunk addr a vaddr v m',
      eval_expr ge sp e m addr vaddr →
      eval_expr ge sp e m a v →
      Mem.storev chunk m vaddr v = some m' →
      exec_stmt f sp e m (Sstore chunk addr a) E0 e m' Out_normal
| exec_Scall :
      ∀ f sp e m optid sig a bl vf vargs fd t m' vres e',
      eval_expr ge sp e m a vf →
      eval_exprlist ge sp e m bl vargs →
      Genv.find_funct ge vf = some fd →
      funsig fd = sig →
      eval_funcall m fd vargs t m' vres →
      e' = set_optvar optid vres e →
      exec_stmt f sp e m (Scall optid sig a bl) t e' m' Out_normal
| exec_Sbuiltin :
      ∀ f sp e m optid ef bl t m' vargs vres e',
      eval_exprlist ge sp e m bl vargs →
      external_call ef ge vargs m t vres m' →
      e' = set_optvar optid vres e →
      exec_stmt f sp e m (Sbuiltin optid ef bl) t e' m' Out_normal
| exec_Sifthenelse :
      ∀ f sp e m a s1 s2 v b t e' m' out,
      eval_expr ge sp e m a v →
      Val.bool_of_val v b →
      exec_stmt f sp e m (if b then s1 else s2) t e' m' out →
      exec_stmt f sp e m (Sifthenelse a s1 s2) t e' m' out
| exec_Sseq_continue :
      ∀ f sp e m t s1 t1 e1 m1 s2 t2 e2 m2 out,
      exec_stmt f sp e m s1 t1 e1 m1 Out_normal →
      exec_stmt f sp e1 m1 s2 t2 e2 m2 out →
      t = t1 ** t2 →
      exec_stmt f sp e m (Sseq s1 s2) t e2 m2 out
| exec_Sseq_stop :
      ∀ f sp e m t s1 s2 e1 m1 out,
      exec_stmt f sp e m s1 t e1 m1 out →
      out ≠ Out_normal →
      exec_stmt f sp e m (Sseq s1 s2) t e1 m1 out
| exec_Sloop_loop :
      ∀ f sp e m s t t1 e1 m1 t2 e2 m2 out,
      exec_stmt f sp e m s t1 e1 m1 Out_normal →
      exec_stmt f sp e1 m1 (Sloop s) t2 e2 m2 out →
      t = t1 ** t2 →
      exec_stmt f sp e m (Sloop s) t e2 m2 out
| exec_Sloop_stop :
      ∀ f sp e m t s e1 m1 out,
      exec_stmt f sp e m s t e1 m1 out →
      out ≠ Out_normal →
      exec_stmt f sp e m (Sloop s) t e1 m1 out
| exec_Sblock :
      ∀ f sp e m s t e1 m1 out,
      exec_stmt f sp e m s t e1 m1 out →
      exec_stmt f sp e m (Sblock s) t e1 m1 (outcome_block out)
| exec_Sexit :
      ∀ f sp e m n,
      exec_stmt f sp e m (Sexit n) E0 e m (Out_exit n)
| exec_Sswitch :
      ∀ f sp e m islong a cases default v n,
      eval_expr ge sp e m a v →
      switch_argument islong v n →
      exec_stmt f sp e m (Sswitch islong a cases default)
                E0 e m (Out_exit (switch_target n default cases))
| exec_Sreturn_none :
      ∀ f sp e m,
      exec_stmt f sp e m (Sreturn none) E0 e m (Out_return none)
| exec_Sreturn_some :
      ∀ f sp e m a v,
      eval_expr ge sp e m a v →
      exec_stmt f sp e m (Sreturn (some a)) E0 e m (Out_return (some v))
| exec_Stailcall :
      ∀ f sp e m sig a bl vf vargs fd t m' m'' vres,
      eval_expr ge (Vptr sp Ptrofs.zero) e m a vf →
      eval_exprlist ge (Vptr sp Ptrofs.zero) e m bl vargs →
      Genv.find_funct ge vf = some fd →
      funsig fd = sig →
      Mem.free m sp 0 f.(fn_stackspace) = some m' →
      eval_funcall m' fd vargs t m'' vres →
      exec_stmt f (Vptr sp Ptrofs.zero) e m (Stailcall sig a bl) t e m'' (Out_tailcall_return vres)

Scheme eval_funcall_ind2 := Minimality for eval_funcall Sort Prop
  with exec_stmt_ind2 := Minimality for exec_stmt Sort Prop
Combined Scheme eval_funcall_exec_stmt_ind2
  from eval_funcall_ind2, exec_stmt_ind2

/- Coinductive semantics for divergence.
  [evalinf_funcall ge m f args t]
  means that the function [f] diverges when applied to the arguments [args] in
  memory state [m].  The infinite trace [t] is the trace of
  observable events generated during the invocation.
-/

CoInductive evalinf_funcall :
        mem → fundef → list val → traceinf → Prop :=
| evalinf_funcall_internal :
      ∀ m f vargs m1 sp e t,
      Mem.alloc m 0 f.(fn_stackspace) = (m1, sp) →
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e →
      execinf_stmt f (Vptr sp Ptrofs.zero) e m1 f.(fn_body) t →
      evalinf_funcall m (Internal f) vargs t

/- [execinf_stmt ge sp e m s t] means that statement [s] diverges.
  [e] is the initial environment, [m] is the initial memory state,
  and [t] the trace of observable events performed during the execution. -/

with execinf_stmt :
         function → val → env → mem → stmt → traceinf → Prop :=
| execinf_Scall :
      ∀ f sp e m optid sig a bl vf vargs fd t,
      eval_expr ge sp e m a vf →
      eval_exprlist ge sp e m bl vargs →
      Genv.find_funct ge vf = some fd →
      funsig fd = sig →
      evalinf_funcall m fd vargs t →
      execinf_stmt f sp e m (Scall optid sig a bl) t
| execinf_Sifthenelse :
      ∀ f sp e m a s1 s2 v b t,
      eval_expr ge sp e m a v →
      Val.bool_of_val v b →
      execinf_stmt f sp e m (if b then s1 else s2) t →
      execinf_stmt f sp e m (Sifthenelse a s1 s2) t
| execinf_Sseq_1 :
      ∀ f sp e m t s1 s2,
      execinf_stmt f sp e m s1 t →
      execinf_stmt f sp e m (Sseq s1 s2) t
| execinf_Sseq_2 :
      ∀ f sp e m t s1 t1 e1 m1 s2 t2,
      exec_stmt f sp e m s1 t1 e1 m1 Out_normal →
      execinf_stmt f sp e1 m1 s2 t2 →
      t = t1 *** t2 →
      execinf_stmt f sp e m (Sseq s1 s2) t
| execinf_Sloop_body :
      ∀ f sp e m s t,
      execinf_stmt f sp e m s t →
      execinf_stmt f sp e m (Sloop s) t
| execinf_Sloop_loop :
      ∀ f sp e m s t t1 e1 m1 t2,
      exec_stmt f sp e m s t1 e1 m1 Out_normal →
      execinf_stmt f sp e1 m1 (Sloop s) t2 →
      t = t1 *** t2 →
      execinf_stmt f sp e m (Sloop s) t
| execinf_Sblock :
      ∀ f sp e m s t,
      execinf_stmt f sp e m s t →
      execinf_stmt f sp e m (Sblock s) t
| execinf_Stailcall :
      ∀ f sp e m sig a bl vf vargs fd m' t,
      eval_expr ge (Vptr sp Ptrofs.zero) e m a vf →
      eval_exprlist ge (Vptr sp Ptrofs.zero) e m bl vargs →
      Genv.find_funct ge vf = some fd →
      funsig fd = sig →
      Mem.free m sp 0 f.(fn_stackspace) = some m' →
      evalinf_funcall m' fd vargs t →
      execinf_stmt f (Vptr sp Ptrofs.zero) e m (Stailcall sig a bl) t

end NATURALSEM

/- Big-step execution of a whole program -/

inductive bigstep_program_terminates (p : program) : trace → int32 → Prop :=
| bigstep_program_terminates_intro :
      ∀ b f m0 t m r,
      let ge := Genv.globalenv p in
      Genv.init_mem p = some m0 →
      Genv.find_symbol ge p.(prog_main) = some b →
      Genv.find_funct_ptr ge b = some f →
      funsig f = signature_main →
      eval_funcall ge m0 f nil t m (Vint r) →
      bigstep_program_terminates p t r

inductive bigstep_program_diverges (p : program) : traceinf → Prop :=
| bigstep_program_diverges_intro :
      ∀ b f m0 t,
      let ge := Genv.globalenv p in
      Genv.init_mem p = some m0 →
      Genv.find_symbol ge p.(prog_main) = some b →
      Genv.find_funct_ptr ge b = some f →
      funsig f = signature_main →
      evalinf_funcall ge m0 f nil t →
      bigstep_program_diverges p t

def bigstep_semantics (p : program) :=
  Bigstep_semantics (bigstep_program_terminates p) (bigstep_program_diverges p)

/- ** Correctness of the big-step semantics with respect to the transition semantics -/

section BIGSTEP_TO_TRANSITION

parameter prog : program
def ge := Genv.globalenv prog

inductive outcome_state_match
        (sp : val) (e : env) (m : mem) (f : function) (k : cont) :
        outcome → state → Prop :=
| osm_normal :
      outcome_state_match sp e m f k
                          Out_normal
                          (State f Sskip k sp e m)
| osm_exit : ∀ n,
      outcome_state_match sp e m f k
                          (Out_exit n)
                          (State f (Sexit n) k sp e m)
| osm_return_none : ∀ k',
      call_cont k' = call_cont k →
      outcome_state_match sp e m f k
                          (Out_return none)
                          (State f (Sreturn none) k' sp e m)
| osm_return_some : ∀ k' a v,
      call_cont k' = call_cont k →
      eval_expr ge sp e m a v →
      outcome_state_match sp e m f k
                          (Out_return (some v))
                          (State f (Sreturn (some a)) k' sp e m)
| osm_tail : ∀ v,
      outcome_state_match sp e m f k
                          (Out_tailcall_return v)
                          (Returnstate v (call_cont k) m)

theorem is_call_cont_call_cont :
  ∀ k, is_call_cont (call_cont k)
Proof
  induction k; simpl; auto
Qed

theorem call_cont_is_call_cont :
  ∀ k, is_call_cont k → call_cont k = k
Proof
  destruct k; simpl; intros; auto || contradiction
Qed

lemma eval_funcall_exec_stmt_steps :
  (∀ m fd args t m' res,
   eval_funcall ge m fd args t m' res →
   ∀ k,
   is_call_cont k →
   star step ge (Callstate fd args k m)
              t (Returnstate res k m'))
∧(∀ f sp e m s t e' m' out,
   exec_stmt ge f sp e m s t e' m' out →
   ∀ k,
   ∃ S,
   star step ge (State f s k sp e m) t S
   ∧ outcome_state_match sp e' m' f k out S)
Proof
  apply eval_funcall_exec_stmt_ind2; intros

/- funcall internal -/
  destruct (H2 k) as [S [A B]]
  assert (call_cont k = k) by (apply call_cont_is_call_cont; auto)
  eapply star_left. econstructor; eauto
  eapply star_trans. eexact A
  inversion B; clear B; subst out; simpl in H3; simpl; try contradiction
  /- Out normal -/
  subst vres. apply star_one. apply step_skip_call; auto
  /- Out_return None -/
  subst vres. replace k with (call_cont k') by congruence
  apply star_one. apply step_return_0; auto
  /- Out_return Some -/
  destruct H3. subst vres
  replace k with (call_cont k') by congruence
  apply star_one. eapply step_return_1; eauto
  /- Out_tailcall_return -/
  subst vres. red in H4. subst m3. rewrite H6. apply star_refl

  reflexivity. traceEq

/- funcall external -/
  apply star_one. constructor; auto

/- skip -/
  econstructor; split
  apply star_refl
  constructor

/- assign -/
  ∃ (State f Sskip k sp (PTree.set id v e) m); split
  apply star_one. constructor. auto
  constructor

/- store -/
  econstructor; split
  apply star_one. econstructor; eauto
  constructor

/- call -/
  econstructor; split
  eapply star_left. econstructor; eauto
  eapply star_right. apply H4. red; auto
  constructor. reflexivity. traceEq
  subst e'. constructor

/- builtin -/
  econstructor; split
  apply star_one. econstructor; eauto
  subst e'. constructor

/- ifthenelse -/
  destruct (H2 k) as [S [A B]]
  ∃ S; split
  apply star_left with E0 (State f (if b then s1 else s2) k sp e m) t
  econstructor; eauto. exact A
  traceEq
  auto

/- seq continue -/
  destruct (H0 (Kseq s2 k)) as [S1 [A1 B1]]
  destruct (H2 k) as [S2 [A2 B2]]
  inv B1
  ∃ S2; split
  eapply star_left. constructor
  eapply star_trans. eexact A1
  eapply star_left. constructor. eexact A2
  reflexivity. reflexivity. traceEq
  auto

/- seq stop -/
  destruct (H0 (Kseq s2 k)) as [S1 [A1 B1]]
  set (S2 :=
    match out with
    | Out_exit n := State f (Sexit n) k sp e1 m1
    | _ := S1
    end)
  ∃ S2; split
  eapply star_left. constructor. eapply star_trans. eexact A1
  unfold S2; destruct out; try (apply star_refl)
  inv B1. apply star_one. constructor
  reflexivity. traceEq
  unfold S2; inv B1; congruence || simpl; constructor; auto

/- loop loop -/
  destruct (H0 (Kseq (Sloop s) k)) as [S1 [A1 B1]]
  destruct (H2 k) as [S2 [A2 B2]]
  inv B1
  ∃ S2; split
  eapply star_left. constructor
  eapply star_trans. eexact A1
  eapply star_left. constructor. eexact A2
  reflexivity. reflexivity. traceEq
  auto

/- loop stop -/
  destruct (H0 (Kseq (Sloop s) k)) as [S1 [A1 B1]]
  set (S2 :=
    match out with
    | Out_exit n := State f (Sexit n) k sp e1 m1
    | _ := S1
    end)
  ∃ S2; split
  eapply star_left. constructor. eapply star_trans. eexact A1
  unfold S2; destruct out; try (apply star_refl)
  inv B1. apply star_one. constructor
  reflexivity. traceEq
  unfold S2; inv B1; congruence || simpl; constructor; auto

/- block -/
  destruct (H0 (Kblock k)) as [S1 [A1 B1]]
  set (S2 :=
    match out with
    | Out_normal := State f Sskip k sp e1 m1
    | Out_exit O := State f Sskip k sp e1 m1
    | Out_exit (S m) := State f (Sexit m) k sp e1 m1
    | _ := S1
    end)
  ∃ S2; split
  eapply star_left. constructor. eapply star_trans. eexact A1
  unfold S2; destruct out; try (apply star_refl)
  inv B1. apply star_one. constructor
  inv B1. apply star_one. destruct n; constructor
  reflexivity. traceEq
  unfold S2; inv B1; simpl; try constructor; auto
  destruct n; constructor

/- exit -/
  econstructor; split. apply star_refl. constructor

/- switch -/
  econstructor; split
  apply star_one. econstructor; eauto. constructor

/- return none -/
  econstructor; split. apply star_refl. constructor; auto

/- return some -/
  econstructor; split. apply star_refl. constructor; auto

/- tailcall -/
  econstructor; split
  eapply star_left. econstructor; eauto
  apply H5. apply is_call_cont_call_cont. traceEq
  econstructor
Qed

lemma eval_funcall_steps :
   ∀ m fd args t m' res,
   eval_funcall ge m fd args t m' res →
   ∀ k,
   is_call_cont k →
   star step ge (Callstate fd args k m)
              t (Returnstate res k m')
Proof (proj1 eval_funcall_exec_stmt_steps)

lemma exec_stmt_steps :
   ∀ f sp e m s t e' m' out,
   exec_stmt ge f sp e m s t e' m' out →
   ∀ k,
   ∃ S,
   star step ge (State f s k sp e m) t S
   ∧ outcome_state_match sp e' m' f k out S
Proof (proj2 eval_funcall_exec_stmt_steps)

lemma evalinf_funcall_forever :
  ∀ m fd args T k,
  evalinf_funcall ge m fd args T →
  forever_plus step ge (Callstate fd args k m) T
Proof
  cofix CIH_FUN
  assert (∀ sp e m s T f k,
          execinf_stmt ge f sp e m s T →
          forever_plus step ge (State f s k sp e m) T)
  cofix CIH_STMT
  intros. inv H

/- call -/
  eapply forever_plus_intro
  apply plus_one. econstructor; eauto
  apply CIH_FUN. eauto. traceEq

/- ifthenelse -/
  eapply forever_plus_intro with (s2 := State f (if b then s1 else s2) k sp e m)
  apply plus_one. econstructor; eauto
  apply CIH_STMT. eauto. traceEq

/- seq 1 -/
  eapply forever_plus_intro
  apply plus_one. constructor
  apply CIH_STMT. eauto. traceEq

/- seq 2 -/
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ _ H0 (Kseq s2 k))
  as [S [A B]]. inv B
  eapply forever_plus_intro
  eapply plus_left. constructor
  eapply star_right. eexact A. constructor
  reflexivity. reflexivity
  apply CIH_STMT. eauto. traceEq

/- loop body -/
  eapply forever_plus_intro
  apply plus_one. econstructor; eauto
  apply CIH_STMT. eauto. traceEq

/- loop loop -/
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ _ H0 (Kseq (Sloop s0) k))
  as [S [A B]]. inv B
  eapply forever_plus_intro
  eapply plus_left. constructor
  eapply star_right. eexact A. constructor
  reflexivity. reflexivity
  apply CIH_STMT. eauto. traceEq

/- block -/
  eapply forever_plus_intro
  apply plus_one. econstructor; eauto
  apply CIH_STMT. eauto. traceEq

/- tailcall -/
  eapply forever_plus_intro
  apply plus_one. econstructor; eauto
  apply CIH_FUN. eauto. traceEq

/- function call -/
  intros. inv H0
  eapply forever_plus_intro
  apply plus_one. econstructor; eauto
  apply H. eauto
  traceEq
Qed

theorem bigstep_semantics_sound :
  bigstep_sound (bigstep_semantics prog) (semantics prog)
Proof
  constructor; intros
/- termination -/
  inv H. econstructor; econstructor
  split. econstructor; eauto
  split. apply eval_funcall_steps. eauto. red; auto
  econstructor
/- divergence -/
  inv H. econstructor
  split. econstructor; eauto
  eapply forever_plus_forever
  eapply evalinf_funcall_forever; eauto
Qed

end BIGSTEP_TO_TRANSITION.

end cminor