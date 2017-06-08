
/- Observable events, execution traces, and semantics of external calls. -/

import .globalenvs .memory

namespace events
open integers word floats ast globalenvs values memory
     ast.typ memory.perm_kind

/- * Events and traces -/

/- The observable behaviour of programs is stated in terms of
  input/output events, which represent the actions of the program
  that the external world can observe.  CompCert leaves much flexibility as to
  the exact content of events: the only requirement is that they
  do not expose memory states nor pointer values
  (other than pointers to global variables), because these
  are not preserved literally during compilation.  For concreteness,
  we use the following type for events.  Each event represents either:

- A system call (e.g. an input/output operation), recording the
  name of the system call, its parameters, and its result.

- A volatile load from a global memory location, recording the chunk
  and address being read and the value just read.

- A volatile store to a global memory location, recording the chunk
  and address being written and the value stored there.

- An annotation, recording the text of the annotation and the values
  of the arguments.

  The values attached to these events are of the following form.
  As mentioned above, we do not expose pointer values directly.
  Pointers relative to a global variable are shown with the name
  of the variable instead of the block identifier.
-/

inductive eventval : Type
| EVint        : int32 → eventval
| EVlong       : int64 → eventval
| EVfloat      : float → eventval
| EVsingle     : float32 → eventval
| EVptr_global : ident → ptrofs → eventval
open eventval

inductive event : Type
| syscall : string → list eventval → eventval → event
| vload   : memory_chunk → ident → ptrofs → eventval → event
| vstore  : memory_chunk → ident → ptrofs → eventval → event
| annot   : string → list eventval → event

/- * Relating values and event values -/

namespace eventval

def type : eventval → typ
| (EVint _)          := Tint
| (EVlong _)         := Tlong
| (EVfloat _)        := Tfloat
| (EVsingle _)       := Tsingle
| (EVptr_global _ _) := Tptr

/- Symbol environment used to translate between global variable names and their block identifiers. -/

section
variable (ge : Senv)

/- Translation between values and event values. -/

def to_val : eventval → option val
| (EVint i)             := some (Vint i)
| (EVlong i)            := some (Vlong i)
| (EVfloat f)           := some (Vfloat f)
| (EVsingle f)          := some (Vsingle f)
| (EVptr_global id ofs) :=
  do guard (Senv.public_symbol ge id),
     b ← Senv.find_symbol ge id,
     return (Vptr b ofs)

def matchv (ev : eventval) (t : typ) (v : val) : Prop :=
ev.type = t ∧ ev.to_val ge = some v

def list_match (evl : list eventval) (tl : list typ) (vl : list val) : Prop :=
evl.map type = tl ∧ mmap (to_val ge) evl = some vl

/- Some properties of these translation predicates. -/

lemma match_type {ev ty v} : matchv ge ev ty v → val.has_type v ty := sorry'

lemma match_lessdef {ev ty v1 v2} :
  matchv ge ev ty v1 → val.lessdef v1 v2 → matchv ge ev ty v2 := sorry'

lemma list_match_lessdef {evl tyl vl1} :
  list_match ge evl tyl vl1 →
  ∀ vl2, list.forall2 val.lessdef vl1 vl2 → list_match ge evl tyl vl2 := sorry'

/- Determinism -/

lemma match_determ_1 {ev ty v1 v2} :
  matchv ge ev ty v1 → matchv ge ev ty v2 → v1 = v2 := sorry'

lemma match_determ_2 {ev1 ev2 ty v} :
  matchv ge ev1 ty v → matchv ge ev2 ty v → ev1 = ev2 := sorry'

lemma list_match_determ_2 {evl1 tyl vl} :
  list_match ge evl1 tyl vl →
  ∀ evl2, list_match ge evl2 tyl vl → evl1 = evl2 := sorry'

/- Validity -/

def valid : eventval → bool
| (EVptr_global id ofs) := Senv.public_symbol ge id
| _                     := tt

lemma match_receptive {ev1 ty v1 ev2} :
  matchv ge ev1 ty v1 →
  valid ge ev1 → valid ge ev2 → type ev1 = type ev2 →
  ∃ v2, matchv ge ev2 ty v2 := sorry'

lemma match_valid {ev ty v} :
  matchv ge ev ty v → valid ge ev := sorry'

lemma match_same_type {ev1 ty v1 ev2 v2} :
  matchv ge ev1 ty v1 → matchv ge ev2 ty v2 → type ev1 = type ev2 := sorry'

end
end eventval

/- Invariance under changes to the global environment -/

section eventval_inv

parameters {ge1 ge2 : Senv}
parameter (public_preserved : ∀ id,
  Senv.public_symbol ge2 id = Senv.public_symbol ge1 id)

lemma eventval_valid_preserved {ev} :
  eventval.valid ge1 ev → eventval.valid ge2 ev := sorry'

parameter (symbols_preserved : ∀ id,
  Senv.find_symbol ge2 id = Senv.find_symbol ge1 id)

lemma eventval_match_preserved {ev ty v} :
  eventval.matchv ge1 ev ty v → eventval.matchv ge2 ev ty v := sorry'

lemma eventval_list_match_preserved :
  ∀ evl tyl vl,
  eventval.list_match ge1 evl tyl vl → eventval.list_match ge2 evl tyl vl := sorry'

end eventval_inv

/- Compatibility with memory injections -/

section eventval_inject

parameter (f : block → option (block × ℤ))
parameters (ge1 ge2 : Senv)

def symbols_inject : Prop :=
   (∀ id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id)
∧ (∀ id b1 b2 delta,
     f b1 = some (b2, delta) → Senv.find_symbol ge1 id = some b1 →
     delta = 0 ∧ Senv.find_symbol ge2 id = some b2)
∧ (∀ id b1,
     Senv.public_symbol ge1 id = tt → Senv.find_symbol ge1 id = some b1 →
     ∃ b2, f b1 = some (b2, 0) ∧ Senv.find_symbol ge2 id = some b2)
∧ (∀ b1 b2 delta,
     f b1 = some (b2, delta) →
     Senv.block_is_volatile ge2 b2 = Senv.block_is_volatile ge1 b1)

parameter symb_inj : symbols_inject

lemma eventval_match_inject {ev ty v1 v2} :
  eventval.matchv ge1 ev ty v1 → val.inject f v1 v2 → eventval.matchv ge2 ev ty v2 := sorry'

lemma eventval_match_inject_2 :
  ∀ ev ty v1,
  eventval.matchv ge1 ev ty v1 →
  ∃ v2, eventval.matchv ge2 ev ty v2 ∧ val.inject f v1 v2 := sorry'

lemma eventval_list_match_inject {evl tyl vl1} :
  eventval.list_match ge1 evl tyl vl1 →
  ∀ vl2, list.forall2 (val.inject f) vl1 vl2 → eventval.list_match ge2 evl tyl vl2 := sorry'

end eventval_inject

/- * Matching traces. -/

section match_traces

parameter ge : Senv

/- Matching between traces corresponding to single transitions.
  Arguments (provided by the program) must be equal.
  Results (provided by the outside world) can vary as long as they
  can be converted safely to values. -/

def match_events : event → event → Prop
| (event.syscall id args res1)    (event.syscall id' args' res2)      :=
  id = id' ∧ args = args' ∧ res1.valid ge ∧ res2.valid ge ∧ res1.type = res2.type
| (event.vload chunk id ofs res1) (event.vload chunk' id' ofs' res2)  :=
  chunk = chunk' ∧ id = id' ∧ ofs = ofs' ∧ res1.valid ge ∧ res2.valid ge ∧ res1.type = res2.type
| (event.vstore chunk id ofs arg) (event.vstore chunk' id' ofs' arg') :=
  chunk = chunk' ∧ id = id' ∧ ofs = ofs' ∧ arg = arg'
| (event.annot id args)           (event.annot id' args')             :=
  id = id' ∧ args = args'
| _                               _                                   := false

inductive match_traces : list event → list event → Prop
| nil : match_traces [] []
| evt (e1 e2) : match_events e1 e2 → match_traces [e1] [e2]

end match_traces

/- Invariance by change of global environment -/

lemma match_traces_preserved {ge1 ge2}
  (public_preserved : ∀ id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id)
  {t1 t2} : match_traces ge1 t1 t2 → match_traces ge2 t1 t2 := sorry'

/- An output trace is a trace composed only of output events,
  that is, events that do not take any result from the outside world. -/

def output_event : event → bool
| (event.vstore _ _ _ _) := tt
| (event.annot _ _)      := tt
| _                      := ff

def output_trace (t : list event) : bool := t.all output_event

/- * Semantics of external functions -/

/- For each external function, its behavior is defined by a predicate relating:
- the global symbol environment
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).
-/

def extcall_sem : Type := Senv → list val → mem → list event → val → mem → Prop

/- We now specify the expected properties of this predicate. -/

def loc_out_of_bounds (m : mem) (b : block) (ofs : ℕ) : Prop :=
  ¬ perm m b ofs Max Nonempty

def loc_not_writable (m : mem) (b : block) (ofs : ℕ) : Prop :=
  ¬ perm m b ofs Max Writable

def loc_unmapped (f : meminj) (b : block) (ofs : ℕ) : Prop :=
  f b = none

def loc_out_of_reach (f : meminj) (m : mem) (b : block) (ofs : ℕ) : Prop :=
  ∀ b0 delta,
  f b0 = some (b, delta) → ¬ perm_Z m b0 (ofs - delta) Max Nonempty

def inject_separated (f f' : meminj) (m1 m2 : mem) : Prop :=
  ∀ b1 b2 delta,
  f b1 = none → f' b1 = some (b2, delta) →
  ¬ valid_block m1 b1 ∧ ¬ valid_block m2 b2

structure extcall_properties (sem : extcall_sem) (sg : signature) : Prop :=
/- The return value of an external call must agree with its signature. -/
(well_typed :
  ∀ ge vargs m1 t vres m2,
  sem ge vargs m1 t vres m2 →
  vres.has_type (proj_sig_res sg))

/- The semantics is invariant under change of global environment that preserves symbols. -/
(symbols_preserved :
  ∀ ge1 ge2 vargs m1 t vres m2,
  Senv.equiv ge1 ge2 →
  sem ge1 vargs m1 t vres m2 →
  sem ge2 vargs m1 t vres m2)

/- External calls cannot invalidate memory blocks.  (Remember that
  freeing a block does not invalidate its block identifier.) -/
(valid_block :
  ∀ ge vargs m1 t vres m2 b,
  sem ge vargs m1 t vres m2 →
  valid_block m1 b → valid_block m2 b)

/- External calls cannot increase the max permissions of a valid block.
    They can decrease the max permissions, e.g. by freeing. -/
(max_perm :
  ∀ ge vargs m1 t vres m2 b ofs p,
  sem ge vargs m1 t vres m2 →
  memory.valid_block m1 b → perm m2 b ofs Max p → perm m1 b ofs Max p)

/- External call cannot modify memory unless they have [Max, Writable]
   permissions. -/
(readonly :
  ∀ ge vargs m1 t vres m2,
  sem ge vargs m1 t vres m2 →
  unchanged_on (loc_not_writable m1) m1 m2)

/- External calls must commute with memory extensions, in the
  following sense. -/
(mem_extends :
  ∀ ge vargs m1 t vres m2 m1' vargs',
  sem ge vargs m1 t vres m2 →
  extends' m1 m1' →
  list.forall2 lessdef vargs vargs' →
  ∃ vres', ∃ m2',
      sem ge vargs' m1' t vres' m2'
  ∧ lessdef vres vres'
  ∧ extends' m2 m2'
  ∧ unchanged_on (loc_out_of_bounds m1) m1' m2')

/- External calls must commute with memory injections,
  in the following sense. -/
(mem_inject :
  ∀ ge1 ge2 vargs m1 t vres m2 f m1' vargs',
  symbols_inject f ge1 ge2 →
  sem ge1 vargs m1 t vres m2 →
  inject f m1 m1' →
  list.forall2 (val.inject f) vargs vargs' →
  ∃ f', ∃ vres', ∃ m2',
      sem ge2 vargs' m1' t vres' m2'
  ∧ inject f' vres vres'
  ∧ inject f' m2 m2'
  ∧ unchanged_on (loc_unmapped f) m1 m2
  ∧ unchanged_on (loc_out_of_reach f m1) m1' m2'
  ∧ inject_incr f f'
  ∧ inject_separated f f' m1 m1')

/- External calls produce at most one event. -/
(trace_length :
  ∀ ge vargs m t vres m',
  sem ge vargs m t vres m' → t.length ≤ 1)

/- External calls must be receptive to changes of traces by another, matching trace. -/
(receptive :
  ∀ ge vargs m t1 vres1 m1 t2,
  sem ge vargs m t1 vres1 m1 → match_traces ge t1 t2 →
  ∃ vres2 m2, sem ge vargs m t2 vres2 m2)

/- External calls must be deterministic up to matching between traces. -/
(determ :
  ∀ ge vargs m t1 vres1 m1 t2 vres2 m2,
  sem ge vargs m t1 vres1 m1 → sem ge vargs m t2 vres2 m2 →
  match_traces ge t1 t2 ∧ (t1 = t2 → vres1 = vres2 ∧ m1 = m2))

/- * Semantics of volatile memory accesses -/

inductive volatile_load (ge) (chunk : memory_chunk) (m b ofs) :
    list event → val → Prop
| volatile_load_vol (id ev v) :
    Senv.block_is_volatile ge b = tt →
    Senv.find_symbol ge id = some b →
    eventval.matchv ge ev chunk.type v →
    volatile_load [event.vload chunk id ofs ev] (load_result chunk v)
| volatile_load_nonvol (v) :
    Senv.block_is_volatile ge b = ff →
    load chunk m b (unsigned ofs) = some v →
    volatile_load [] v

inductive volatile_store (ge) (chunk : memory_chunk) (m b ofs v) :
    list event → mem → Prop
| volatile_store_vol (id ev) :
    Senv.block_is_volatile ge b = tt →
    Senv.find_symbol ge id = some b →
    eventval.matchv ge ev chunk.type (load_result chunk v) →
    volatile_store [event.vstore chunk id ofs ev] m
| volatile_store_nonvol (m') :
    Senv.block_is_volatile ge b = ff →
    store chunk m b (unsigned ofs) v = some m' →
    volatile_store [] m'

/- ** Semantics of volatile loads -/

inductive volatile_load_sem (chunk : memory_chunk) (ge : Senv) :
  list val → mem → list event → val → mem → Prop
| mk (b ofs m t v) :
  volatile_load ge chunk m b ofs t v →
  volatile_load_sem [Vptr b ofs] m t v m.

lemma volatile_load_preserved {ge1 ge2 chunk m b ofs t v} :
  Senv.equiv ge1 ge2 →
  volatile_load ge1 chunk m b ofs t v →
  volatile_load ge2 chunk m b ofs t v := sorry'

lemma volatile_load_extends {ge chunk m b ofs t v m'} :
  volatile_load ge chunk m b ofs t v →
  extends' m m' →
  ∃ v', volatile_load ge chunk m' b ofs t v' ∧ lessdef v v' := sorry'

lemma volatile_load_inject {ge1 ge2 f chunk m b ofs t v b' ofs' m'} :
  symbols_inject f ge1 ge2 →
  volatile_load ge1 chunk m b ofs t v →
  inject f (Vptr b ofs) (Vptr b' ofs') →
  inject f m m' →
  ∃ v', volatile_load ge2 chunk m' b' ofs' t v' ∧ inject f v v' := sorry'

lemma volatile_load_receptive {ge chunk m b ofs t1 t2 v1} :
  volatile_load ge chunk m b ofs t1 v1 → match_traces ge t1 t2 →
  ∃ v2, volatile_load ge chunk m b ofs t2 v2 := sorry'

lemma volatile_load_ok {chunk} :
  extcall_properties (volatile_load_sem chunk)
  ⟨[Tptr], some chunk.type, cc_default⟩ :=
{ well_typed        := sorry',
  symbols_preserved := sorry',
  valid_block       := sorry',
  max_perm          := sorry',
  readonly          := sorry',
  mem_extends       := sorry',
  mem_inject        := sorry',
  trace_length      := sorry',
  receptive         := sorry',
  determ            := sorry' }

/- ** Semantics of volatile stores -/

inductive volatile_store_sem (chunk : memory_chunk) (ge : Senv) :
  list val → mem → list event → val → mem → Prop
| mk (b ofs m1 v t m2) :
  volatile_store ge chunk m1 b ofs v t m2 →
  volatile_store_sem [Vptr b ofs, v] m1 t Vundef m2.

lemma volatile_store_preserved {ge1 ge2 chunk m1 b ofs v t m2} :
  Senv.equiv ge1 ge2 →
  volatile_store ge1 chunk m1 b ofs v t m2 →
  volatile_store ge2 chunk m1 b ofs v t m2 := sorry'

lemma volatile_store_readonly {ge chunk1 m1 b1 ofs1 v t m2} :
  volatile_store ge chunk1 m1 b1 ofs1 v t m2 →
  unchanged_on (loc_not_writable m1) m1 m2 := sorry'

lemma volatile_store_extends {ge chunk m1 b ofs v t m2 m1' v'} :
  volatile_store ge chunk m1 b ofs v t m2 →
  extends' m1 m1' →
  lessdef v v' →
  ∃ m2',
     volatile_store ge chunk m1' b ofs v' t m2'
  ∧ extends' m2 m2'
  ∧ unchanged_on (loc_out_of_bounds m1) m1' m2' := sorry'

lemma volatile_store_inject {ge1 ge2 f chunk m1 b ofs v t m2 m1' b' ofs' v'} :
  symbols_inject f ge1 ge2 →
  volatile_store ge1 chunk m1 b ofs v t m2 →
  inject f (Vptr b ofs) (Vptr b' ofs') →
  inject f v v' →
  inject f m1 m1' →
  ∃ m2',
       volatile_store ge2 chunk m1' b' ofs' v' t m2'
    ∧ inject f m2 m2'
    ∧ unchanged_on (loc_unmapped f) m1 m2
    ∧ unchanged_on (loc_out_of_reach f m1) m1' m2' := sorry'

lemma volatile_store_receptive {ge chunk m b ofs v t1 m1 t2} :
  volatile_store ge chunk m b ofs v t1 m1 → match_traces ge t1 t2 → t1 = t2 := sorry'

lemma volatile_store_ok {chunk} :
  extcall_properties (volatile_store_sem chunk) ⟨[Tptr, chunk.type], none, cc_default⟩ :=
{ well_typed        := sorry',
  symbols_preserved := sorry',
  valid_block       := sorry',
  max_perm          := sorry',
  readonly          := sorry',
  mem_extends       := sorry',
  mem_inject        := sorry',
  trace_length      := sorry',
  receptive         := sorry',
  determ            := sorry' }

/- ** Semantics of dynamic memory allocation (malloc) -/

inductive extcall_malloc_sem (ge : Senv) :
  list val → mem → list event → val → mem → Prop
| mk (sz : ptrofs) (m m' : mem) :
  store Mptr (m.alloc 0 (unsigned sz + Mptr.size)) m.nextblock 0 (Vptrofs sz) = some m' →
  extcall_malloc_sem [Vptrofs sz] m [] (Vptr m.nextblock Mptr.size) m'

lemma extcall_malloc_ok :
  extcall_properties extcall_malloc_sem ⟨[Tptr], some Tptr, cc_default⟩ :=
{ well_typed        := sorry',
  symbols_preserved := sorry',
  valid_block       := sorry',
  max_perm          := sorry',
  readonly          := sorry',
  mem_extends       := sorry',
  mem_inject        := sorry',
  trace_length      := sorry',
  receptive         := sorry',
  determ            := sorry' }

/- ** Semantics of dynamic memory deallocation (free) -/

inductive extcall_free_sem (ge : Senv) :
              list val → mem → list event → val → mem → Prop
| mk (b) (lo : ptrofs) (sz m m') :
  load Mptr m b (unsigned lo - Mptr.size) = some (Vptrofs sz) →
  unsigned sz > 0 →
  free m b (unsigned lo - Mptr.size) (unsigned lo + unsigned sz) = some m' →
  extcall_free_sem [Vptr b lo] m [] Vundef m'

lemma extcall_free_ok :
  extcall_properties extcall_free_sem ⟨[Tptr], none, cc_default⟩ :=
{ well_typed        := sorry',
  symbols_preserved := sorry',
  valid_block       := sorry',
  max_perm          := sorry',
  readonly          := sorry',
  mem_extends       := sorry',
  mem_inject        := sorry',
  trace_length      := sorry',
  receptive         := sorry',
  determ            := sorry' }

/- ** Semantics of [memcpy] operations. -/

inductive extcall_memcpy_sem (sz al : ℕ) (ge : Senv) :
  list val → mem → list event → val → mem → Prop
| mk (bdst bsrc) (odst osrc : ptrofs) (m bytes m') :
  al = 1 ∨ al = 2 ∨ al = 4 ∨ al = 8 → al ∣ sz →
  (sz > 0 → al ∣ unsigned osrc ∧ al ∣ unsigned odst) →
  bsrc ≠ bdst ∨ unsigned osrc = unsigned odst
                ∨ unsigned osrc + sz ≤ unsigned odst
                ∨ unsigned odst + sz ≤ unsigned osrc →
  load_bytes m bsrc (unsigned osrc) sz = some bytes →
  store_bytes m bdst (unsigned odst) bytes = some m' →
  extcall_memcpy_sem [Vptr bdst odst, Vptr bsrc osrc] m [] Vundef m'

lemma extcall_memcpy_ok (sz al) :
  extcall_properties (extcall_memcpy_sem sz al) ⟨[Tptr, Tptr], none, cc_default⟩ :=
{ well_typed        := sorry',
  symbols_preserved := sorry',
  valid_block       := sorry',
  max_perm          := sorry',
  readonly          := sorry',
  mem_extends       := sorry',
  mem_inject        := sorry',
  trace_length      := sorry',
  receptive         := sorry',
  determ            := sorry' }

/- ** Semantics of annotations. -/

inductive extcall_annot_sem (text : string) (targs : list typ) (ge : Senv) :
  list val → mem → list event → val → mem → Prop
| mk (vargs m args) : eventval.list_match ge args targs vargs →
  extcall_annot_sem vargs m [event.annot text args] Vundef m

lemma extcall_annot_ok (text targs) :
  extcall_properties (extcall_annot_sem text targs) ⟨targs, none, cc_default⟩ :=
{ well_typed        := sorry',
  symbols_preserved := sorry',
  valid_block       := sorry',
  max_perm          := sorry',
  readonly          := sorry',
  mem_extends       := sorry',
  mem_inject        := sorry',
  trace_length      := sorry',
  receptive         := sorry',
  determ            := sorry' }

inductive extcall_annot_val_sem (text : string) (targ : typ) (ge : Senv) :
  list val → mem → list event → val → mem → Prop
| mk (varg m arg) :
  eventval.matchv ge arg targ varg →
  extcall_annot_val_sem [varg] m [event.annot text [arg]] varg m

lemma extcall_annot_val_ok (text targ) :
  extcall_properties (extcall_annot_val_sem text targ) ⟨[targ], some targ, cc_default⟩ :=
{ well_typed        := sorry',
  symbols_preserved := sorry',
  valid_block       := sorry',
  max_perm          := sorry',
  readonly          := sorry',
  mem_extends       := sorry',
  mem_inject        := sorry',
  trace_length      := sorry',
  receptive         := sorry',
  determ            := sorry' }

inductive extcall_debug_sem (ge : Senv) :
  list val → mem → list event → val → mem → Prop
| mk (vargs m) : extcall_debug_sem vargs m [] Vundef m

lemma extcall_debug_ok (targs) :
  extcall_properties extcall_debug_sem ⟨targs, none, cc_default⟩ :=
{ well_typed        := sorry',
  symbols_preserved := sorry',
  valid_block       := sorry',
  max_perm          := sorry',
  readonly          := sorry',
  mem_extends       := sorry',
  mem_inject        := sorry',
  trace_length      := sorry',
  receptive         := sorry',
  determ            := sorry' }

/- ** Semantics of external functions. -/

/- For functions defined outside the program ([EF_external],
  [EF_builtin] and [EF_runtime]), we do not define their
  semantics, but only assume that it satisfies
  [extcall_properties]. -/

constant external_functions_sem : string → signature → extcall_sem

constant external_functions_properties {id sg} :
  extcall_properties (external_functions_sem id sg) sg

/- We treat inline assembly similarly. -/

constant inline_assembly_sem : string → signature → extcall_sem

constant inline_assembly_properties {id sg} :
  extcall_properties (inline_assembly_sem id sg) sg

/- ** Combined semantics of external calls -/

/- Combining the semantics given above for the various kinds of external calls,
  we define the predicate [external_call] that relates:
- the external function being invoked
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).

This predicate is used in the semantics of all CompCert languages. -/

noncomputable def external_call : external_function → extcall_sem
| (EF_external name sg)      := external_functions_sem name sg
| (EF_builtin name sg)       := external_functions_sem name sg
| (EF_runtime name sg)       := external_functions_sem name sg
| (EF_vload chunk)           := volatile_load_sem chunk
| (EF_vstore chunk)          := volatile_store_sem chunk
| EF_malloc                  := extcall_malloc_sem
| EF_free                    := extcall_free_sem
| (EF_memcpy sz al)          := extcall_memcpy_sem sz al
| (EF_annot txt targs)       := extcall_annot_sem txt targs
| (EF_annot_val txt targ)    := extcall_annot_val_sem txt targ
| (EF_inline_asm txt sg clb) := inline_assembly_sem txt sg
| (EF_debug kind txt targs)  := extcall_debug_sem

theorem external_call_spec (ef) :
  extcall_properties (external_call ef) (ef_sig ef) := sorry'

def external_call_well_typed        (ef) := (external_call_spec ef).well_typed
def external_call_symbols_preserved (ef) := (external_call_spec ef).symbols_preserved
def external_call_valid_block       (ef) := (external_call_spec ef).valid_block
def external_call_max_perm          (ef) := (external_call_spec ef).max_perm
def external_call_readonly          (ef) := (external_call_spec ef).readonly
def external_call_mem_extends       (ef) := (external_call_spec ef).mem_extends
def external_call_mem_inject_gen    (ef) := (external_call_spec ef).mem_inject
def external_call_trace_length      (ef) := (external_call_spec ef).trace_length
def external_call_receptive         (ef) := (external_call_spec ef).receptive
def external_call_determ            (ef) := (external_call_spec ef).determ

/- Corollary of [external_call_valid_block]. -/

lemma external_call_nextblock (ef ge vargs m1 t vres m2) :
  external_call ef ge vargs m1 t vres m2 →
  m1.nextblock ≤ m2.nextblock := sorry'

/- Special case of [external_call_mem_inject_gen] (for backward compatibility) -/

def meminj_preserves_globals {F V} (ge : Genv F V) (f : block → option (block × ℤ)) : Prop :=
     (∀ id b, Genv.find_symbol ge id = some b → f b = some (b, 0))
  ∧ (∀ b gv, Genv.find_var_info ge b = some gv → f b = some (b, 0))
  ∧ (∀ b1 b2 delta gv, Genv.find_var_info ge b2 = some gv → f b1 = some (b2, delta) → b2 = b1)

lemma external_call_mem_inject {ef F V} {ge : Genv F V} {vargs m1 t vres m2 f m1' vargs'} :
  meminj_preserves_globals ge f →
  external_call ef ge vargs m1 t vres m2 →
  inject f m1 m1' →
  list.forall2 (val.inject f) vargs vargs' →
  ∃ f' vres' m2',
     external_call ef ge vargs' m1' t vres' m2'
    ∧ inject f' vres vres'
    ∧ inject f' m2 m2'
    ∧ unchanged_on (loc_unmapped f) m1 m2
    ∧ unchanged_on (loc_out_of_reach f m1) m1' m2'
    ∧ inject_incr f f'
    ∧ inject_separated f f' m1 m1' := sorry'

/- Corollaries of [external_call_determ]. -/

lemma external_call_match_traces {ef ge vargs m t1 vres1 m1 t2 vres2 m2} :
  external_call ef ge vargs m t1 vres1 m1 →
  external_call ef ge vargs m t2 vres2 m2 →
  match_traces ge t1 t2 := sorry'

lemma external_call_deterministic {ef ge vargs m t vres1 m1 vres2 m2} :
  external_call ef ge vargs m t vres1 m1 →
  external_call ef ge vargs m t vres2 m2 →
  vres1 = vres2 ∧ m1 = m2 := sorry'

/- * Evaluation of builtin arguments -/

section eval_builtin_arg

parameters {A : Type} (ge : Senv) (e : A → val) (sp : val) (m : mem)

def eval_builtin_arg : builtin_arg A → option val
| (BA x) := some (e x)
| (BA_int n) := some (Vint n)
| (BA_long n) := some (Vlong n)
| (BA_float n) := some (Vfloat n)
| (BA_single n) := some (Vsingle n)
| (BA_loadstack chunk ofs) := loadv chunk m (offset_ptr sp ofs)
| (BA_addrstack ofs) := some (offset_ptr sp ofs)
| (BA_loadglobal chunk id ofs) := loadv chunk m (Senv.symbol_address ge id ofs)
| (BA_addrglobal id ofs) := some (Senv.symbol_address ge id ofs)
| (BA_splitlong hi lo) :=
  do vhi ← eval_builtin_arg hi,
     vlo ← eval_builtin_arg lo,
     return (long_of_words vhi vlo)

def eval_builtin_args (al : list (builtin_arg A)) : option (list val) :=
mmap eval_builtin_arg al

end eval_builtin_arg

/- Invariance by change of global environment. -/

section eval_builtin_arg_preserved

parameters {A F1 V1 F2 V2 : Type} {ge1 : Genv F1 V1} {ge2 : Genv F2 V2}
           (e : A → val) (sp : val) (m : mem)

parameter (symbols_preserved : ∀ id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id)

lemma eval_builtin_arg_preserved {a v} :
  eval_builtin_arg ge1 e sp m a = some v → eval_builtin_arg ge2 e sp m a = some v := sorry'

lemma eval_builtin_args_preserved {al vl} :
  eval_builtin_args ge1 e sp m al = some vl → eval_builtin_args ge2 e sp m al = some vl := sorry'

end eval_builtin_arg_preserved

/- Compatibility with the "is less defined than" relation. -/

section eval_builtin_arg_lessdef

parameters {A : Type} (ge : Senv) {e1 e2 : A → val} (sp : val) {m1 m2 : mem}

parameter env_lessdef : ∀ x, val.lessdef (e1 x) (e2 x)
parameter mem_extends : extends' m1 m2

lemma eval_builtin_arg_lessdef {a v1} :
  eval_builtin_arg ge e1 sp m1 a = some v1 →
  ∃ v2, eval_builtin_arg ge e2 sp m2 a = some v2 ∧ lessdef v1 v2 := sorry'

lemma eval_builtin_args_lessdef {al vl1} :
  eval_builtin_args ge e1 sp m1 al = some vl1 →
  ∃ vl2, eval_builtin_args ge e2 sp m2 al = some vl2 ∧ list.forall2 lessdef vl1 vl2 := sorry'

end eval_builtin_arg_lessdef

end events