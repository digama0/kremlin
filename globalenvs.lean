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

/- Global environments are a component of the dynamic semantics of
  all languages involved in the compiler.  A global environment
  maps symbol names (names of functions and of global variables)
  to the corresponding memory addresses.  It also maps memory addresses
  of functions to the corresponding function descriptions.

  Global environments, along with the initial memory state at the beginning
  of program execution, are built from the program of interest, as follows:
- A distinct memory address is assigned to each function of the program.
  These function addresses use negative numbers to distinguish them from
  addresses of memory blocks.  The associations of function name to function
  address and function address to function description are recorded in
  the global environment.
- For each global variable, a memory block is allocated and associated to
  the name of the variable.

  These operations reflect (at a high level of abstraction) what takes
  place during program linking and program loading in a real operating
  system. -/

Require Recdef
Require Import Zwf
Require Import Axioms Coqlib Errors Maps AST Linking
Require Import Integers Floats Values Memory

Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope

Local Open Scope pair_scope
Local Open Scope error_monad_scope

Set Implicit Arguments

/- Auxiliary function for initialization of global variables. -/

Function store_zeros (m : mem) (b : block) (p : ℤ) (n : ℤ) {wf (Zwf 0) n} : option mem :=
  if zle n 0 then some m else
    match Mem.store Mint8unsigned m b p Vzero with
    | some m' := store_zeros m' b (p + 1) (n - 1)
    | none := none
    end
Proof
  intros. red. omega
  apply Zwf_well_founded
Qed

/- To avoid useless definitions of inductors in extracted code. -/
Local Unset Elimination Schemes
Local Unset Case Analysis Schemes

/- * Symbol environments -/

/- Symbol environments are a restricted view of global environments,
  focusing on symbol names and their associated blocks.  They do not
  contain mappings from blocks to function or variable definitions. -/

Module Senv

structure t : Type := mksenv {
  /- Operations -/
  find_symbol : ident → option block;
  public_symbol : ident → bool;
  invert_symbol : block → option ident;
  block_is_volatile : block → bool;
  nextblock : block;
  /- Properties -/
  find_symbol_injective :
    ∀ id1 id2 b, find_symbol id1 = some b → find_symbol id2 = some b → id1 = id2;
  invert_find_symbol :
    ∀ id b, invert_symbol b = some id → find_symbol id = some b;
  find_invert_symbol :
    ∀ id b, find_symbol id = some b → invert_symbol b = some id;
  public_symbol_exists :
    ∀ id, public_symbol id = tt → ∃ b, find_symbol id = some b;
  find_symbol_below :
    ∀ id b, find_symbol id = some b → Plt b nextblock;
  block_is_volatile_below :
    ∀ b, block_is_volatile b = tt → Plt b nextblock
}

def symbol_address (ge : t) (id : ident) (ofs : ptrofs) : val :=
  match find_symbol ge id with
| some b := Vptr b ofs
| none := Vundef
  end

theorem shift_symbol_address :
  ∀ ge id ofs delta,
  symbol_address ge id (Ptrofs.add ofs delta) = Val.offset_ptr (symbol_address ge id ofs) delta
Proof
  intros. unfold symbol_address, Val.offset_ptr. destruct (find_symbol ge id); auto
Qed

theorem shift_symbol_address_32 :
  ∀ ge id ofs n,
  Archi.ptr64 = ff →
  symbol_address ge id (Ptrofs.add ofs (Ptrofs.of_int n)) = Val.add (symbol_address ge id ofs) (Vint n)
Proof
  intros. unfold symbol_address. destruct (find_symbol ge id)
- unfold Val.add. rewrite H. auto
- auto
Qed

theorem shift_symbol_address_64 :
  ∀ ge id ofs n,
  Archi.ptr64 = tt →
  symbol_address ge id (Ptrofs.add ofs (Ptrofs.of_int64 n)) = Val.addl (symbol_address ge id ofs) (Vlong n)
Proof
  intros. unfold symbol_address. destruct (find_symbol ge id)
- unfold Val.addl. rewrite H. auto
- auto
Qed

def equiv (se1 se2 : t) : Prop :=
     (∀ id, find_symbol se2 id = find_symbol se1 id)
  ∧ (∀ id, public_symbol se2 id = public_symbol se1 id)
  ∧ (∀ b, block_is_volatile se2 b = block_is_volatile se1 b)

end Senv

Module Genv

/- * Global environments -/

section GENV

parameter F : Type.  /- The type of function descriptions -/
parameter V : Type.  /- The type of information attached to variables -/

/- The type of global environments. -/

structure t : Type := mkgenv {
  genv_public : list ident;              /- which symbol names are public -/
  genv_symb : PTree.t block;             /- mapping symbol -> block -/
  genv_defs : PTree.t (globdef F V);     /- mapping block -> definition -/
  genv_next : block;                     /- next symbol pointer -/
  genv_symb_range : ∀ id b, PTree.get id genv_symb = some b → Plt b genv_next;
  genv_defs_range : ∀ b g, PTree.get b genv_defs = some g → Plt b genv_next;
  genv_vars_inj : ∀ id1 id2 b,
    PTree.get id1 genv_symb = some b → PTree.get id2 genv_symb = some b → id1 = id2
}

/- ** Lookup functions -/

/- [find_symbol ge id] returns the block associated with the given name, if any -/

def find_symbol (ge : t) (id : ident) : option block :=
  PTree.get id ge.(genv_symb)

/- [symbol_address ge id ofs] returns a pointer into the block associated
  with [id], at byte offset [ofs].  [Vundef] is returned if no block is associated
  to [id]. -/

def symbol_address (ge : t) (id : ident) (ofs : ptrofs) : val :=
  match find_symbol ge id with
| some b := Vptr b ofs
| none := Vundef
  end

/- [public_symbol ge id] says whether the name [id] is public and defined. -/

def public_symbol (ge : t) (id : ident) : bool :=
  match find_symbol ge id with
| none := ff
| some _ := In_dec ident_eq id ge.(genv_public)
  end

/- [find_def ge b] returns the global definition associated with the given address. -/

def find_def (ge : t) (b : block) : option (globdef F V) :=
  PTree.get b ge.(genv_defs)

/- [find_funct_ptr ge b] returns the function description associated with
    the given address. -/

def find_funct_ptr (ge : t) (b : block) : option F :=
  match find_def ge b with some (Gfun f) := some f | _ := none end

/- [find_funct] is similar to [find_funct_ptr], but the function address
    is given as a value, which must be a pointer with offset 0. -/

def find_funct (ge : t) (v : val) : option F :=
  match v with
| Vptr b ofs := if Ptrofs.eq_dec ofs Ptrofs.zero then find_funct_ptr ge b else none
| _ := none
  end

/- [invert_symbol ge b] returns the name associated with the given block, if any -/

def invert_symbol (ge : t) (b : block) : option ident :=
  PTree.fold
    (λ res id b' := if eq_block b b' then some id else res)
    ge.(genv_symb) none

/- [find_var_info ge b] returns the information attached to the variable
   at address [b]. -/

def find_var_info (ge : t) (b : block) : option (globvar V) :=
  match find_def ge b with some (Gvar v) := some v | _ := none end

/- [block_is_volatile ge b] returns [true] if [b] points to a global variable
  of volatile type, [false] otherwise. -/

def block_is_volatile (ge : t) (b : block) : bool :=
  match find_var_info ge b with
| none := ff
| some gv := gv.(gvar_volatile)
  end

/- ** Constructing the global environment -/

Program def add_global (ge : t) (idg : ident * globdef F V) : t :=
  @mkgenv
    ge.(genv_public)
    (PTree.set idg#1 ge.(genv_next) ge.(genv_symb))
    (PTree.set ge.(genv_next) idg#2 ge.(genv_defs))
    (Psucc ge.(genv_next))
    _ _ _
Next Obligation
  destruct ge; simpl in *
  rewrite PTree.gsspec in H. destruct (peq id i). inv H. apply Plt_succ
  apply Plt_trans_succ; eauto
Qed
Next Obligation
  destruct ge; simpl in *
  rewrite PTree.gsspec in H. destruct (peq b genv_next0)
  inv H. apply Plt_succ
  apply Plt_trans_succ; eauto
Qed
Next Obligation
  destruct ge; simpl in *
  rewrite PTree.gsspec in H. rewrite PTree.gsspec in H0
  destruct (peq id1 i); destruct (peq id2 i)
  congruence
  inv H. eelim Plt_strict. eapply genv_symb_range0; eauto
  inv H0. eelim Plt_strict. eapply genv_symb_range0; eauto
  eauto
Qed

def add_globals (ge : t) (gl : list (ident * globdef F V)) : t :=
  List.fold_left add_global gl ge

lemma add_globals_app :
  ∀ gl2 gl1 ge,
  add_globals ge (gl1 ++ gl2) = add_globals (add_globals ge gl1) gl2
Proof
  intros. apply fold_left_app. 
Qed

Program def empty_genv (pub : list ident) : t :=
  @mkgenv pub (PTree.empty _) (PTree.empty _) 1%positive _ _ _
Next Obligation
  rewrite PTree.gempty in H. discriminate
Qed
Next Obligation
  rewrite PTree.gempty in H. discriminate
Qed
Next Obligation
  rewrite PTree.gempty in H. discriminate
Qed

def globalenv (p : program F V) :=
  add_globals (empty_genv p.(prog_public)) p.(prog_defs)

/- Proof principles -/

section GLOBALENV_PRINCIPLES

parameter P : t → Prop

lemma add_globals_preserves :
  ∀ gl ge,
  (∀ ge id g, P ge → In (id, g) gl → P (add_global ge (id, g))) →
  P ge → P (add_globals ge gl)
Proof
  induction gl; simpl; intros
  auto
  destruct a. apply IHgl; auto
Qed

lemma add_globals_ensures :
  ∀ id g gl ge,
  (∀ ge id g, P ge → In (id, g) gl → P (add_global ge (id, g))) →
  (∀ ge, P (add_global ge (id, g))) →
  In (id, g) gl → P (add_globals ge gl)
Proof
  induction gl; simpl; intros
  contradiction
  destruct H1. subst a. apply add_globals_preserves; auto
  apply IHgl; auto
Qed

lemma add_globals_unique_preserves :
  ∀ id gl ge,
  (∀ ge id1 g, P ge → In (id1, g) gl → id1 ≠ id → P (add_global ge (id1, g))) →
  ~In id (map fst gl) → P ge → P (add_globals ge gl)
Proof
  induction gl; simpl; intros
  auto
  destruct a. apply IHgl; auto
Qed

lemma add_globals_unique_ensures :
  ∀ gl1 id g gl2 ge,
  (∀ ge id1 g1, P ge → In (id1, g1) gl2 → id1 ≠ id → P (add_global ge (id1, g1))) →
  (∀ ge, P (add_global ge (id, g))) →
  ~In id (map fst gl2) → P (add_globals ge (gl1 ++ (id, g) :: gl2))
Proof
  intros. rewrite add_globals_app. simpl. apply add_globals_unique_preserves with id; auto
Qed

theorem in_norepet_unique :
  ∀ id g (gl : list (ident * globdef F V)),
  In (id, g) gl → list_norepet (map fst gl) →
  ∃ gl1 gl2, gl = gl1 ++ (id, g) :: gl2 ∧ ~In id (map fst gl2)
Proof
  induction gl as [|[id1 g1] gl]; simpl; intros
  contradiction
  inv H0. destruct H
  inv H. ∃ nil, gl. auto
  exploit IHgl; eauto. intros (gl1 & gl2 & X & Y)
  ∃ ((id1, g1) :: gl1), gl2; split; auto. rewrite X; auto
Qed

lemma add_globals_norepet_ensures :
  ∀ id g gl ge,
  (∀ ge id1 g1, P ge → In (id1, g1) gl → id1 ≠ id → P (add_global ge (id1, g1))) →
  (∀ ge, P (add_global ge (id, g))) →
  In (id, g) gl → list_norepet (map fst gl) → P (add_globals ge gl)
Proof
  intros. exploit in_norepet_unique; eauto. intros (gl1 & gl2 & X & Y)
  subst gl. apply add_globals_unique_ensures; auto. intros. eapply H; eauto
  apply in_or_app; simpl; auto
Qed

end GLOBALENV_PRINCIPLES

/- ** Properties of the operations over global environments -/

theorem public_symbol_exists :
  ∀ ge id, public_symbol ge id = tt → ∃ b, find_symbol ge id = some b
Proof
  unfold public_symbol; intros. destruct (find_symbol ge id) as [b|]
  ∃ b; auto
  discriminate
Qed

theorem shift_symbol_address :
  ∀ ge id ofs delta,
  symbol_address ge id (Ptrofs.add ofs delta) = Val.offset_ptr (symbol_address ge id ofs) delta
Proof
  intros. unfold symbol_address, Val.offset_ptr. destruct (find_symbol ge id); auto
Qed

theorem shift_symbol_address_32 :
  ∀ ge id ofs n,
  Archi.ptr64 = ff →
  symbol_address ge id (Ptrofs.add ofs (Ptrofs.of_int n)) = Val.add (symbol_address ge id ofs) (Vint n)
Proof
  intros. unfold symbol_address. destruct (find_symbol ge id)
- unfold Val.add. rewrite H. auto
- auto
Qed

theorem shift_symbol_address_64 :
  ∀ ge id ofs n,
  Archi.ptr64 = tt →
  symbol_address ge id (Ptrofs.add ofs (Ptrofs.of_int64 n)) = Val.addl (symbol_address ge id ofs) (Vlong n)
Proof
  intros. unfold symbol_address. destruct (find_symbol ge id)
- unfold Val.addl. rewrite H. auto
- auto
Qed

theorem find_funct_inv :
  ∀ ge v f,
  find_funct ge v = some f → ∃ b, v = Vptr b Ptrofs.zero
Proof
  intros until f; unfold find_funct
  destruct v; try congruence
  destruct (Ptrofs.eq_dec i Ptrofs.zero); try congruence
  intros. ∃ b; congruence
Qed

theorem find_funct_find_funct_ptr :
  ∀ ge b,
  find_funct ge (Vptr b Ptrofs.zero) = find_funct_ptr ge b
Proof
  intros; simpl. apply dec_eq_true
Qed

theorem find_funct_ptr_iff :
  ∀ ge b f, find_funct_ptr ge b = some f ↔ find_def ge b = some (Gfun f)
Proof
  intros. unfold find_funct_ptr. destruct (find_def ge b) as [[f1|v1]|]; intuition congruence
Qed

theorem find_var_info_iff :
  ∀ ge b v, find_var_info ge b = some v ↔ find_def ge b = some (Gvar v)
Proof
  intros. unfold find_var_info. destruct (find_def ge b) as [[f1|v1]|]; intuition congruence
Qed

theorem find_def_symbol :
  ∀ p id g,
  (prog_defmap p)!id = some g ↔ ∃ b, find_symbol (globalenv p) id = some b ∧ find_def (globalenv p) b = some g
Proof
  intros
  set (P := λ m ge := m!id = some g ↔ ∃ b, find_symbol ge id = some b ∧ find_def ge b = some g)
  assert (REC : ∀ l m ge,
            P m ge →
            P (fold_left (λ m idg := PTree.set idg#1 idg#2 m) l m)
              (add_globals ge l))
  { induction l as [ | [id1 g1] l]; intros; simpl
  - auto
  - apply IHl. unfold P, add_global, find_symbol, find_def; simpl
    rewrite ! PTree.gsspec. destruct (peq id id1). 
    + subst id1. split; intros
      inv H0. ∃ (genv_next ge); split; auto. apply PTree.gss
      destruct H0 as (b & A & B). inv A. rewrite PTree.gss in B. auto
    + red in H; rewrite H. split
      intros (b & A & B). ∃ b; split; auto. rewrite PTree.gso; auto. 
      apply Plt_ne. eapply genv_symb_range; eauto. 
      intros (b & A & B). rewrite PTree.gso in B. ∃ b; auto. 
      apply Plt_ne. eapply genv_symb_range; eauto. 
  }
  apply REC. unfold P, find_symbol, find_def; simpl. 
  rewrite ! PTree.gempty. split
  congruence
  intros (b & A & B); congruence
Qed

theorem find_symbol_exists :
  ∀ p id g,
  In (id, g) (prog_defs p) →
  ∃ b, find_symbol (globalenv p) id = some b
Proof
  intros. unfold globalenv. eapply add_globals_ensures; eauto
/- preserves -/
  intros. unfold find_symbol; simpl. rewrite PTree.gsspec. destruct (peq id id0)
  econstructor; eauto
  auto
/- ensures -/
  intros. unfold find_symbol; simpl. rewrite PTree.gss. econstructor; eauto
Qed

theorem find_symbol_inversion : ∀ p x b,
  find_symbol (globalenv p) x = some b →
  In x (prog_defs_names p)
Proof
  intros until b; unfold globalenv. eapply add_globals_preserves
/- preserves -/
  unfold find_symbol; simpl; intros. rewrite PTree.gsspec in H1
  destruct (peq x id). subst x. change id with (fst (id, g)). apply List.in_map; auto
  auto
/- base -/
  unfold find_symbol; simpl; intros. rewrite PTree.gempty in H. discriminate
Qed

theorem find_def_inversion :
  ∀ p b g,
  find_def (globalenv p) b = some g →
  ∃ id, In (id, g) (prog_defs p)
Proof
  intros until g. unfold globalenv. apply add_globals_preserves
/- preserves -/
  unfold find_def; simpl; intros
  rewrite PTree.gsspec in H1. destruct (peq b (genv_next ge))
  inv H1. ∃ id; auto
  auto
/- base -/
  unfold find_def; simpl; intros. rewrite PTree.gempty in H. discriminate
Qed

Corollary find_funct_ptr_inversion :
  ∀ p b f,
  find_funct_ptr (globalenv p) b = some f →
  ∃ id, In (id, Gfun f) (prog_defs p)
Proof
  intros. apply find_def_inversion with b. apply find_funct_ptr_iff; auto
Qed

Corollary find_funct_inversion :
  ∀ p v f,
  find_funct (globalenv p) v = some f →
  ∃ id, In (id, Gfun f) (prog_defs p)
Proof
  intros. exploit find_funct_inv; eauto. intros [b EQ]. subst v
  rewrite find_funct_find_funct_ptr in H
  eapply find_funct_ptr_inversion; eauto
Qed

theorem find_funct_ptr_prop :
  ∀ (P : F → Prop) p b f,
  (∀ id f, In (id, Gfun f) (prog_defs p) → P f) →
  find_funct_ptr (globalenv p) b = some f →
  P f
Proof
  intros. exploit find_funct_ptr_inversion; eauto. intros [id IN]. eauto
Qed

theorem find_funct_prop :
  ∀ (P : F → Prop) p v f,
  (∀ id f, In (id, Gfun f) (prog_defs p) → P f) →
  find_funct (globalenv p) v = some f →
  P f
Proof
  intros. exploit find_funct_inversion; eauto. intros [id IN]. eauto
Qed

theorem global_addresses_distinct :
  ∀ ge id1 id2 b1 b2,
  id1 ≠ id2 →
  find_symbol ge id1 = some b1 →
  find_symbol ge id2 = some b2 →
  b1 ≠ b2
Proof
  intros. red; intros; subst. elim H. destruct ge. eauto
Qed

theorem invert_find_symbol :
  ∀ ge id b,
  invert_symbol ge b = some id → find_symbol ge id = some b
Proof
  intros until b; unfold find_symbol, invert_symbol
  apply PTree_Properties.fold_rec
  intros. rewrite H in H0; auto
  congruence
  intros. destruct (eq_block b v). inv H2. apply PTree.gss
  rewrite PTree.gsspec. destruct (peq id k)
  subst. assert (m!k = some b) by auto. congruence
  auto
Qed

theorem find_invert_symbol :
  ∀ ge id b,
  find_symbol ge id = some b → invert_symbol ge b = some id
Proof
  intros until b
  assert (find_symbol ge id = some b → ∃ id', invert_symbol ge b = some id')
  unfold find_symbol, invert_symbol
  apply PTree_Properties.fold_rec
  intros. rewrite H in H0; auto
  rewrite PTree.gempty; congruence
  intros. destruct (eq_block b v). ∃ k; auto
  rewrite PTree.gsspec in H2. destruct (peq id k)
  inv H2. congruence. auto

  intros; exploit H; eauto. intros [id' A]
  assert (id = id'). eapply genv_vars_inj; eauto. apply invert_find_symbol; auto
  congruence
Qed

def advance_next (gl : list (ident * globdef F V)) (x : positive) :=
  List.fold_left (λ n g := Psucc n) gl x

theorem genv_next_add_globals :
  ∀ gl ge,
  genv_next (add_globals ge gl) = advance_next gl (genv_next ge)
Proof
  induction gl; simpl; intros
  auto
  rewrite IHgl. auto
Qed

theorem genv_public_add_globals :
  ∀ gl ge,
  genv_public (add_globals ge gl) = genv_public ge
Proof
  induction gl; simpl; intros
  auto
  rewrite IHgl; auto
Qed

theorem globalenv_public :
  ∀ p, genv_public (globalenv p) = prog_public p
Proof
  unfold globalenv; intros. rewrite genv_public_add_globals. auto
Qed

theorem block_is_volatile_below :
  ∀ ge b, block_is_volatile ge b = tt →  Plt b ge.(genv_next)
Proof
  unfold block_is_volatile; intros. destruct (find_var_info ge b) as [gv|] eqn:FV
  rewrite find_var_info_iff in FV. eapply genv_defs_range; eauto
  discriminate
Qed

/- ** Coercing a global environment into a symbol environment -/

def to_senv (ge : t) : Senv.t :=
 @Senv.mksenv
    (find_symbol ge)
    (public_symbol ge)
    (invert_symbol ge)
    (block_is_volatile ge)
    ge.(genv_next)
    ge.(genv_vars_inj)
    (invert_find_symbol ge)
    (find_invert_symbol ge)
    (public_symbol_exists ge)
    ge.(genv_symb_range)
    (block_is_volatile_below ge)

/- * Construction of the initial memory state -/

section INITMEM

parameter ge : t

def store_init_data (m : mem) (b : block) (p : ℤ) (id : init_data) : option mem :=
  match id with
| Init_int8 n := Mem.store Mint8unsigned m b p (Vint n)
| Init_int16 n := Mem.store Mint16unsigned m b p (Vint n)
| Init_int32 n := Mem.store Mint32 m b p (Vint n)
| Init_int64 n := Mem.store Mint64 m b p (Vlong n)
| Init_float32 n := Mem.store Mfloat32 m b p (Vsingle n)
| Init_float64 n := Mem.store Mfloat64 m b p (Vfloat n)
| Init_addrof symb ofs :=
      match find_symbol ge symb with
      | none := none
      | some b' := Mem.store Mptr m b p (Vptr b' ofs)
      end
| Init_space n := some m
  end

def store_init_data_list (m : mem) (b : block) (p : ℤ) (idl : list init_data)
                              {struct idl} : option mem :=
  match idl with
| nil := some m
| id :: idl' :=
      match store_init_data m b p id with
      | none := none
      | some m' := store_init_data_list m' b (p + init_data_size id) idl'
      end
  end

def perm_globvar (gv : globvar V) : permission :=
  if gv.(gvar_volatile) then Nonempty
  else if gv.(gvar_readonly) then Readable
  else Writable

def alloc_global (m : mem) (idg : ident * globdef F V) : option mem :=
  match idg with
| (id, Gfun f) :=
      let (m1, b) := Mem.alloc m 0 1 in
      Mem.drop_perm m1 b 0 1 Nonempty
| (id, Gvar v) :=
      let init := v.(gvar_init) in
      let sz := init_data_list_size init in
      let (m1, b) := Mem.alloc m 0 sz in
      match store_zeros m1 b 0 sz with
      | none := none
      | some m2 :=
          match store_init_data_list m2 b 0 init with
          | none := none
          | some m3 := Mem.drop_perm m3 b 0 sz (perm_globvar v)
          end
      end
  end

def alloc_globals (m : mem) (gl : list (ident * globdef F V))
                       {struct gl} : option mem :=
  match gl with
| nil := some m
| g :: gl' :=
      match alloc_global m g with
      | none := none
      | some m' := alloc_globals m' gl'
      end
  end

lemma alloc_globals_app : ∀ gl1 gl2 m m1,
  alloc_globals m gl1 = some m1 →
  alloc_globals m1 gl2 = alloc_globals m (gl1 ++ gl2)
Proof
  induction gl1
  simpl. intros.  inversion H; subst. auto
  simpl. intros. destruct (alloc_global m a); eauto. inversion H
Qed

/- Next-block properties -/

theorem store_zeros_nextblock :
  ∀ m b p n m', store_zeros m b p n = some m' → Mem.nextblock m' = Mem.nextblock m
Proof
  intros until n. functional induction (store_zeros m b p n); intros
  inv H; auto
  rewrite IHo; eauto with mem
  congruence
Qed

theorem store_init_data_list_nextblock :
  ∀ idl b m p m',
  store_init_data_list m b p idl = some m' →
  Mem.nextblock m' = Mem.nextblock m
Proof
  induction idl; simpl; intros until m'
  intros. congruence
  caseEq (store_init_data m b p a); try congruence. intros
  transitivity (Mem.nextblock m0). eauto
  destruct a; simpl in H; try (eapply Mem.nextblock_store; eauto; fail)
  congruence
  destruct (find_symbol ge i); try congruence. eapply Mem.nextblock_store; eauto
Qed

theorem alloc_global_nextblock :
  ∀ g m m',
  alloc_global m g = some m' →
  Mem.nextblock m' = Psucc(Mem.nextblock m)
Proof
  unfold alloc_global. intros
  destruct g as [id [f|v]]
  /- function -/
  destruct (Mem.alloc m 0 1) as [m1 b] eqn:?
  erewrite Mem.nextblock_drop; eauto. erewrite Mem.nextblock_alloc; eauto
  /- variable -/
  set (init := gvar_init v) in *
  set (sz := init_data_list_size init) in *
  destruct (Mem.alloc m 0 sz) as [m1 b] eqn:?
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate
  destruct (store_init_data_list m2 b 0 init) as [m3|] eqn:?; try discriminate
  erewrite Mem.nextblock_drop; eauto
  erewrite store_init_data_list_nextblock; eauto
  erewrite store_zeros_nextblock; eauto
  erewrite Mem.nextblock_alloc; eauto
Qed

theorem alloc_globals_nextblock :
  ∀ gl m m',
  alloc_globals m gl = some m' →
  Mem.nextblock m' = advance_next gl (Mem.nextblock m)
Proof
  induction gl; simpl; intros
  congruence
  destruct (alloc_global m a) as [m1|] eqn:?; try discriminate
  erewrite IHgl; eauto. erewrite alloc_global_nextblock; eauto
Qed

/- Permissions -/

theorem store_zeros_perm :
  ∀ k prm b' q m b p n m',
  store_zeros m b p n = some m' →
  (Mem.perm m b' q k prm ↔ Mem.perm m' b' q k prm)
Proof
  intros until n. functional induction (store_zeros m b p n); intros
  inv H; tauto
  destruct (IHo _ H); intros. split; eauto with mem
  congruence
Qed

theorem store_init_data_perm :
  ∀ k prm b' q i b m p m',
  store_init_data m b p i = some m' →
  (Mem.perm m b' q k prm ↔ Mem.perm m' b' q k prm)
Proof
  intros. 
  assert (∀ chunk v,
          Mem.store chunk m b p v = some m' →
          (Mem.perm m b' q k prm ↔ Mem.perm m' b' q k prm))
    intros; split; eauto with mem
  destruct i; simpl in H; eauto. 
  inv H; tauto
  destruct (find_symbol ge i); try discriminate. eauto
Qed

theorem store_init_data_list_perm :
  ∀ k prm b' q idl b m p m',
  store_init_data_list m b p idl = some m' →
  (Mem.perm m b' q k prm ↔ Mem.perm m' b' q k prm)
Proof
  induction idl as [ | i1 idl]; simpl; intros
- inv H; tauto
- destruct (store_init_data m b p i1) as [m1|] eqn:S1; try discriminate
  transitivity (Mem.perm m1 b' q k prm). 
  eapply store_init_data_perm; eauto
  eapply IHidl; eauto
Qed

theorem alloc_global_perm :
  ∀ k prm b' q idg m m',
  alloc_global m idg = some m' →
  Mem.valid_block m b' →
  (Mem.perm m b' q k prm ↔ Mem.perm m' b' q k prm)
Proof
  intros. destruct idg as [id [f|v]]; simpl in H
  /- function -/
  destruct (Mem.alloc m 0 1) as [m1 b] eqn:?
  assert (b' ≠ b). apply Mem.valid_not_valid_diff with m; eauto with mem
  split; intros
  eapply Mem.perm_drop_3; eauto. eapply Mem.perm_alloc_1; eauto
  eapply Mem.perm_alloc_4; eauto. eapply Mem.perm_drop_4; eauto
  /- variable -/
  set (init := gvar_init v) in *
  set (sz := init_data_list_size init) in *
  destruct (Mem.alloc m 0 sz) as [m1 b] eqn:?
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate
  destruct (store_init_data_list m2 b 0 init) as [m3|] eqn:?; try discriminate
  assert (b' ≠ b). apply Mem.valid_not_valid_diff with m; eauto with mem
  split; intros
  eapply Mem.perm_drop_3; eauto
  erewrite <- store_init_data_list_perm; [idtac|eauto]
  erewrite <- store_zeros_perm; [idtac|eauto]
  eapply Mem.perm_alloc_1; eauto
  eapply Mem.perm_alloc_4; eauto
  erewrite store_zeros_perm; [idtac|eauto]
  erewrite store_init_data_list_perm; [idtac|eauto]
  eapply Mem.perm_drop_4; eauto
Qed

theorem alloc_globals_perm :
  ∀ k prm b' q gl m m',
  alloc_globals m gl = some m' →
  Mem.valid_block m b' →
  (Mem.perm m b' q k prm ↔ Mem.perm m' b' q k prm)
Proof
  induction gl
  simpl; intros. inv H. tauto
  simpl; intros. destruct (alloc_global m a) as [m1|] eqn:?; try discriminate
  erewrite alloc_global_perm; eauto. eapply IHgl; eauto
  unfold Mem.valid_block in *. erewrite alloc_global_nextblock; eauto
  apply Plt_trans_succ; auto
Qed

/- Data preservation properties -/

theorem store_zeros_unchanged :
  ∀ (P : block → ℤ → Prop) m b p n m',
  store_zeros m b p n = some m' →
  (∀ i, p <= i < p + n → ~ P b i) →
  Mem.unchanged_on P m m'
Proof
  intros until n. functional induction (store_zeros m b p n); intros
- inv H; apply Mem.unchanged_on_refl
- apply Mem.unchanged_on_trans with m'
+ eapply Mem.store_unchanged_on; eauto. simpl. intros. apply H0. omega. 
+ apply IHo; auto. intros; apply H0; omega. 
- discriminate
Qed

theorem store_init_data_unchanged :
  ∀ (P : block → ℤ → Prop) b i m p m',
  store_init_data m b p i = some m' →
  (∀ ofs, p <= ofs < p + init_data_size i → ~ P b ofs) →
  Mem.unchanged_on P m m'
Proof
  intros. destruct i; simpl in *;
  try (eapply Mem.store_unchanged_on; eauto; fail)
  inv H; apply Mem.unchanged_on_refl
  destruct (find_symbol ge i); try congruence
  eapply Mem.store_unchanged_on; eauto;
  unfold Mptr; destruct Archi.ptr64; eauto
Qed

theorem store_init_data_list_unchanged :
  ∀ (P : block → ℤ → Prop) b il m p m',
  store_init_data_list m b p il = some m' →
  (∀ ofs, p <= ofs → ~ P b ofs) →
  Mem.unchanged_on P m m'
Proof
  induction il; simpl; intros
- inv H. apply Mem.unchanged_on_refl
- destruct (store_init_data m b p a) as [m1|] eqn:?; try congruence
  apply Mem.unchanged_on_trans with m1
  eapply store_init_data_unchanged; eauto. intros; apply H0; tauto. 
  eapply IHil; eauto. intros; apply H0. generalize (init_data_size_pos a); omega
Qed

/- Properties related to [loadbytes] -/

def readbytes_as_zero (m : mem) (b : block) (ofs len : ℤ) : Prop :=
  ∀ p n,
  ofs <= p → p + ℤ.of_nat n <= ofs + len →
  Mem.loadbytes m b p (ℤ.of_nat n) = some (list_repeat n (Byte Byte.zero))

lemma store_zeros_loadbytes :
  ∀ m b p n m',
  store_zeros m b p n = some m' →
  readbytes_as_zero m' b p n
Proof
  intros until n; functional induction (store_zeros m b p n); red; intros
- destruct n0. simpl. apply Mem.loadbytes_empty. omega
  rewrite inj_S in H1. omegaContradiction
- destruct (zeq p0 p)
  + subst p0. destruct n0. simpl. apply Mem.loadbytes_empty. omega
    rewrite inj_S in H1. rewrite inj_S
    replace (ℤ.succ (ℤ.of_nat n0)) with (1 + ℤ.of_nat n0) by omega
    change (list_repeat (S n0) (Byte Byte.zero))
      with ((Byte Byte.zero :: nil) ++ list_repeat n0 (Byte Byte.zero))
    apply Mem.loadbytes_concat
    eapply Mem.loadbytes_unchanged_on with (P := λ b1 ofs1 := ofs1 = p)
    eapply store_zeros_unchanged; eauto. intros; omega
    intros; omega
    replace (Byte Byte.zero :: nil) with (encode_val Mint8unsigned Vzero)
    change 1 with (size_chunk Mint8unsigned)
    eapply Mem.loadbytes_store_same; eauto
    unfold encode_val; unfold encode_int; unfold rev_if_be; destruct Archi.big_endian; reflexivity
    eapply IHo; eauto. omega. omega. omega. omega
  + eapply IHo; eauto. omega. omega
- discriminate
Qed

def bytes_of_init_data (i : init_data) : list memval :=
  match i with
| Init_int8 n := inj_bytes (encode_int 1%ℕ (Int.unsigned n))
| Init_int16 n := inj_bytes (encode_int 2%ℕ (Int.unsigned n))
| Init_int32 n := inj_bytes (encode_int 4%ℕ (Int.unsigned n))
| Init_int64 n := inj_bytes (encode_int 8%ℕ (Int64.unsigned n))
| Init_float32 n := inj_bytes (encode_int 4%ℕ (Int.unsigned (Float32.to_bits n)))
| Init_float64 n := inj_bytes (encode_int 8%ℕ (Int64.unsigned (Float.to_bits n)))
| Init_space n := list_repeat (ℤ.to_nat n) (Byte Byte.zero)
| Init_addrof id ofs :=
      match find_symbol ge id with
      | some b := inj_value (if Archi.ptr64 then Q64 else Q32) (Vptr b ofs)
      | none   := list_repeat (if Archi.ptr64 then 8%ℕ else 4%ℕ) Undef
      end
  end

theorem init_data_size_addrof :
  ∀ id ofs, init_data_size (Init_addrof id ofs) = size_chunk Mptr
Proof
  intros. unfold Mptr. simpl. destruct Archi.ptr64; auto
Qed

lemma store_init_data_loadbytes :
  ∀ m b p i m',
  store_init_data m b p i = some m' →
  readbytes_as_zero m b p (init_data_size i) →
  Mem.loadbytes m' b p (init_data_size i) = some (bytes_of_init_data i)
Proof
  intros; destruct i; simpl in H; try apply (Mem.loadbytes_store_same _ _ _ _ _ _ H)
- inv H. simpl
  assert (EQ : ℤ.of_nat (ℤ.to_nat z) = ℤ.max z 0)
  { destruct (zle 0 z). rewrite Z2Nat.id; xomega. destruct z; try discriminate. simpl. xomega. } 
  rewrite <- EQ. apply H0. omega. simpl. omega. 
- rewrite init_data_size_addrof. simpl
  destruct (find_symbol ge i) as [b'|]; try discriminate
  rewrite (Mem.loadbytes_store_same _ _ _ _ _ _ H)
  unfold encode_val, Mptr; destruct Archi.ptr64; reflexivity
Qed

def bytes_of_init_data_list (il : list init_data) : list memval :=
  match il with
| nil := nil
| i :: il := bytes_of_init_data i ++ bytes_of_init_data_list il
  end

lemma store_init_data_list_loadbytes :
  ∀ b il m p m',
  store_init_data_list m b p il = some m' →
  readbytes_as_zero m b p (init_data_list_size il) →
  Mem.loadbytes m' b p (init_data_list_size il) = some (bytes_of_init_data_list il)
Proof
  induction il as [ | i1 il]; simpl; intros
- apply Mem.loadbytes_empty. omega
- generalize (init_data_size_pos i1) (init_data_list_size_pos il); intros P1 PL
  destruct (store_init_data m b p i1) as [m1|] eqn:S; try discriminate
  apply Mem.loadbytes_concat
  eapply Mem.loadbytes_unchanged_on with (P := λ b1 ofs1 := ofs1 < p + init_data_size i1)
  eapply store_init_data_list_unchanged; eauto
  intros; omega
  intros; omega
  eapply store_init_data_loadbytes; eauto. 
  red; intros; apply H0. omega. omega
  apply IHil with m1; auto
  red; intros. 
  eapply Mem.loadbytes_unchanged_on with (P := λ b1 ofs1 := p + init_data_size i1 <= ofs1)
  eapply store_init_data_unchanged; eauto. 
  intros; omega
  intros; omega. 
  apply H0. omega. omega
  auto. auto
Qed

/- Properties related to [load] -/

def read_as_zero (m : mem) (b : block) (ofs len : ℤ) : Prop :=
  ∀ chunk p,
  ofs <= p → p + size_chunk chunk <= ofs + len →
  (align_chunk chunk | p) →
  Mem.load chunk m b p =
  some (match chunk with
        | Mint8unsigned | Mint8signed | Mint16unsigned | Mint16signed | Mint32 := Vint Int.zero
        | Mint64 := Vlong Int64.zero
        | Mfloat32 := Vsingle Float32.zero
        | Mfloat64 := Vfloat Float.zero
        | Many32 | Many64 := Vundef
        end)

theorem read_as_zero_unchanged :
  ∀ (P : block → ℤ → Prop) m b ofs len m',
  read_as_zero m b ofs len →
  Mem.unchanged_on P m m' →
  (∀ i, ofs <= i < ofs + len → P b i) →
  read_as_zero m' b ofs len
Proof
  intros; red; intros. eapply Mem.load_unchanged_on; eauto. 
  intros; apply H1. omega. 
Qed. 

lemma store_zeros_read_as_zero :
  ∀ m b p n m',
  store_zeros m b p n = some m' →
  read_as_zero m' b p n
Proof
  intros; red; intros
  transitivity (some(decode_val chunk (list_repeat (size_chunk_nat chunk) (Byte Byte.zero))))
  apply Mem.loadbytes_load; auto. rewrite size_chunk_conv
  eapply store_zeros_loadbytes; eauto. rewrite <- size_chunk_conv; auto
  f_equal. destruct chunk; unfold decode_val; unfold decode_int; unfold rev_if_be; destruct Archi.big_endian; reflexivity
Qed

def load_store_init_data (m : mem) (b : block) (p : ℤ) (il : list init_data) {struct il} : Prop :=
  match il with
| nil := true
| Init_int8 n :: il' :=
      Mem.load Mint8unsigned m b p = some(Vint(Int.zero_ext 8 n))
      ∧ load_store_init_data m b (p + 1) il'
| Init_int16 n :: il' :=
      Mem.load Mint16unsigned m b p = some(Vint(Int.zero_ext 16 n))
      ∧ load_store_init_data m b (p + 2) il'
| Init_int32 n :: il' :=
      Mem.load Mint32 m b p = some(Vint n)
      ∧ load_store_init_data m b (p + 4) il'
| Init_int64 n :: il' :=
      Mem.load Mint64 m b p = some(Vlong n)
      ∧ load_store_init_data m b (p + 8) il'
| Init_float32 n :: il' :=
      Mem.load Mfloat32 m b p = some(Vsingle n)
      ∧ load_store_init_data m b (p + 4) il'
| Init_float64 n :: il' :=
      Mem.load Mfloat64 m b p = some(Vfloat n)
      ∧ load_store_init_data m b (p + 8) il'
| Init_addrof symb ofs :: il' :=
      (∃ b', find_symbol ge symb = some b' ∧ Mem.load Mptr m b p = some(Vptr b' ofs))
      ∧ load_store_init_data m b (p + size_chunk Mptr) il'
| Init_space n :: il' :=
      read_as_zero m b p n
      ∧ load_store_init_data m b (p + Zmax n 0) il'
  end

lemma store_init_data_list_charact :
  ∀ b il m p m',
  store_init_data_list m b p il = some m' →
  read_as_zero m b p (init_data_list_size il) →
  load_store_init_data m' b p il
Proof
  assert (A : ∀ chunk v m b p m1 il m',
    Mem.store chunk m b p v = some m1 →
    store_init_data_list m1 b (p + size_chunk chunk) il = some m' →
    Mem.load chunk m' b p = some(Val.load_result chunk v))
  {
    intros
    eapply Mem.load_unchanged_on with (P := λ b' ofs' := ofs' < p + size_chunk chunk)
    eapply store_init_data_list_unchanged; eauto. intros; omega
    intros; tauto
    eapply Mem.load_store_same; eauto
  }
  induction il; simpl
- auto
- intros. destruct (store_init_data m b p a) as [m1|] eqn:?; try congruence
  exploit IHil; eauto
  set (P := λ (b' : block) ofs' := p + init_data_size a <= ofs')
  apply read_as_zero_unchanged with (m := m) (P := P)
  red; intros; apply H0; auto. generalize (init_data_size_pos a); omega. omega. 
  eapply store_init_data_unchanged with (P := P); eauto
  intros; unfold P. omega
  intros; unfold P. omega
  intro D
  destruct a; simpl in Heqo
+ split; auto. eapply (A Mint8unsigned (Vint i)); eauto
+ split; auto. eapply (A Mint16unsigned (Vint i)); eauto
+ split; auto. eapply (A Mint32 (Vint i)); eauto
+ split; auto. eapply (A Mint64 (Vlong i)); eauto
+ split; auto. eapply (A Mfloat32 (Vsingle f)); eauto
+ split; auto. eapply (A Mfloat64 (Vfloat f)); eauto
+ split; auto
  set (P := λ (b' : block) ofs' := ofs' < p + init_data_size (Init_space z))
  inv Heqo. apply read_as_zero_unchanged with (m := m1) (P := P)
  red; intros. apply H0; auto. simpl. generalize (init_data_list_size_pos il); xomega
  eapply store_init_data_list_unchanged; eauto. 
  intros; unfold P. omega
  intros; unfold P. simpl; xomega
+ rewrite init_data_size_addrof in *
  split; auto
  destruct (find_symbol ge i); try congruence
  ∃ b0; split; auto
  transitivity (some (Val.load_result Mptr (Vptr b0 i0)))
  eapply (A Mptr (Vptr b0 i0)); eauto
  unfold Val.load_result, Mptr; destruct Archi.ptr64; auto
Qed

theorem alloc_global_unchanged :
  ∀ (P : block → ℤ → Prop) m id g m',
  alloc_global m (id, g) = some m' →
  Mem.unchanged_on P m m'
Proof
  intros. destruct g as [f|v]; simpl in H
- /- function -/
  destruct (Mem.alloc m 0 1) as [m1 b] eqn:?
  set (Q := λ b' (ofs : ℤ) := b' ≠ b)
  apply Mem.unchanged_on_implies with Q
  apply Mem.unchanged_on_trans with m1
  eapply Mem.alloc_unchanged_on; eauto
  eapply Mem.drop_perm_unchanged_on; eauto. 
  intros; red. apply Mem.valid_not_valid_diff with m; eauto with mem
- /- variable -/
  set (init := gvar_init v) in *
  set (sz := init_data_list_size init) in *
  destruct (Mem.alloc m 0 sz) as [m1 b] eqn:?
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate
  destruct (store_init_data_list m2 b 0 init) as [m3|] eqn:?; try discriminate
  set (Q := λ b' (ofs : ℤ) := b' ≠ b)
  apply Mem.unchanged_on_implies with Q
  apply Mem.unchanged_on_trans with m1
  eapply Mem.alloc_unchanged_on; eauto
  apply Mem.unchanged_on_trans with m2
  eapply store_zeros_unchanged; eauto
  apply Mem.unchanged_on_trans with m3
  eapply store_init_data_list_unchanged; eauto. 
  eapply Mem.drop_perm_unchanged_on; eauto. 
  intros; red. apply Mem.valid_not_valid_diff with m; eauto with mem
Qed

theorem alloc_globals_unchanged :
  ∀ (P : block → ℤ → Prop) gl m m',
  alloc_globals m gl = some m' →
  Mem.unchanged_on P m m'
Proof
  induction gl; simpl; intros
- inv H. apply Mem.unchanged_on_refl
- destruct (alloc_global m a) as [m''|] eqn:?; try discriminate
  destruct a as [id g]
  apply Mem.unchanged_on_trans with m''. 
  eapply alloc_global_unchanged; eauto
  apply IHgl; auto
Qed

theorem load_store_init_data_invariant :
  ∀ m m' b,
  (∀ chunk ofs, Mem.load chunk m' b ofs = Mem.load chunk m b ofs) →
  ∀ il p,
  load_store_init_data m b p il → load_store_init_data m' b p il
Proof
  induction il; intro p; simpl
  auto
  rewrite ! H. destruct a; intuition. red; intros; rewrite H; auto
Qed

def globals_initialized (g : t) (m : mem) :=
  ∀ b gd,
  find_def g b = some gd →
  match gd with
| Gfun f :=
         Mem.perm m b 0 Cur Nonempty
      ∧ (∀ ofs k p, Mem.perm m b ofs k p → ofs = 0 ∧ p = Nonempty)
| Gvar v :=
         Mem.range_perm m b 0 (init_data_list_size v.(gvar_init)) Cur (perm_globvar v)
      ∧ (∀ ofs k p, Mem.perm m b ofs k p →
            0 <= ofs < init_data_list_size v.(gvar_init) ∧ perm_order (perm_globvar v) p)
      ∧ (v.(gvar_volatile) = ff → load_store_init_data m b 0 v.(gvar_init))
      ∧ (v.(gvar_volatile) = ff → Mem.loadbytes m b 0 (init_data_list_size v.(gvar_init)) = some (bytes_of_init_data_list v.(gvar_init)))
  end

lemma alloc_global_initialized :
  ∀ g m id gd m',
  genv_next g = Mem.nextblock m →
  alloc_global m (id, gd) = some m' →
  globals_initialized g m →
     globals_initialized (add_global g (id, gd)) m'
  ∧ genv_next (add_global g (id, gd)) = Mem.nextblock m'
Proof
  intros
  exploit alloc_global_nextblock; eauto. intros NB. split
- /- globals-initialized -/
  red; intros. unfold find_def in H2; simpl in H2
  rewrite PTree.gsspec in H2. destruct (peq b (genv_next g))
+ inv H2. destruct gd0 as [f|v]; simpl in H0
* destruct (Mem.alloc m 0 1) as [m1 b] eqn:ALLOC
  exploit Mem.alloc_result; eauto. intros RES
  rewrite H, <- RES. split
  eapply Mem.perm_drop_1; eauto. omega
  intros. 
  assert (0 <= ofs < 1). { eapply Mem.perm_alloc_3; eauto. eapply Mem.perm_drop_4; eauto. }
  exploit Mem.perm_drop_2; eauto. intros ORD
  split. omega. inv ORD; auto
* set (init := gvar_init v) in *
  set (sz := init_data_list_size init) in *
  destruct (Mem.alloc m 0 sz) as [m1 b] eqn:?
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate
  destruct (store_init_data_list m2 b 0 init) as [m3|] eqn:?; try discriminate
  exploit Mem.alloc_result; eauto. intro RES
  replace (genv_next g) with b by congruence
  split. red; intros. eapply Mem.perm_drop_1; eauto
  split. intros
  assert (0 <= ofs < sz)
  { eapply Mem.perm_alloc_3; eauto. 
    erewrite store_zeros_perm by eauto
    erewrite store_init_data_list_perm by eauto. 
    eapply Mem.perm_drop_4; eauto. }
  split; auto
  eapply Mem.perm_drop_2; eauto
  split. intros NOTVOL. apply load_store_init_data_invariant with m3
  intros. eapply Mem.load_drop; eauto. right; right; right. 
  unfold perm_globvar. rewrite NOTVOL. destruct (gvar_readonly v); auto with mem
  eapply store_init_data_list_charact; eauto. 
  eapply store_zeros_read_as_zero; eauto
  intros NOTVOL. 
  transitivity (Mem.loadbytes m3 b 0 sz). 
  eapply Mem.loadbytes_drop; eauto. right; right; right
  unfold perm_globvar. rewrite NOTVOL. destruct (gvar_readonly v); auto with mem
  eapply store_init_data_list_loadbytes; eauto
  eapply store_zeros_loadbytes; eauto
+ assert (U : Mem.unchanged_on (λ _ _ := true) m m') by (eapply alloc_global_unchanged; eauto)
  assert (VALID : Mem.valid_block m b)
  { red. rewrite <- H. eapply genv_defs_range; eauto. } 
  exploit H1; eauto
  destruct gd0 as [f|v]
* intros [A B]; split; intros
  eapply Mem.perm_unchanged_on; eauto. exact I
  eapply B. eapply Mem.perm_unchanged_on_2; eauto. exact I
* intros (A & B & C & D). split; [| split; [| split]]. 
  red; intros. eapply Mem.perm_unchanged_on; eauto. exact I
  intros. eapply B. eapply Mem.perm_unchanged_on_2; eauto. exact I
  intros. apply load_store_init_data_invariant with m; auto. 
  intros. eapply Mem.load_unchanged_on_1; eauto. intros; exact I
  intros. eapply Mem.loadbytes_unchanged_on; eauto. intros; exact I
- simpl. congruence
Qed

lemma alloc_globals_initialized :
  ∀ gl ge m m',
  alloc_globals m gl = some m' →
  genv_next ge = Mem.nextblock m →
  globals_initialized ge m →
  globals_initialized (add_globals ge gl) m'
Proof
  induction gl; simpl; intros
- inv H; auto
- destruct a as [id g]. destruct (alloc_global m (id, g)) as [m1|] eqn:?; try discriminate
  exploit alloc_global_initialized; eauto. intros [P Q]
  eapply IHgl; eauto
Qed

end INITMEM

def init_mem (p : program F V) :=
  alloc_globals (globalenv p) Mem.empty p.(prog_defs)

lemma init_mem_genv_next : ∀ p m,
  init_mem p = some m →
  genv_next (globalenv p) = Mem.nextblock m
Proof
  unfold init_mem; intros
  exploit alloc_globals_nextblock; eauto. rewrite Mem.nextblock_empty. intro
  generalize (genv_next_add_globals (prog_defs p) (empty_genv (prog_public p)))
  fold (globalenv p). simpl genv_next. intros. congruence
Qed

theorem find_symbol_not_fresh :
  ∀ p id b m,
  init_mem p = some m →
  find_symbol (globalenv p) id = some b → Mem.valid_block m b
Proof
  intros. red. erewrite <- init_mem_genv_next; eauto
  eapply genv_symb_range; eauto
Qed

theorem find_def_not_fresh :
  ∀ p b g m,
  init_mem p = some m →
  find_def (globalenv p) b = some g → Mem.valid_block m b
Proof
  intros. red. erewrite <- init_mem_genv_next; eauto
  eapply genv_defs_range; eauto
Qed

theorem find_funct_ptr_not_fresh :
  ∀ p b f m,
  init_mem p = some m →
  find_funct_ptr (globalenv p) b = some f → Mem.valid_block m b
Proof
  intros. rewrite find_funct_ptr_iff in H0. eapply find_def_not_fresh; eauto
Qed

theorem find_var_info_not_fresh :
  ∀ p b gv m,
  init_mem p = some m →
  find_var_info (globalenv p) b = some gv → Mem.valid_block m b
Proof
  intros. rewrite find_var_info_iff in H0. eapply find_def_not_fresh; eauto
Qed

lemma init_mem_characterization_gen :
  ∀ p m,
  init_mem p = some m →
  globals_initialized (globalenv p) (globalenv p) m
Proof
  intros. apply alloc_globals_initialized with Mem.empty. 
  auto
  rewrite Mem.nextblock_empty. auto
  red; intros. unfold find_def in H0; simpl in H0; rewrite PTree.gempty in H0; discriminate
Qed

theorem init_mem_characterization :
  ∀ p b gv m,
  find_var_info (globalenv p) b = some gv →
  init_mem p = some m →
  Mem.range_perm m b 0 (init_data_list_size gv.(gvar_init)) Cur (perm_globvar gv)
  ∧ (∀ ofs k p, Mem.perm m b ofs k p →
        0 <= ofs < init_data_list_size gv.(gvar_init) ∧ perm_order (perm_globvar gv) p)
  ∧ (gv.(gvar_volatile) = ff →
      load_store_init_data (globalenv p) m b 0 gv.(gvar_init))
  ∧ (gv.(gvar_volatile) = ff →
      Mem.loadbytes m b 0 (init_data_list_size gv.(gvar_init)) = some (bytes_of_init_data_list (globalenv p) gv.(gvar_init)))
Proof
  intros. rewrite find_var_info_iff in H
  exploit init_mem_characterization_gen; eauto
Qed

theorem init_mem_characterization_2 :
  ∀ p b fd m,
  find_funct_ptr (globalenv p) b = some fd →
  init_mem p = some m →
  Mem.perm m b 0 Cur Nonempty
  ∧ (∀ ofs k p, Mem.perm m b ofs k p → ofs = 0 ∧ p = Nonempty)
Proof
  intros. rewrite find_funct_ptr_iff in H
  exploit init_mem_characterization_gen; eauto
Qed

/- ** Compatibility with memory injections -/

section INITMEM_INJ

parameter ge : t
parameter thr : block
Hypothesis symb_inject : ∀ id b, find_symbol ge id = some b → Plt b thr

lemma store_zeros_neutral :
  ∀ m b p n m',
  Mem.inject_neutral thr m →
  Plt b thr →
  store_zeros m b p n = some m' →
  Mem.inject_neutral thr m'
Proof
  intros until n. functional induction (store_zeros m b p n); intros
  inv H1; auto
  apply IHo; auto. eapply Mem.store_inject_neutral; eauto. constructor
  inv H1
Qed

lemma store_init_data_neutral :
  ∀ m b p id m',
  Mem.inject_neutral thr m →
  Plt b thr →
  store_init_data ge m b p id = some m' →
  Mem.inject_neutral thr m'
Proof
  intros
  destruct id; simpl in H1; try (eapply Mem.store_inject_neutral; eauto; fail)
  congruence
  destruct (find_symbol ge i) as [b'|] eqn:E; try discriminate
  eapply Mem.store_inject_neutral; eauto
  econstructor. unfold Mem.flat_inj. apply pred_dec_true; auto. eauto
  rewrite Ptrofs.add_zero. auto
Qed

lemma store_init_data_list_neutral :
  ∀ b idl m p m',
  Mem.inject_neutral thr m →
  Plt b thr →
  store_init_data_list ge m b p idl = some m' →
  Mem.inject_neutral thr m'
Proof
  induction idl; simpl; intros
  congruence
  destruct (store_init_data ge m b p a) as [m1|] eqn:E; try discriminate
  eapply IHidl. eapply store_init_data_neutral; eauto. auto. eauto
Qed

lemma alloc_global_neutral :
  ∀ idg m m',
  alloc_global ge m idg = some m' →
  Mem.inject_neutral thr m →
  Plt (Mem.nextblock m) thr →
  Mem.inject_neutral thr m'
Proof
  intros. destruct idg as [id [f|v]]; simpl in H
  /- function -/
  destruct (Mem.alloc m 0 1) as [m1 b] eqn:?
  assert (Plt b thr). rewrite (Mem.alloc_result _ _ _ _ _ Heqp). auto
  eapply Mem.drop_inject_neutral; eauto
  eapply Mem.alloc_inject_neutral; eauto
  /- variable -/
  set (init := gvar_init v) in *
  set (sz := init_data_list_size init) in *
  destruct (Mem.alloc m 0 sz) as [m1 b] eqn:?
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate
  destruct (store_init_data_list ge m2 b 0 init) as [m3|] eqn:?; try discriminate
  assert (Plt b thr). rewrite (Mem.alloc_result _ _ _ _ _ Heqp). auto
  eapply Mem.drop_inject_neutral; eauto
  eapply store_init_data_list_neutral with (m := m2) (b := b); eauto
  eapply store_zeros_neutral with (m := m1); eauto
  eapply Mem.alloc_inject_neutral; eauto
Qed

theorem advance_next_le : ∀ gl x, Ple x (advance_next gl x)
Proof
  induction gl; simpl; intros
  apply Ple_refl
  apply Ple_trans with (Psucc x). apply Ple_succ. eauto
Qed

lemma alloc_globals_neutral :
  ∀ gl m m',
  alloc_globals ge m gl = some m' →
  Mem.inject_neutral thr m →
  Ple (Mem.nextblock m') thr →
  Mem.inject_neutral thr m'
Proof
  induction gl; intros
  simpl in *. congruence
  exploit alloc_globals_nextblock; eauto. intros EQ
  simpl in *. destruct (alloc_global ge m a) as [m1|] eqn:E; try discriminate
  exploit alloc_global_neutral; eauto
  assert (Ple (Psucc (Mem.nextblock m)) (Mem.nextblock m'))
  { rewrite EQ. apply advance_next_le. }
  unfold Plt, Ple in *; zify; omega
Qed

end INITMEM_INJ

theorem initmem_inject :
  ∀ p m,
  init_mem p = some m →
  Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m
Proof
  unfold init_mem; intros
  apply Mem.neutral_inject
  eapply alloc_globals_neutral; eauto
  intros. exploit find_symbol_not_fresh; eauto
  apply Mem.empty_inject_neutral
  apply Ple_refl
Qed

/- ** Sufficient and necessary conditions for the initial memory to exist. -/

/- Alignment properties -/

def init_data_alignment (i : init_data) : ℤ :=
  match i with
| Init_int8 n := 1
| Init_int16 n := 2
| Init_int32 n := 4
| Init_int64 n := 8
| Init_float32 n := 4
| Init_float64 n := 4
| Init_addrof symb ofs := if Archi.ptr64 then 8 else 4
| Init_space n := 1
  end

def init_data_list_aligned (p : ℤ) (il : list init_data) {struct il} : Prop :=
  match il with
| nil := true
| i1 :: il := (init_data_alignment i1 | p) ∧ init_data_list_aligned (p + init_data_size i1) il
  end

section INITMEM_INVERSION

parameter ge : t

lemma store_init_data_aligned :
  ∀ m b p i m',
  store_init_data ge m b p i = some m' →
  (init_data_alignment i | p)
Proof
  intros
  assert (DFL : ∀ chunk v,
    Mem.store chunk m b p v = some m' →
    align_chunk chunk = init_data_alignment i →
    (init_data_alignment i | p))
  { intros. apply Mem.store_valid_access_3 in H0. destruct H0. congruence. }
  destruct i; simpl in H; eauto
  simpl. apply ℤ.divide_1_l
  destruct (find_symbol ge i); try discriminate. eapply DFL. eassumption. 
  unfold Mptr, init_data_alignment; destruct Archi.ptr64; auto
Qed

lemma store_init_data_list_aligned :
  ∀ b il m p m',
  store_init_data_list ge m b p il = some m' →
  init_data_list_aligned p il
Proof
  induction il as [ | i1 il]; simpl; intros
- auto
- destruct (store_init_data ge m b p i1) as [m1|] eqn:S1; try discriminate
  split; eauto. eapply store_init_data_aligned; eauto
Qed

lemma store_init_data_list_free_idents :
  ∀ b i o il m p m',
  store_init_data_list ge m b p il = some m' →
  In (Init_addrof i o) il →
  ∃ b', find_symbol ge i = some b'
Proof
  induction il as [ | i1 il]; simpl; intros
- contradiction
- destruct (store_init_data ge m b p i1) as [m1|] eqn:S1; try discriminate
  destruct H0
+ subst i1. simpl in S1. destruct (find_symbol ge i) as [b'|]. ∃ b'; auto. discriminate
+ eapply IHil; eauto
Qed

end INITMEM_INVERSION

theorem init_mem_inversion :
  ∀ p m id v,
  init_mem p = some m →
  In (id, Gvar v) p.(prog_defs) →
  init_data_list_aligned 0 v.(gvar_init)
  ∧ ∀ i o, In (Init_addrof i o) v.(gvar_init) → ∃ b, find_symbol (globalenv p) i = some b
Proof
  intros until v. unfold init_mem. set (ge := globalenv p). 
  revert m. generalize Mem.empty. generalize (prog_defs p). 
  induction l as [ | idg1 defs ]; simpl; intros m m'; intros
- contradiction
- destruct (alloc_global ge m idg1) as [m''|] eqn:A; try discriminate
  destruct H0
+ subst idg1; simpl in A. 
  set (il := gvar_init v) in *. set (sz := init_data_list_size il) in *. 
  destruct (Mem.alloc m 0 sz) as [m1 b]
  destruct (store_zeros m1 b 0 sz) as [m2|]; try discriminate
  destruct (store_init_data_list ge m2 b 0 il) as [m3|] eqn:B; try discriminate
  split. eapply store_init_data_list_aligned; eauto. intros; eapply store_init_data_list_free_idents; eauto
+ eapply IHdefs; eauto
Qed

section INITMEM_EXISTS

parameter ge : t

lemma store_zeros_exists :
  ∀ m b p n,
  Mem.range_perm m b p (p + n) Cur Writable →
  ∃ m', store_zeros m b p n = some m'
Proof
  intros until n. functional induction (store_zeros m b p n); intros PERM
- ∃ m; auto
- apply IHo. red; intros. eapply Mem.perm_store_1; eauto. apply PERM. omega
- destruct (Mem.valid_access_store m Mint8unsigned b p Vzero) as (m' & STORE)
  split. red; intros. apply Mem.perm_cur. apply PERM. simpl in H. omega. 
  simpl. apply ℤ.divide_1_l
  congruence
Qed

lemma store_init_data_exists :
  ∀ m b p i,
  Mem.range_perm m b p (p + init_data_size i) Cur Writable →
  (init_data_alignment i | p) →
  (∀ id ofs, i = Init_addrof id ofs → ∃ b, find_symbol ge id = some b) →
  ∃ m', store_init_data ge m b p i = some m'
Proof
  intros. 
  assert (DFL : ∀ chunk v,
          init_data_size i = size_chunk chunk →
          init_data_alignment i = align_chunk chunk →
          ∃ m', Mem.store chunk m b p v = some m')
  { intros. destruct (Mem.valid_access_store m chunk b p v) as (m' & STORE)
    split. rewrite <- H2; auto. rewrite <- H3; auto. 
    ∃ m'; auto. }
  destruct i; eauto
  simpl. ∃ m; auto
  simpl. exploit H1; eauto. intros (b1 & FS). rewrite FS. eapply DFL. 
  unfold init_data_size, Mptr. destruct Archi.ptr64; auto
  unfold init_data_alignment, Mptr. destruct Archi.ptr64; auto
Qed

lemma store_init_data_list_exists :
  ∀ b il m p,
  Mem.range_perm m b p (p + init_data_list_size il) Cur Writable →
  init_data_list_aligned p il →
  (∀ id ofs, In (Init_addrof id ofs) il → ∃ b, find_symbol ge id = some b) →
  ∃ m', store_init_data_list ge m b p il = some m'
Proof
  induction il as [ | i1 il ]; simpl; intros
- ∃ m; auto
- destruct H0. 
  destruct (@store_init_data_exists m b p i1) as (m1 & S1); eauto
  red; intros. apply H. generalize (init_data_list_size_pos il); omega
  rewrite S1. 
  apply IHil; eauto. 
  red; intros. erewrite <- store_init_data_perm by eauto. apply H. generalize (init_data_size_pos i1); omega
Qed

lemma alloc_global_exists :
  ∀ m idg,
  match idg with
| (id, Gfun f) := true
| (id, Gvar v) :=
        init_data_list_aligned 0 v.(gvar_init)
     ∧ ∀ i o, In (Init_addrof i o) v.(gvar_init) → ∃ b, find_symbol ge i = some b
  end →
  ∃ m', alloc_global ge m idg = some m'
Proof
  intros m [id [f|v]]; intros; simpl
- destruct (Mem.alloc m 0 1) as [m1 b] eqn:ALLOC
  destruct (Mem.range_perm_drop_2 m1 b 0 1 Nonempty) as [m2 DROP]
  red; intros; eapply Mem.perm_alloc_2; eauto. 
  ∃ m2; auto
- destruct H as [P Q]
  set (sz := init_data_list_size (gvar_init v))
  destruct (Mem.alloc m 0 sz) as [m1 b] eqn:ALLOC
  assert (P1 : Mem.range_perm m1 b 0 sz Cur Freeable) by (red; intros; eapply Mem.perm_alloc_2; eauto)
  destruct (@store_zeros_exists m1 b 0 sz) as [m2 ZEROS]
  red; intros. apply Mem.perm_implies with Freeable; auto with mem
  rewrite ZEROS
  assert (P2 : Mem.range_perm m2 b 0 sz Cur Freeable)
  { red; intros. erewrite <- store_zeros_perm by eauto. eauto. }
  destruct (@store_init_data_list_exists b (gvar_init v) m2 0) as [m3 STORE]; auto
  red; intros. apply Mem.perm_implies with Freeable; auto with mem
  rewrite STORE
  assert (P3 : Mem.range_perm m3 b 0 sz Cur Freeable)
  { red; intros. erewrite <- store_init_data_list_perm by eauto. eauto. }
  destruct (Mem.range_perm_drop_2 m3 b 0 sz (perm_globvar v)) as [m4 DROP]; auto
  ∃ m4; auto
Qed

end INITMEM_EXISTS

theorem init_mem_exists :
  ∀ p,
  (∀ id v, In (id, Gvar v) (prog_defs p) →
        init_data_list_aligned 0 v.(gvar_init)
     ∧ ∀ i o, In (Init_addrof i o) v.(gvar_init) → ∃ b, find_symbol (globalenv p) i = some b) →
  ∃ m, init_mem p = some m
Proof
  intros. set (ge := globalenv p) in *. 
  unfold init_mem. revert H. generalize (prog_defs p) Mem.empty
  induction l as [ | idg l]; simpl; intros
- ∃ m; auto
- destruct (@alloc_global_exists ge m idg) as [m1 A1]
  destruct idg as [id [f|v]]; eauto
  fold ge. rewrite A1. eapply IHl; eauto. 
Qed. 

end GENV

/- * Commutation with program transformations -/

section MATCH_GENVS

Context {A B V W : Type} (R : globdef A V → globdef B W → Prop)

structure match_genvs (ge1 : t A V) (ge2 : t B W) : Prop := {
  mge_next :
    genv_next ge2 = genv_next ge1;
  mge_symb :
    ∀ id, PTree.get id (genv_symb ge2) = PTree.get id (genv_symb ge1);
  mge_defs :
    ∀ b, option_rel R (PTree.get b (genv_defs ge1)) (PTree.get b (genv_defs ge2))
}

lemma add_global_match :
  ∀ ge1 ge2 id g1 g2,
  match_genvs ge1 ge2 →
  R g1 g2 →
  match_genvs (add_global ge1 (id, g1)) (add_global ge2 (id, g2))
Proof
  intros. destruct H. constructor; simpl; intros
- congruence
- rewrite mge_next0, ! PTree.gsspec. destruct (peq id0 id); auto. 
- rewrite mge_next0, ! PTree.gsspec. destruct (peq b (genv_next ge1)). 
  constructor; auto
  auto
Qed

lemma add_globals_match :
  ∀ gl1 gl2,
  list_forall2 (λ idg1 idg2 := fst idg1 = fst idg2 ∧ R (snd idg1) (snd idg2)) gl1 gl2 →
  ∀ ge1 ge2, match_genvs ge1 ge2 →
  match_genvs (add_globals ge1 gl1) (add_globals ge2 gl2)
Proof
  induction 1; intros; simpl
  auto
  destruct a1 as [id1 g1]; destruct b1 as [id2 g2]; simpl in *; destruct H; subst id2
  apply IHlist_forall2. apply add_global_match; auto
Qed

end MATCH_GENVS

section MATCH_PROGRAMS

Context {C F1 V1 F2 V2 : Type} {LC : Linker C} {LF : Linker F1} {LV : Linker V1}
parameter match_fundef : C → F1 → F2 → Prop
parameter match_varinfo : V1 → V2 → Prop
parameter ctx : C
parameter p : program F1 V1
parameter tp : program F2 V2
Hypothesis progmatch : match_program_gen match_fundef match_varinfo ctx p tp

lemma globalenvs_match :
  match_genvs (match_globdef match_fundef match_varinfo ctx) (globalenv p) (globalenv tp)
Proof
  intros. apply add_globals_match. apply progmatch. 
  constructor; simpl; intros; auto. rewrite ! PTree.gempty. constructor
Qed

theorem find_def_match_2 :
  ∀ b, option_rel (match_globdef match_fundef match_varinfo ctx)
                       (find_def (globalenv p) b) (find_def (globalenv tp) b)
Proof (mge_defs globalenvs_match)

theorem find_def_match :
  ∀ b g,
  find_def (globalenv p) b = some g →
  ∃ tg,
  find_def (globalenv tp) b = some tg ∧ match_globdef match_fundef match_varinfo ctx g tg
Proof
  intros. generalize (find_def_match_2 b). rewrite H; intros R; inv R
  ∃ y; auto. 
Qed

theorem find_funct_ptr_match :
  ∀ b f,
  find_funct_ptr (globalenv p) b = some f →
  ∃ cunit tf,
  find_funct_ptr (globalenv tp) b = some tf ∧ match_fundef cunit f tf ∧ linkorder cunit ctx
Proof
  intros. rewrite find_funct_ptr_iff in *. apply find_def_match in H. 
  destruct H as (tg & P & Q). inv Q. 
  ∃ ctx', f2; intuition auto. apply find_funct_ptr_iff; auto
Qed

theorem find_funct_match :
  ∀ v f,
  find_funct (globalenv p) v = some f →
  ∃ cunit tf,
  find_funct (globalenv tp) v = some tf ∧ match_fundef cunit f tf ∧ linkorder cunit ctx
Proof
  intros. exploit find_funct_inv; eauto. intros [b EQ]. subst v
  rewrite find_funct_find_funct_ptr in H
  rewrite find_funct_find_funct_ptr
  apply find_funct_ptr_match. auto
Qed

theorem find_var_info_match :
  ∀ b v,
  find_var_info (globalenv p) b = some v →
  ∃ tv,
  find_var_info (globalenv tp) b = some tv ∧ match_globvar match_varinfo v tv
Proof
  intros. rewrite find_var_info_iff in *. apply find_def_match in H. 
  destruct H as (tg & P & Q). inv Q. 
  ∃ v2; split; auto. apply find_var_info_iff; auto
Qed

theorem find_symbol_match :
  ∀ (s : ident),
  find_symbol (globalenv tp) s = find_symbol (globalenv p) s
Proof
  intros. destruct globalenvs_match. apply mge_symb0
Qed

theorem senv_match :
  Senv.equiv (to_senv (globalenv p)) (to_senv (globalenv tp))
Proof
  red; simpl. repeat split
- apply find_symbol_match
- intros. unfold public_symbol. rewrite find_symbol_match. 
  rewrite ! globalenv_public. 
  destruct progmatch as (P & Q & R). rewrite R. auto
- intros. unfold block_is_volatile. 
  destruct globalenvs_match as [P Q R]. specialize (R b)
  unfold find_var_info, find_def
  inv R; auto
  inv H1; auto
  inv H2; auto
Qed

lemma store_init_data_list_match :
  ∀ idl m b ofs m',
  store_init_data_list (globalenv p) m b ofs idl = some m' →
  store_init_data_list (globalenv tp) m b ofs idl = some m'
Proof
  induction idl; simpl; intros
- auto
- destruct (store_init_data (globalenv p) m b ofs a) as [m1|] eqn:S; try discriminate
  assert (X : store_init_data (globalenv tp) m b ofs a = some m1)
  { destruct a; auto. simpl; rewrite find_symbol_match; auto. }
  rewrite X. auto
Qed

lemma alloc_globals_match :
  ∀ gl1 gl2, list_forall2 (match_ident_globdef match_fundef match_varinfo ctx) gl1 gl2 →
  ∀ m m',
  alloc_globals (globalenv p) m gl1 = some m' →
  alloc_globals (globalenv tp) m gl2 = some m'
Proof
  induction 1; simpl; intros
- auto
- destruct (alloc_global (globalenv p) m a1) as [m1|] eqn:?; try discriminate
  assert (X : alloc_global (globalenv tp) m b1 = some m1)
  { destruct a1 as [id1 g1]; destruct b1 as [id2 g2]; destruct H; simpl in *
    subst id2. inv H2
  - auto
  - inv H; simpl in *. 
    set (sz := init_data_list_size init) in *
    destruct (Mem.alloc m 0 sz) as [m2 b] eqn:?
    destruct (store_zeros m2 b 0 sz) as [m3|] eqn:?; try discriminate
    destruct (store_init_data_list (globalenv p) m3 b 0 init) as [m4|] eqn:?; try discriminate
    erewrite store_init_data_list_match; eauto
  }
  rewrite X; eauto
Qed

theorem init_mem_match :
  ∀ m, init_mem p = some m → init_mem tp = some m
Proof
  unfold init_mem; intros
  eapply alloc_globals_match; eauto. apply progmatch
Qed

end MATCH_PROGRAMS

/- Special case for partial transformations that do not depend on the compilation unit -/

section TRANSFORM_PARTIAL

Context {A B V : Type} {LA : Linker A} {LV : Linker V}
Context {transf : A → res B} {p : program A V} {tp : program B V}
Hypothesis progmatch : match_program (λ cu f tf := transf f = OK tf) eq p tp

theorem find_funct_ptr_transf_partial :
  ∀ b f,
  find_funct_ptr (globalenv p) b = some f →
  ∃ tf,
  find_funct_ptr (globalenv tp) b = some tf ∧ transf f = OK tf
Proof
  intros. exploit (find_funct_ptr_match progmatch); eauto. 
  intros (cu & tf & P & Q & R); ∃ tf; auto
Qed

theorem find_funct_transf_partial :
  ∀ v f,
  find_funct (globalenv p) v = some f →
  ∃ tf,
  find_funct (globalenv tp) v = some tf ∧ transf f = OK tf
Proof
  intros. exploit (find_funct_match progmatch); eauto. 
  intros (cu & tf & P & Q & R); ∃ tf; auto
Qed

theorem find_symbol_transf_partial :
  ∀ (s : ident),
  find_symbol (globalenv tp) s = find_symbol (globalenv p) s
Proof
  intros. eapply (find_symbol_match progmatch). 
Qed

theorem senv_transf_partial :
  Senv.equiv (to_senv (globalenv p)) (to_senv (globalenv tp))
Proof
  intros. eapply (senv_match progmatch)
Qed

theorem init_mem_transf_partial :
  ∀ m, init_mem p = some m → init_mem tp = some m
Proof
  eapply (init_mem_match progmatch)
Qed

end TRANSFORM_PARTIAL

/- Special case for total transformations that do not depend on the compilation unit -/

section TRANSFORM_TOTAL

Context {A B V : Type} {LA : Linker A} {LV : Linker V}
Context {transf : A → B} {p : program A V} {tp : program B V}
Hypothesis progmatch : match_program (λ cu f tf := tf = transf f) eq p tp

theorem find_funct_ptr_transf :
  ∀ b f,
  find_funct_ptr (globalenv p) b = some f →
  find_funct_ptr (globalenv tp) b = some (transf f)
Proof
  intros. exploit (find_funct_ptr_match progmatch); eauto. 
  intros (cu & tf & P & Q & R). congruence
Qed

theorem find_funct_transf :
  ∀ v f,
  find_funct (globalenv p) v = some f →
  find_funct (globalenv tp) v = some (transf f)
Proof
  intros. exploit (find_funct_match progmatch); eauto. 
  intros (cu & tf & P & Q & R). congruence
Qed

theorem find_symbol_transf :
  ∀ (s : ident),
  find_symbol (globalenv tp) s = find_symbol (globalenv p) s
Proof
  intros. eapply (find_symbol_match progmatch)
Qed

theorem senv_transf :
  Senv.equiv (to_senv (globalenv p)) (to_senv (globalenv tp))
Proof
  intros. eapply (senv_match progmatch)
Qed

theorem init_mem_transf :
  ∀ m, init_mem p = some m → init_mem tp = some m
Proof
  eapply (init_mem_match progmatch)
Qed

end TRANSFORM_TOTAL

end Genv

Coercion Genv.to_senv : Genv.t >→ Senv.t.