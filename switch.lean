
/- Multi-way branches (``switch'' statements) and their compilation
    to comparison trees. -/

import .values

namespace switch
open values word integers maps

inductive switch_argument : bool → val → Π w:ℕ+, word w → Prop
| switch_argument_32 (i) : switch_argument ff (Vint i) _ i
| switch_argument_64 (i) : switch_argument tt (Vlong i) _ i

section
parameter wordsize : ℕ+

local notation `uword` := uword wordsize

/- A multi-way branch is composed of a list of (key, action) pairs,
  plus a default action.  -/

def table : Type := list (uword × ℕ)

def switch_target (n : uword) (dfl : ℕ) : table → ℕ
| []                     := dfl
| ((key, action) :: rem) := if n = key then action else switch_target rem

def switch_target' (n : uword) (dfl : ℕ) (tbl : list (ℤ × ℕ)) : ℕ :=
switch_target n dfl $ tbl.map (λ⟨a, b⟩, (repr a, b))

/- Multi-way branches are translated to comparison trees.
    Each node of the tree performs either
- an equality against one of the keys;
- or a "less than" test against one of the keys;
- or a computed branch (jump table) against a range of key values. -/

inductive comptree : Type
| CTaction {} (act : ℕ)
| CTifeq (key : uword) (act : ℕ) (cne : comptree)
| CTiflt (key : uword) (clt : comptree) (cge : comptree)
| CTjumptable (ofs sz : uword) (acts : list ℕ) (h : (sz:ℕ) ≤ acts.length) (cother : comptree)
open comptree

def comptree_match (n : uword) : comptree → option ℕ
| (CTaction act) := some act
| (CTifeq key act t') := if n = key then some act else comptree_match t'
| (CTiflt key t1 t2) := if n < key then comptree_match t1 else comptree_match t2
| (CTjumptable ofs sz tbl sl t') :=
  let delta := n - ofs in
  if h : delta < sz
  then some (list.nth_le tbl (unsigned delta) (lt_of_lt_of_le h sl))
  else comptree_match t'

def comptree_match' (n : uword) (dfl : ℕ) (t : comptree) : ℕ :=
(comptree_match n t).get_or_else dfl

/- The translation from a table to a comparison tree is performed
  by untrusted Caml code (function [compile_switch] in
  file [RTLgenaux.ml]).  In Coq, we validate a posteriori the
  result of this function.  In other terms, we now develop
  and prove correct Coq functions that take a table and a comparison
  tree, and check that their semantics are equivalent. -/

def split_lt (pivot : uword) (cases : table) : table × table :=
cases.partition (λ e, e.1 < pivot)

def split_eq (pivot : uword) : table → option ℕ × table
| [] := (none, [])
| ((key, act) :: rem) :=
  let (same, others) := split_eq rem in
  if key = pivot
  then (some act, others)
  else (same, (key, act) :: others)

def split_between (ofs sz : uword) : table → PTree ℕ × table
| [] := (∅, [])
| ((key, act) :: rem) :=
  let (inside, outside) := split_between rem in
  if key - ofs < sz
  then (PTree.set (pos_num.of_nat_succ key) act inside, outside)
  else (inside, (key, act) :: outside)

def refine_low_bound (v lo : uword) := if v = lo then lo + 1 else lo

def refine_high_bound (v hi : uword) := if v = hi then hi - 1 else hi

def validate_jumptable (dfl : ℕ) (cases : PTree ℕ) : Π (tbl : list ℕ) (n : uword),
  semidecidable (∀ (v : uword) h,
    tbl.nth_le (unsigned (v - n)) h = cases.get_or (pos_num.of_nat_succ v) dfl)
| []           n := semidecidable.success $ λ v h, absurd h (nat.not_lt_zero _)
| (act :: rem) n :=
  semidecidable.bind (act = cases.get_or (pos_num.of_nat_succ n) dfl) $ λae,
  @semidecidable.bind _ _ (validate_jumptable rem (n + 1)) $ λIH,
  semidecidable.success $
  show ∀ (v : uword) h, list.nth_le (act :: rem) (unsigned (v - n)) h =
      PTree.get_or (pos_num.of_nat_succ ↑v) cases dfl, begin
    intro v,
    ginduction unsigned (v - n) with u; rw u; dsimp [list.nth_le]; intro h,
    { note vn : v = n := eq_of_sub_eq_zero (unsigned_eq.2 $ eq.trans u unsigned_zero.symm),
      rw vn, exact ae },
    { assert va : unsigned (v - (n + 1)) = a,
      { rw [-sub_sub, sub_unsigned, unsigned_one, u, -int.coe_nat_sub, unsigned_repr],
        refl,
        { change a ≤ _,
          apply nat.le_of_succ_le,
          rw -u, apply unsigned_range_2 },
        { apply nat.succ_pos } },
      note : ∀ h, list.nth_le rem (unsigned (v - (n + 1))) h =
                  PTree.get_or (pos_num.of_nat_succ ↑v) cases dfl := IH v,
      rw va at this, apply this }
  end

def table_tree_agree' (dfl : ℕ) (cases : table) (t : comptree) (lo hi : uword) : Prop :=
∀ ⦃n⦄, lo ≤ n → n ≤ hi → switch_target n dfl cases = comptree_match' n dfl t

def table_tree_agree (dfl : ℕ) (cases : table) (t : comptree) : Prop :=
∀ ⦃n⦄, switch_target n dfl cases = comptree_match' n dfl t

lemma split_eq_prop (dfl : ℕ) {pivot cases} (v) : ∀ ⦃optact cases'⦄,
  split_eq pivot cases = (optact, cases') →
  switch_target v dfl cases =
   (if v = pivot then optact.get_or_else dfl
    else switch_target v dfl cases') := sorry'

lemma split_lt_prop (dfl : ℕ) {pivot cases} (v) : ∀ ⦃lcases rcases⦄,
  split_lt pivot cases = (lcases, rcases) →
  switch_target v dfl cases =
    (if v < pivot
     then switch_target v dfl lcases
     else switch_target v dfl rcases) := sorry'

lemma split_between_prop (dfl : ℕ) (v) {ofs sz} : ∀ {cases} ⦃inside outside⦄,
  split_between ofs sz cases = (inside, outside) →
  switch_target v dfl cases =
    (if v - ofs < sz
     then PTree.get_or (pos_num.of_nat_succ v) inside dfl
     else switch_target v dfl outside) := sorry'

def validate (dfl : ℕ) : Π (cases : table) (t : comptree) (lo hi : uword),
  semidecidable (table_tree_agree' dfl cases t lo hi)
| []                  (CTaction act) lo hi :=
  semidecidable.bind (dfl = act) $ λh,
  semidecidable.success $ λ n nl nh, h
| ((key1, act1) :: _) (CTaction act) lo hi :=
  semidecidable.bind (key1 = lo ∧ lo = hi ∧ act1 = act) $ λ⟨kl, lh, aa⟩,
  semidecidable.success $ λ n nl nh,
  begin
    dsimp [switch_target], rw if_pos, exact aa,
    rw [kl], rw -lh at nh, exact le_antisymm nh nl
  end
| cases (CTifeq pivot act t') lo hi :=
  match _, rfl : ∀ x, split_eq pivot cases = x → _ with
  | (none, _), _ := semidecidable.fail
  | (some act', others), se :=
    semidecidable.bind (act' = act) $ λaa,
    @semidecidable.bind _ _ (validate others t'
      (refine_low_bound pivot lo) (refine_high_bound pivot hi)) $ λIH,
    semidecidable.success $
    show table_tree_agree' dfl cases (CTifeq pivot act t') lo hi, begin
      rw aa at se, intros n nl nh,
      rw [split_eq_prop _ dfl n se],
      by_cases n = pivot with np; simp [np, option.get_or_else, comptree_match', comptree_match],
      apply IH,
      { dsimp [refine_low_bound], by_cases pivot = lo with pl; simp [pl],
        { rw pl at np, exact uword.succ_le_of_lt (lt_of_le_of_ne nl (ne.symm np)) },
        { exact nl } },
      { dsimp [refine_high_bound], by_cases pivot = hi with ph; simp [ph],
        { rw ph at np, exact uword.le_pred_of_lt (lt_of_le_of_ne nh np) },
        { exact nh } }
    end
  end
| cases (CTiflt pivot t1 t2) lo hi :=
  match _, rfl : ∀ x, split_lt pivot cases = x → _ with
  | (lcases, rcases), sl :=
    @semidecidable.bind _ _ (validate lcases t1 lo (pivot - 1)) $ λL,
    @semidecidable.bind _ _ (validate rcases t2 pivot hi) $ λR,
    semidecidable.success $
    show table_tree_agree' dfl cases (CTiflt pivot t1 t2) lo hi, begin
      intros n nl nh,
      rw [split_lt_prop _ dfl n sl],
      by_cases (n < pivot) with lp; simp [lp, comptree_match', comptree_match],
      exact L nl (uword.le_pred_of_lt lp),
      exact R (le_of_not_gt lp) nh,
    end
  end
| cases (CTjumptable ofs sz tbl h t') lo hi :=
  match _, rfl : ∀ x, split_between ofs sz cases = x → _ with
  | (inside, outside), sb :=
    @semidecidable.bind _ _ (validate_jumptable dfl inside tbl ofs) $ λI,
    @semidecidable.bind _ _ (validate outside t' lo hi) $ λO,
    semidecidable.success $
    show table_tree_agree' dfl cases (CTjumptable ofs sz tbl h t') lo hi, begin
      intros n nl nh,
      rw [split_between_prop _ dfl n sb],
      dsimp only [comptree_match', comptree_match],
      cases (by apply_instance : decidable (n - ofs < sz)) with ns ns; dsimp only [ite, dite, option.get_or_else],
      exact O nl nh,
      { rw I }
    end
  end

def validate_switch (dfl : ℕ) (cases : table) (t : comptree) :
  semidecidable (table_tree_agree dfl cases t) :=
begin
  refine @semidecidable.of_imp _ _ _ (validate _ dfl cases t 0 (repr (max_unsigned wordsize))),
  intros h n,
  apply h (uword.zero_le _),
  unfold has_le.le leu,
  rw unsigned_repr,
  { apply unsigned_range_2 },
  { apply le_refl }
end

/- Caml code for compile_switch

module ZSet = Set.Make(Z)

let normalize_table tbl =
  let rec norm keys accu = function
  | [] -> (accu, keys)
  | (key, act) :: rem ->
      if ZSet.mem key keys
      then norm keys accu rem
      else norm (ZSet.add key keys) ((key, act) :: accu) rem
  in norm ZSet.empty [] tbl

let compile_switch_as_tree modulus default tbl =
  let sw = Array.of_list tbl in
  Array.stable_sort (fun (n1, _) (n2, _) -> Z.compare n1 n2) sw;
  let rec build lo hi minval maxval =
    match hi - lo with
    | 0 ->
       CTaction default
    | 1 ->
       let (key, act) = sw.(lo) in
       if Z.sub maxval minval = Z.zero
       then CTaction act
       else CTifeq(key, act, CTaction default)
    | 2 ->
       let (key1, act1) = sw.(lo)
       and (key2, act2) = sw.(lo+1) in
       CTifeq(key1, act1,
         if Z.sub maxval minval = Z.one
         then CTaction act2
         else CTifeq(key2, act2, CTaction default))
    | 3 ->
       let (key1, act1) = sw.(lo)
       and (key2, act2) = sw.(lo+1)
       and (key3, act3) = sw.(lo+2) in
       CTifeq(key1, act1,
        CTifeq(key2, act2,
          if Z.sub maxval minval = Z.of_uint 2
          then CTaction act3
          else CTifeq(key3, act3, CTaction default)))
    | _ ->
       let mid = (lo + hi) / 2 in
       let (pivot, _) = sw.(mid) in
       CTiflt(pivot,
              build lo mid minval (Z.sub pivot Z.one),
              build mid hi pivot maxval)
  in build 0 (Array.length sw) Z.zero modulus

let compile_switch_as_jumptable default cases minkey maxkey =
  let tblsize = 1 + Z.to_int (Z.sub maxkey minkey) in
  assert (tblsize >= 0 && tblsize <= Sys.max_array_length);
  let tbl = Array.make tblsize default in
  List.iter
    (fun (key, act) ->
       let pos = Z.to_int (Z.sub key minkey) in
       tbl.(pos) <- act)
    cases;
  CTjumptable(minkey,
              Z.of_uint tblsize,
              Array.to_list tbl,
              CTaction default)

let dense_enough (numcases: int) (minkey: Z.t) (maxkey: Z.t) =
  let span = Z.sub maxkey minkey in
  assert (Z.ge span Z.zero);
  let tree_size = Z.mul (Z.of_uint 4) (Z.of_uint numcases)
  and table_size = Z.add (Z.of_uint 8) span in
  numcases >= 7           (* small jump tables are always less efficient *)
  && Z.le table_size tree_size
  && Z.lt span (Z.of_uint Sys.max_array_length)

let compile_switch modulus default table =
  let (tbl, keys) = normalize_table table in
  if ZSet.is_empty keys then CTaction default else begin
    let minkey = ZSet.min_elt keys
    and maxkey = ZSet.max_elt keys in
    if dense_enough (List.length tbl) minkey maxkey
    then compile_switch_as_jumptable default tbl minkey maxkey
    else compile_switch_as_tree modulus default tbl
  end
-/

end
end switch