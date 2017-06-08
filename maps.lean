import data.hash_map .lib

namespace maps

def prev_append : pos_num → pos_num → pos_num
| pos_num.one j := j
| (pos_num.bit1 i') j := prev_append i' (pos_num.bit1 j)
| (pos_num.bit0 i') j := prev_append i' (pos_num.bit0 j)

def prev (i : pos_num) : pos_num :=
prev_append i pos_num.one

inductive PTree (A : Type) : Type
| leaf {} : PTree
| node    : PTree → option A → PTree → PTree
open PTree

namespace PTree

instance {A} : has_emptyc (PTree A) := ⟨leaf⟩

def get {A : Type} : pos_num → PTree A → option A :=
by { intros i m, revert i,
     induction m with l o r Il Ir; intro i, exact none,
     cases i with i' i',
     exact o,
     exact Il i', exact Ir i' }

def get_or {A : Type} (n : pos_num) (t : PTree A) (dfl : A) : A :=
(t.get n).get_or_else dfl

def set {A : Type} : pos_num → A → PTree A → PTree A
| pos_num.one       v leaf         := node leaf (some v) leaf
| (pos_num.bit0 i') v leaf         := node (set i' v leaf) none leaf
| (pos_num.bit1 i') v leaf         := node leaf none (set i' v leaf)
| pos_num.one       v (node l o r) := node l (some v) r
| (pos_num.bit0 i') v (node l o r) := node (set i' v l) o r
| (pos_num.bit1 i') v (node l o r) := node l o (set i' v r)

lemma gleaf {A} (i) : get i (leaf : PTree A) = none :=
by induction i; simp [get]

theorem gempty {A} (i) : get i (∅ : PTree A) = none := gleaf i

theorem gss {A} (i x) (m : PTree A) : get i (set i x m) = some x := sorry

theorem gso {A i j} (x : A) (m : PTree A) : i ≠ j → get i (set j x m) = get i m := sorry

theorem gsspec {A} (i j) (x : A) (m : PTree A) :
  get i (set j x m) = if i = j then some x else get i m :=
by { by_cases (i = j); simp [h], rw gss, rw gso _ _ h }

theorem gsident {A} (i : pos_num) (m : PTree A) (v : A) :
  get i m = some v → set i v m = m := sorry

theorem set2 {A} (i : pos_num) (m : PTree A) (v1 v2 : A) :
  set i v2 (set i v1 m) = set i v2 m := sorry

def of_list {A} (l : list (pos_num × A)) : PTree A :=
l.foldl (λ m ⟨k, v⟩, set k v m) ∅

def node' {A} : PTree A → option A → PTree A → PTree A
| leaf none leaf := leaf
| l x r := node l x r

section combine

variables {A B C : Type} (f : option A → option B → option C)

def xcombine_l : PTree A → PTree C
| leaf := leaf
| (node l o r) := node' (xcombine_l l) (f o none) (xcombine_l r)

def xcombine_r : PTree B → PTree C
| leaf := leaf
| (node l o r) := node' (xcombine_r l) (f none o) (xcombine_r r)

def combine : PTree A → PTree B → PTree C
| leaf m2 := xcombine_r f m2
| m1 leaf := xcombine_l f m1
| (node l1 o1 r1) (node l2 o2 r2) := node' (combine l1 l2) (f o1 o2) (combine r1 r2)

theorem combine_commut (f g : option A → option A → option B) :
(∀ i j, f i j = g j i) →
∀ m1 m2, combine f m1 m2 = combine g m2 m1 := sorry

end combine

def xelements {A} : PTree A → pos_num → list (pos_num × A) → list (pos_num × A)
| leaf i k := k
| (node l none r) i k :=
    xelements l (pos_num.bit0 i) (xelements r (pos_num.bit1 i) k)
| (node l (some x) r) i k :=
    xelements l (pos_num.bit0 i)
    ((prev i, x) :: xelements r (pos_num.bit1 i) k)

def elements {A} (m : PTree A) := xelements m pos_num.one []

def xfold {A B} (f : B → pos_num → A → B) : pos_num → PTree A → B → B
| i leaf v := v
| i (node l none r) v :=
  let v1 := xfold (pos_num.bit0 i) l v in
  xfold (pos_num.bit1 i) r v1
| i (node l (some x) r) v :=
  let v1 := xfold (pos_num.bit0 i) l v in
  let v2 := f v1 (pos_num.pred i) x in
  xfold (pos_num.bit1 i) r v2

def fold {A B} (f : B → pos_num → A → B) (m : PTree A) (v : B) :=
xfold f pos_num.one m v

def for_all {A} (m : PTree A) (f : pos_num → A → bool) : bool :=
fold (λ b x a, b && f x a) m tt

notation a `^!` b := get b a

end PTree

end maps