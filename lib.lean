import algebra.ring

instance : has_div ℤ := sorry

def align (n : ℤ) (amount : ℤ) :=
  ((n + amount - 1) / amount) * amount.

lemma align_le (x y) (h : y > 0) : x ≤ align x y := sorry

lemma align_divides (x y : ℤ) (h : y > 0) : y ∣ align x y := sorry

/- Coq types which we don't have -/
def float32 : Type := sorry

def float : Type := sorry

inductive option.rel {A B} (R: A → B → Prop) : option A → option B → Prop
| none : option.rel none none
| some (x y) : R x y → option.rel (some x) (some y)

inductive list.forall2 {A B} (P : A → B → Prop) : list A → list B → Prop
| nil : list.forall2 [] []
| cons {a1 al b1 bl} : P a1 b1 →
  list.forall2 al bl →
  list.forall2 (a1 :: al) (b1 :: bl)
