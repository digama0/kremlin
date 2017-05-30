import algebra.ring data.hash_map data.num.lemmas

instance : has_coe ℕ+ ℕ := ⟨λn, n.1⟩

theorem to_bool_iff (p : Prop) [d : decidable p] : to_bool p ↔ p :=
match d with
| is_true hp := ⟨λh, hp, λ_, rfl⟩
| is_false hnp := ⟨λh, bool.no_confusion h, λhp, absurd hp hnp⟩
end

theorem to_bool_true {p : Prop} [decidable p] : p → to_bool p := (to_bool_iff p).2

theorem to_bool_tt {p : Prop} [decidable p] : p → to_bool p = tt := to_bool_true

theorem of_to_bool_true {p : Prop} [decidable p] : to_bool p → p := (to_bool_iff p).1

theorem bool_iff_false {b : bool} : ¬ b ↔ b = ff := by cases b; exact dec_trivial

theorem bool_eq_false {b : bool} : ¬ b → b = ff := bool_iff_false.1

theorem to_bool_ff_iff (p : Prop) [decidable p] : to_bool p = ff ↔ ¬p :=
bool_iff_false.symm.trans (not_congr (to_bool_iff _))

theorem to_bool_ff {p : Prop} [decidable p] : ¬p → to_bool p = ff := (to_bool_ff_iff p).2

theorem of_to_bool_ff {p : Prop} [decidable p] : to_bool p = ff → ¬p := (to_bool_ff_iff p).1

theorem to_bool_congr {p q : Prop} [decidable p] [decidable q] (h : p ↔ q) : to_bool p = to_bool q :=
begin
  ginduction to_bool q with h',
  exact to_bool_ff (mt h.1 $ of_to_bool_ff h'),
  exact to_bool_true (h.2 $ of_to_bool_true h') 
end

theorem bor_iff (a b : bool) : a || b ↔ a ∨ b :=
by cases a; cases b; exact dec_trivial

theorem band_iff (a b : bool) : a && b ↔ a ∧ b :=
by cases a; cases b; exact dec_trivial

theorem bxor_iff (a b : bool) : bxor a b ↔ xor a b :=
by cases a; cases b; exact dec_trivial

lemma pos_num.lor_self (x y) : pos_num.lor (pos_num.lor x y) y = pos_num.lor x y := sorry

lemma nat.test_bit_size {x} : 0 < x → nat.test_bit x (nat.size x - 1) := sorry

lemma nat.test_bit_size_lt {x i} : nat.test_bit x i → i < nat.size x := sorry

lemma nat.lt_pow_size (x) : x < 2^nat.size x := sorry

lemma nat.size_le_of_lt_pow {x n} : x < 2^n → nat.size x ≤ n := sorry

lemma nat.size_monotone {x y} : x ≤ y → nat.size x ≤ nat.size y := sorry

def powerseries : list ℕ → ℕ
| [] := 0
| (x :: xs) := 2^x + powerseries xs

lemma one_bits_powerseries (x) : powerseries (num.one_bits x) = x :=
sorry

lemma mem_one_bits (x i) : i ∈ num.one_bits x ↔ num.test_bit x i :=
sorry

def int.quot : ℤ → ℤ → ℤ
| (m : ℕ) (n : ℕ) := (m / n : ℕ)
| (m : ℕ) -[1+ n] := -(m / nat.succ n : ℕ)
| -[1+ m] (n : ℕ) := -(nat.succ m / n : ℕ)
| -[1+ m] -[1+ n] := (nat.succ m / nat.succ n : ℕ)

def int.rem : ℤ → ℤ → ℤ
| (m : ℕ) (n : ℕ) := (m % n : ℕ)
| (m : ℕ) -[1+ n] := (m % nat.succ n : ℕ)
| -[1+ m] (n : ℕ) := -(nat.succ m % n : ℕ)
| -[1+ m] -[1+ n] := -(nat.succ m % nat.succ n : ℕ)

def int.div : ℤ → ℤ → ℤ
| (m : ℕ) (n : ℕ) := (m / n : ℕ)
| (m : ℕ) -[1+ n] := -(m / nat.succ n : ℕ)
| -[1+ m] (n : ℕ) := -(nat.succ m / n : ℕ)
| -[1+ m] -[1+ n] := (nat.succ m / nat.succ n : ℕ)

def int.nat_mod : ℤ → ℕ → ℕ
| (m : ℕ) n := m % n
| -[1+ m] n := n - nat.succ (m % n)

def int.mod : ℤ → ℤ → ℤ
| m (n : ℕ) := int.nat_mod m n
| m -[1+ n] := int.nat_mod (-m) (nat.succ n)

instance : has_div ℤ := ⟨int.div⟩
instance : has_mod ℤ := ⟨int.mod⟩

lemma int.shiftr_div_two_p (x) (n : ℕ) : int.shiftr x n = x / 2^n := sorry

lemma int.testbit_mod_two_p (n x i) : int.test_bit (x % 2^n) i =
  if i < n then int.test_bit x i else ff := sorry

theorem Ztestbit_two_p_m1 (n i) : int.test_bit (2^n - 1) i = to_bool (i < n) := sorry

def align (n : ℤ) (amount : ℤ) :=
  ((n + amount - 1) / amount) * amount.

lemma align_le (x y) (h : y > 0) : x ≤ align x y := sorry

lemma align_dvd (x y : ℤ) (h : y > 0) : y ∣ align x y := sorry

inductive option.rel {A B} (R: A → B → Prop) : option A → option B → Prop
| none : option.rel none none
| some (x y) : R x y → option.rel (some x) (some y)

inductive list.forall2 {A B} (P : A → B → Prop) : list A → list B → Prop
| nil : list.forall2 [] []
| cons {a1 al b1 bl} : P a1 b1 →
  list.forall2 al bl →
  list.forall2 (a1 :: al) (b1 :: bl)

theorem list.forall2.imp {A} {P Q : A → A → Prop} (H : ∀ x y, P x y → Q x y)
  {l1 l2} (al : list.forall2 P l1 l2) : list.forall2 Q l1 l2 :=
by induction al; constructor; try {assumption}; apply H; assumption

theorem list.forall2.iff {A} {P Q : A → A → Prop} (H : ∀ x y, P x y ↔ Q x y)
  {l1 l2} : list.forall2 P l1 l2 ↔ list.forall2 Q l1 l2 :=
⟨λh, h.imp (λx y, (H x y).1), λh, h.imp (λx y, (H x y).2)⟩

theorem list.forall2.trans {A} {P : A → A → Prop} (t : transitive P) : transitive (list.forall2 P) :=
begin
  intros x y z h12, revert z,
  induction h12 with a1 l1 a2 l2 p12 al12 IH; intros z h23,
  assumption,
  cases h23 with _ _ a3 l3 p23 al23,
  constructor,
  exact t p12 p23,
  exact IH al23
end

/- * Comparisons -/

inductive comparison : Type
| Ceq : comparison    /- same -/
| Cne : comparison    /- different -/
| Clt : comparison    /- less than -/
| Cle : comparison    /- less than or equal -/
| Cgt : comparison    /- greater than -/
| Cge : comparison    /- greater than or equal -/
export comparison

def negate_comparison : comparison → comparison
| Ceq := Cne
| Cne := Ceq
| Clt := Cge
| Cle := Cgt
| Cgt := Cle
| Cge := Clt

def swap_comparison : comparison → comparison
| Ceq := Ceq
| Cne := Cne
| Clt := Cgt
| Cle := Cge
| Cgt := Clt
| Cge := Cle
