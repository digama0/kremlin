import algebra.ring data.hash_map

meta def exact_dec_trivial : tactic unit := `[exact dec_trivial]

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

def num.bit0 : num → num
| 0 := 0
| (num.pos n) := num.pos (pos_num.bit0 n)

def num.bit1 : num → num
| 0 := 1
| (num.pos n) := num.pos (pos_num.bit1 n)

instance : has_coe pos_num num := ⟨num.pos⟩

instance pos_num.decidable_eq : decidable_eq pos_num := by tactic.mk_dec_eq_instance
instance num.decidable_eq : decidable_eq num := by tactic.mk_dec_eq_instance

def pos_num.lor : pos_num → pos_num → pos_num
| 1                (pos_num.bit0 q) := pos_num.bit1 q
| 1                q                := q
| (pos_num.bit0 p) 1                := pos_num.bit1 p
| p                1                := p
| (pos_num.bit0 p) (pos_num.bit0 q) := pos_num.bit0 (pos_num.lor p q)
| (pos_num.bit0 p) (pos_num.bit1 q) := pos_num.bit1 (pos_num.lor p q)
| (pos_num.bit1 p) (pos_num.bit0 q) := pos_num.bit1 (pos_num.lor p q)
| (pos_num.bit1 p) (pos_num.bit1 q) := pos_num.bit1 (pos_num.lor p q)

def pos_num.land : pos_num → pos_num → num
| 1                (pos_num.bit0 q) := 0
| 1                _                := 1
| (pos_num.bit0 p) 1                := 0
| _                1                := 1
| (pos_num.bit0 p) (pos_num.bit0 q) := num.bit0 (pos_num.land p q)
| (pos_num.bit0 p) (pos_num.bit1 q) := num.bit0 (pos_num.land p q)
| (pos_num.bit1 p) (pos_num.bit0 q) := num.bit0 (pos_num.land p q)
| (pos_num.bit1 p) (pos_num.bit1 q) := num.bit1 (pos_num.land p q)

def pos_num.ldiff : pos_num → pos_num → num
| 1                (pos_num.bit0 q) := 1
| 1                _                := 0
| (pos_num.bit0 p) 1                := pos_num.bit0 p
| (pos_num.bit1 p) 1                := pos_num.bit0 p
| (pos_num.bit0 p) (pos_num.bit0 q) := num.bit0 (pos_num.ldiff p q)
| (pos_num.bit0 p) (pos_num.bit1 q) := num.bit0 (pos_num.ldiff p q)
| (pos_num.bit1 p) (pos_num.bit0 q) := num.bit1 (pos_num.ldiff p q)
| (pos_num.bit1 p) (pos_num.bit1 q) := num.bit0 (pos_num.ldiff p q)

def pos_num.lxor : pos_num → pos_num → num
| 1                1                := 0
| 1                (pos_num.bit0 q) := pos_num.bit1 q
| 1                (pos_num.bit1 q) := pos_num.bit0 q
| (pos_num.bit0 p) 1                := pos_num.bit1 p
| (pos_num.bit1 p) 1                := pos_num.bit0 p
| (pos_num.bit0 p) (pos_num.bit0 q) := num.bit0 (pos_num.lxor p q)
| (pos_num.bit0 p) (pos_num.bit1 q) := num.bit1 (pos_num.lxor p q)
| (pos_num.bit1 p) (pos_num.bit0 q) := num.bit1 (pos_num.lxor p q)
| (pos_num.bit1 p) (pos_num.bit1 q) := num.bit0 (pos_num.lxor p q)

def pos_num.test_bit : pos_num → nat → bool
| 1                0     := tt
| 1                (n+1) := ff
| (pos_num.bit0 p) 0     := ff
| (pos_num.bit0 p) (n+1) := pos_num.test_bit p n
| (pos_num.bit1 p) 0     := tt
| (pos_num.bit1 p) (n+1) := pos_num.test_bit p n

def pos_num.one_bits : pos_num → nat → list nat
| 1                d := [d]
| (pos_num.bit0 p) d := pos_num.one_bits p (d+1)
| (pos_num.bit1 p) d := d :: pos_num.one_bits p (d+1)

lemma pos_num.lor_self (x y) : pos_num.lor (pos_num.lor x y) y = pos_num.lor x y := sorry

def num.size' (a : num) : num :=
num.rec_on a 0 (λ p, pos_num.size p)

def num.lor : num → num → num
| 0           q           := q
| p           0           := p
| (num.pos p) (num.pos q) := pos_num.lor p q

def num.land : num → num → num
| 0           q           := 0
| p           0           := 0
| (num.pos p) (num.pos q) := pos_num.land p q

def num.ldiff : num → num → num
| 0           q           := 0
| p           0           := p
| (num.pos p) (num.pos q) := pos_num.ldiff p q

def num.lxor : num → num → num
| 0           q           := q
| p           0           := p
| (num.pos p) (num.pos q) := pos_num.lxor p q

def num.test_bit : num → nat → bool
| 0           n := ff
| (num.pos p) n := pos_num.test_bit p n

def num.one_bits : num → list nat
| 0           := []
| (num.pos p) := pos_num.one_bits p 0

def pos_num.shiftl (p : pos_num) : nat → pos_num
| 0     := p
| (n+1) := pos_num.bit0 (pos_num.shiftl n)

def num.shiftl : num → nat → num
| 0           n := 0
| (num.pos p) n := num.pos (pos_num.shiftl p n)

def pos_num.shiftr : pos_num → nat → num
| p                0     := 1
| 1                (n+1) := 0
| (pos_num.bit0 p) (n+1) := pos_num.shiftr p n
| (pos_num.bit1 p) (n+1) := pos_num.shiftr p n

def num.shiftr : num → nat → num
| 0           n := 0
| (num.pos p) n := pos_num.shiftr p n

def num.succ' : num → pos_num
| 0           := 1
| (num.pos p) := pos_num.succ p

theorem num.succ'_eq_succ (n : num) : n.succ = num.pos n.succ' := by cases n; refl

def num.of_nat : nat → num
| 0 := 0
| (nat.succ n) := num.succ (num.of_nat n)

instance pos_num_nat_coe : has_coe pos_num nat := ⟨nat.of_pos_num⟩

instance num_nat_coe : has_coe num nat := ⟨nat.of_num⟩

instance nat_num_coe : has_coe nat num := ⟨num.of_nat⟩

theorem nat.of_pos_num_succ : ∀ n, nat.of_pos_num (pos_num.succ n) = nat.succ (nat.of_pos_num n)
| 1                := rfl
| (pos_num.bit0 p) := by simph [pos_num.succ, nat.of_pos_num]
| (pos_num.bit1 p) := by simph [pos_num.succ, nat.of_pos_num];
  change nat.of_pos_num p + 1 + nat.of_pos_num p + 1 =
         nat.of_pos_num p + nat.of_pos_num p + 1 + 1; simp

theorem nat.of_pos_num_succ_coe : ∀ n, (pos_num.succ n : ℕ) = n + 1 := nat.of_pos_num_succ

theorem pos_num.add_one (n : pos_num) : n + 1 = pos_num.succ n := by cases n; refl
theorem pos_num.one_add (n : pos_num) : 1 + n = pos_num.succ n := by cases n; refl

theorem nat.of_pos_num_add : ∀ m n : pos_num, nat.of_pos_num (pos_num.add m n) = nat.of_pos_num m + nat.of_pos_num n
| 1                b                :=
  by rw [show pos_num.add 1 b = _, from pos_num.one_add b, nat.of_pos_num_succ, add_comm]; refl
| a                1                :=
  by rw [show pos_num.add a 1 = _, from pos_num.add_one a, nat.of_pos_num_succ]; refl
| (pos_num.bit0 a) (pos_num.bit0 b) :=
  by simp [pos_num.add, nat.of_pos_num, nat.of_pos_num_add];
  change (_ + _) + (_ + _) = (_ + _) + (_ + _); simp
| (pos_num.bit0 a) (pos_num.bit1 b) :=
  by simp [pos_num.add, nat.of_pos_num, nat.of_pos_num_add, nat.of_pos_num_succ];
  change (_ + _) + (_ + _) + 1 = (_ + _) + (_ + _ + 1); simp
| (pos_num.bit1 a) (pos_num.bit0 b) :=
  by simp [pos_num.add, nat.of_pos_num, nat.of_pos_num_add, nat.of_pos_num_succ];
  change (_ + _) + (_ + _) + 1 = (_ + _) + (_ + _ + 1); simp
| (pos_num.bit1 a) (pos_num.bit1 b) :=
  by simp [pos_num.add, nat.of_pos_num, nat.of_pos_num_add, nat.of_pos_num_succ];
  change (_ + _ + 1) + (_ + _ + 1) = (_ + _ + 1) + (_ + _ + 1); simp

theorem pos_num.add_succ : ∀ (m n : pos_num), m + pos_num.succ n = pos_num.succ (m + n)
| 1                b                := by simp [pos_num.one_add]
| (pos_num.bit0 a) 1                := congr_arg pos_num.bit0 (pos_num.add_one a)
| (pos_num.bit1 a) 1                := congr_arg pos_num.bit1 (pos_num.add_one a)
| (pos_num.bit0 a) (pos_num.bit0 b) := rfl
| (pos_num.bit0 a) (pos_num.bit1 b) := congr_arg pos_num.bit0 (pos_num.add_succ a b)
| (pos_num.bit1 a) (pos_num.bit0 b) := rfl
| (pos_num.bit1 a) (pos_num.bit1 b) := congr_arg pos_num.bit1 (pos_num.add_succ a b)

theorem nat.of_num_add : Π m n, nat.of_num (m + n) = nat.of_num m + nat.of_num n
| 0           0           := rfl
| 0           (num.pos q) := (zero_add _).symm
| (num.pos p) 0           := rfl
| (num.pos p) (num.pos q) := nat.of_pos_num_add _ _

theorem num.add_zero (n : num) : n + 0 = n := by cases n; refl
theorem num.zero_add (n : num) : 0 + n = n := by cases n; refl

theorem num.add_succ : ∀ (m n : num), m + num.succ n = num.succ (m + n)
| 0           n           := by simp [num.zero_add]
| (num.pos p) 0           := show num.pos (p + 1) = num.succ (num.pos p + 0),
                             by rw [pos_num.add_one, num.add_zero]; refl
| (num.pos p) (num.pos q) := congr_arg num.pos (pos_num.add_succ _ _)

theorem nat.of_num_succ : Π (n : num), nat.of_num (num.succ n) = nat.succ (nat.of_num n)
| 0           := rfl
| (num.pos p) := by simp [num.succ, nat.of_num, nat.of_pos_num_succ]

@[simp] theorem nat_of_num_of_nat : Π (n : ℕ), nat.of_num (num.of_nat n) = n
| 0     := rfl
| (n+1) := (nat.of_num_succ (num.of_nat n)).trans (congr_arg nat.succ (nat_of_num_of_nat n))

theorem pos_num.bit0_of_bit0 : Π (n : pos_num), bit0 n = pos_num.bit0 n
| 1                := rfl
| (pos_num.bit0 p) := congr_arg pos_num.bit0 (pos_num.bit0_of_bit0 p)
| (pos_num.bit1 p) := show pos_num.bit0 (pos_num.succ (bit0 p)) = _,
                      by rw pos_num.bit0_of_bit0; refl

theorem pos_num.bit1_of_bit1 (n : pos_num) : bit1 n = pos_num.bit1 n :=
show bit0 n + 1 = pos_num.bit1 n, by rw [pos_num.add_one, pos_num.bit0_of_bit0]; refl

theorem num.of_nat_add (m) : Π (n : ℕ), num.of_nat (m + n) = num.of_nat m + num.of_nat n
| 0     := (num.add_zero _).symm
| (n+1) := show num.succ (num.of_nat (m + n)) = num.of_nat m + num.succ (num.of_nat n),
           by rw [num.add_succ, num.of_nat_add]

@[simp] theorem num_of_nat_of_pos_num : Π (n : pos_num), num.of_nat (nat.of_pos_num n) = num.pos n
| 1                := rfl
| (pos_num.bit0 p) :=
  show num.of_nat (nat.of_pos_num p + nat.of_pos_num p) = num.pos (pos_num.bit0 p),
  by rw [num.of_nat_add, num_of_nat_of_pos_num]; exact congr_arg num.pos p.bit0_of_bit0
| (pos_num.bit1 p) :=
  show num.succ (num.of_nat (nat.of_pos_num p + nat.of_pos_num p)) = num.pos (pos_num.bit1 p),
  by rw [num.of_nat_add, num_of_nat_of_pos_num]; exact congr_arg (num.pos ∘ pos_num.succ) p.bit0_of_bit0

@[simp] theorem num_of_nat_of_num : Π (n : num), num.of_nat (nat.of_num n) = n
| 0           := rfl
| (num.pos p) := num_of_nat_of_pos_num p

@[simp] theorem num_of_nat_of_num_coe : Π (n : num), ((n : ℕ) : num) = n := num_of_nat_of_num

@[simp] theorem nat_of_num_of_nat_coe : Π (n : ℕ), ((n : num) : ℕ) = n := nat_of_num_of_nat

theorem num.of_nat_inj : ∀ {m n}, num.of_nat m = num.of_nat n → m = n :=
function.injective_of_left_inverse nat_of_num_of_nat

theorem nat.of_num_inj : ∀ {m n}, nat.of_num m = nat.of_num n → m = n :=
function.injective_of_left_inverse num_of_nat_of_num

theorem num.of_nat_inj_coe : ∀ {m n : ℕ}, (m : num) = n → m = n :=
function.injective_of_left_inverse nat_of_num_of_nat

theorem nat.of_num_inj_coe : ∀ {m n : num}, (m : ℕ) = n → m = n :=
function.injective_of_left_inverse num_of_nat_of_num

theorem nat.of_pos_num_inj {m n} (h : nat.of_pos_num m = nat.of_pos_num n) : m = n :=
by note := congr_arg num.of_nat h; simp at this; injection this; assumption

theorem nat.of_pos_num_inj_coe {m n : pos_num} : (m : ℕ) = n → m = n := nat.of_pos_num_inj

theorem nat.of_pos_num_pos : ∀ n : pos_num, (n : ℕ) > 0
| 1                := dec_trivial
| (pos_num.bit0 p) := let h := nat.of_pos_num_pos p in add_pos h h
| (pos_num.bit1 p) := nat.succ_pos _

theorem nat.of_pos_num_pred : ∀ n, (pos_num.pred n : ℕ) = cond (pos_num.is_one n) 1 (nat.pred n)
| 1                := rfl
| 2                := rfl
| (pos_num.bit1 q) := rfl
| (pos_num.bit0 q) := have IH : _, from nat.of_pos_num_pred q,
  begin cases q with p p, refl,
    pose q := pos_num.bit1 p, tactic.swap, pose q := pos_num.bit0 p, all_goals {
      change (pos_num.pred q + pos_num.pred q + 1 : ℕ) = nat.pred (q + q),
      rw IH, exact
      calc  nat.succ (nat.pred q + nat.pred q)
          = nat.pred (nat.succ (nat.pred q) + nat.succ (nat.pred q)) : by rw nat.succ_add; refl
      ... = nat.pred (q + q) : by rw nat.succ_pred_eq_of_pos (nat.of_pos_num_pos q) }
  end

theorem nat.of_num_pred : ∀ (n : num), (num.pred n : ℕ) = nat.pred n
| 0                := rfl
| 1                := rfl
| (pos_num.bit0 p) := nat.of_pos_num_pred (pos_num.bit0 p)
| (pos_num.bit1 p) := rfl

theorem nat.of_pos_num_lt' : ∀ (m n : pos_num), to_bool ((m : ℕ) < n) = pos_num.lt m n
| 1                1                := rfl
| 1                (pos_num.bit0 q) :=
  let h : (1:ℕ) ≤ q := nat.of_pos_num_pos q in to_bool_true (add_le_add h h)
| 1                (pos_num.bit1 q) := to_bool_true $ nat.succ_lt_succ $ nat.of_pos_num_pos $ pos_num.bit0 q
| (pos_num.bit0 p) 1                := to_bool_ff $ not_lt_of_ge $ nat.of_pos_num_pos $ pos_num.bit0 p
| (pos_num.bit0 p) (pos_num.bit0 q) :=
  have (p + p : ℕ) < q + q ↔ (p:ℕ) < q, from
  ⟨λh, lt_of_not_ge $ λhn, not_le_of_gt h $ add_le_add hn hn,
   λh, add_lt_add h h⟩,
  eq.trans (to_bool_congr this) (nat.of_pos_num_lt' p q)
| (pos_num.bit0 p) (pos_num.bit1 q) := show _ = pos_num.lt p (pos_num.succ q), from
  have (p + p : ℕ) < q + q + 1 ↔ (p:ℕ) < q + 1, by rw add_assoc; exact
  ⟨λh, lt_of_not_ge $ λhn, not_le_of_gt h $ add_le_add (nat.le_of_lt hn) hn,
   λh, add_lt_add_of_le_of_lt (nat.le_of_lt_succ h) h⟩,
  eq.trans (to_bool_congr (by rw nat.of_pos_num_succ_coe; exact this)) (nat.of_pos_num_lt' p (pos_num.succ q))
| (pos_num.bit1 p) 1                := rfl
| (pos_num.bit1 p) (pos_num.bit0 q) :=
  have (p + p + 1 : ℕ) < q + q ↔ (p:ℕ) < q, by rw add_assoc; exact
  ⟨λh, lt_of_not_ge $ λhn, not_le_of_gt h $ add_le_add hn (nat.le_succ_of_le hn),
   λh, add_lt_add_of_lt_of_le h h⟩,
  eq.trans (to_bool_congr this) (nat.of_pos_num_lt' p q)
| (pos_num.bit1 p) (pos_num.bit1 q) :=
  have (p + p + 1 : ℕ) < q + q + 1 ↔ (p:ℕ) < q, from
  ⟨λh, lt_of_not_ge $ λhn, not_le_of_gt h $ nat.succ_le_succ (add_le_add hn hn),
   λh, nat.succ_lt_succ (add_lt_add h h)⟩,
  eq.trans (to_bool_congr this) (nat.of_pos_num_lt' p q)

instance : has_lt pos_num := ⟨λ m n, pos_num.lt m n⟩
instance : has_le pos_num := ⟨λ m n, pos_num.le m n⟩

theorem nat.of_pos_num_lt {m n : pos_num} : m < n ↔ (m : ℕ) < n :=
show pos_num.lt m n ↔ _, by rw -nat.of_pos_num_lt'; apply to_bool_iff

theorem nat.of_pos_num_le' (m n : pos_num) : to_bool ((m : ℕ) ≤ n) = pos_num.le m n :=
by delta pos_num.le; rw [-nat.of_pos_num_lt', nat.of_pos_num_succ_coe]; exact
to_bool_congr ⟨nat.lt_succ_of_le, nat.le_of_lt_succ⟩

theorem nat.of_pos_num_le {m n : pos_num} : m ≤ n ↔ (m : ℕ) ≤ n :=
show pos_num.le m n ↔ _, by rw -nat.of_pos_num_le'; apply to_bool_iff

theorem nat.of_num_lt' : ∀ (m n : num), to_bool ((m : ℕ) < n) = num.lt m n
| 0           0           := rfl
| 0           (num.pos q) := to_bool_true (nat.of_pos_num_pos q)
| (num.pos p) 0           := rfl
| (num.pos p) (num.pos q) := nat.of_pos_num_lt' p q

instance : has_lt num := ⟨λ m n, num.lt m n⟩
instance : has_le num := ⟨λ m n, num.le m n⟩

theorem nat.of_num_lt {m n : num} : m < n ↔ (m : ℕ) < n :=
show num.lt m n ↔ _, by rw -nat.of_num_lt'; apply to_bool_iff

theorem nat.of_num_le' : ∀ (m n : num), to_bool ((m : ℕ) ≤ n) = num.le m n
| 0           0           := rfl
| 0           (num.pos q) := rfl
| (num.pos p) 0           := to_bool_ff $ not_le_of_gt (nat.of_pos_num_pos p)
| (num.pos p) (num.pos q) := nat.of_pos_num_le' p q

theorem nat.of_num_le {m n : num} : m ≤ n ↔ (m : ℕ) ≤ n :=
show num.le m n ↔ _, by rw -nat.of_num_le'; apply to_bool_iff

-- TODO(Mario): Prove these using transfer tactic
instance : decidable_linear_order pos_num :=
{ lt                         := (<),
  le                         := (≤),
  le_refl                    := λa, nat.of_pos_num_le.2 (le_refl _),
  le_trans                   := λa b c h1 h2, nat.of_pos_num_le.2 $
                                le_trans (nat.of_pos_num_le.1 h1) (nat.of_pos_num_le.1 h2),
  le_antisymm                := λa b h1 h2, nat.of_pos_num_inj_coe $ 
                                le_antisymm (nat.of_pos_num_le.1 h1) (nat.of_pos_num_le.1 h2),
  le_total                   := λa b, (le_total (a:ℕ) b).imp nat.of_pos_num_le.2 nat.of_pos_num_le.2,
  le_iff_lt_or_eq            := λa b, nat.of_pos_num_le.trans $ le_iff_lt_or_eq.trans $
                                or_congr nat.of_pos_num_lt.symm ⟨nat.of_pos_num_inj_coe, congr_arg _⟩,
  lt_irrefl                  := λ a h1, lt_irrefl (a:ℕ) $ nat.of_pos_num_lt.1 h1,
  decidable_lt               := by apply_instance,
  decidable_le               := by apply_instance,
  decidable_eq               := by apply_instance }

instance : decidable_linear_order num :=
{ lt                         := (<),
  le                         := (≤),
  le_refl                    := λa, nat.of_num_le.2 (le_refl _),
  le_trans                   := λa b c h1 h2, nat.of_num_le.2 $
                                le_trans (nat.of_num_le.1 h1) (nat.of_num_le.1 h2),
  le_antisymm                := λa b h1 h2, nat.of_num_inj_coe $ 
                                le_antisymm (nat.of_num_le.1 h1) (nat.of_num_le.1 h2),
  le_total                   := λa b, (le_total (a:ℕ) b).imp nat.of_num_le.2 nat.of_num_le.2,
  le_iff_lt_or_eq            := λa b, nat.of_num_le.trans $ le_iff_lt_or_eq.trans $
                                or_congr nat.of_num_lt.symm ⟨nat.of_num_inj_coe, congr_arg _⟩,
  lt_irrefl                  := λ a h1, lt_irrefl (a:ℕ) $ nat.of_num_lt.1 h1,
  decidable_lt               := by apply_instance,
  decidable_le               := by apply_instance,
  decidable_eq               := by apply_instance }

def nat.lor    (m n : ℕ) : ℕ := num.lor m n
def nat.land   (m n : ℕ) : ℕ := num.land m n
def nat.ldiff  (m n : ℕ) : ℕ := num.ldiff m n
def nat.lxor   (m n : ℕ) : ℕ := num.lxor m n
def nat.shiftl (m n : ℕ) : ℕ := num.shiftl m n
def nat.shiftr (m n : ℕ) : ℕ := num.shiftr m n

def nat.test_bit (m n : ℕ) : bool := num.test_bit m n

def nat.size (n : ℕ) : ℕ := num.size' n

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

def int.lnot : ℤ → ℤ
| (m : ℕ) := -[1+ m]
| -[1+ m] := m

def int.lor : ℤ → ℤ → ℤ
| (m : ℕ) (n : ℕ) := nat.lor m n
| (m : ℕ) -[1+ n] := -[1+ nat.ldiff n m]
| -[1+ m] (n : ℕ) := -[1+ nat.ldiff m n]
| -[1+ m] -[1+ n] := -[1+ nat.land m n]

def int.land : ℤ → ℤ → ℤ
| (m : ℕ) (n : ℕ) := nat.land m n
| (m : ℕ) -[1+ n] := -[1+ nat.ldiff m n]
| -[1+ m] (n : ℕ) := -[1+ nat.ldiff n m]
| -[1+ m] -[1+ n] := -[1+ nat.lor m n]

def int.ldiff : ℤ → ℤ → ℤ
| (m : ℕ) (n : ℕ) := nat.ldiff m n
| (m : ℕ) -[1+ n] := -[1+ nat.lor m n]
| -[1+ m] (n : ℕ) := nat.land m n
| -[1+ m] -[1+ n] := nat.ldiff n m

def int.lxor : ℤ → ℤ → ℤ
| (m : ℕ) (n : ℕ) := nat.lxor m n
| (m : ℕ) -[1+ n] := -[1+ nat.lxor m n]
| -[1+ m] (n : ℕ) := -[1+ nat.lxor m n]
| -[1+ m] -[1+ n] := nat.lxor m n

def int.shiftl : ℤ → ℤ → ℤ
| (m : ℕ) (n : ℕ) := nat.shiftl m n
| (m : ℕ) -[1+ n] := nat.shiftr m (nat.succ n)
| -[1+ m] (n : ℕ) := -[1+ nat.shiftl m n]
| -[1+ m] -[1+ n] := -[1+ nat.shiftr m (nat.succ n)]

def int.shiftr : ℤ → ℤ → ℤ
| (m : ℕ) (n : ℕ) := nat.shiftr m n
| (m : ℕ) -[1+ n] := nat.shiftl m (nat.succ n)
| -[1+ m] (n : ℕ) := -[1+ nat.shiftr m n]
| -[1+ m] -[1+ n] := -[1+ nat.shiftl m (nat.succ n)]

def int.test_bit : ℤ → ℕ → bool
| (m : ℕ) n := nat.test_bit m n
| -[1+ m] n := bnot (nat.test_bit m n)

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

def ordering.swap : ordering → ordering
| ordering.lt := ordering.gt
| ordering.eq := ordering.eq
| ordering.gt := ordering.lt

theorem ordering.swap_swap (o : ordering) : o.swap.swap = o :=
by cases o; refl

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
