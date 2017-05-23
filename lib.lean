import algebra.ring data.hash_map

instance : has_coe ℕ+ ℕ := ⟨λn, n.1⟩

def num.bit0 : num → num
| 0 := 0
| (num.pos n) := num.pos (pos_num.bit0 n)

def num.bit1 : num → num
| 0 := 1
| (num.pos n) := num.pos (pos_num.bit1 n)

instance : has_coe pos_num num := ⟨num.pos⟩

instance pos_num.decidable_eq : decidable_eq pos_num := by tactic.mk_dec_eq_instance

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

def num.of_nat : nat → num
| 0 := 0
| (nat.succ n) := num.succ (num.of_nat n)

instance pos_num_nat_coe : has_coe pos_num nat := ⟨nat.of_pos_num⟩

instance num_nat_coe : has_coe num nat := ⟨nat.of_num⟩

instance nat_num_coe : has_coe nat num := ⟨num.of_nat⟩

def nat.lor    (m n : ℕ) : ℕ := num.lor m n 
def nat.land   (m n : ℕ) : ℕ := num.land m n 
def nat.ldiff  (m n : ℕ) : ℕ := num.ldiff m n 
def nat.lxor   (m n : ℕ) : ℕ := num.lxor m n 
def nat.shiftl (m n : ℕ) : ℕ := num.shiftl m n 
def nat.shiftr (m n : ℕ) : ℕ := num.shiftr m n 

def nat.test_bit (m n : ℕ) : bool := num.test_bit m n 

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

def fin.of_int {n} : ℤ → fin (nat.succ n)
| (m : ℕ) := fin.of_nat m
| -[1+ m] := ⟨n - m % (nat.succ n), nat.lt_succ_of_le (nat.sub_le _ _)⟩

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

def int.mod : ℤ → ℤ → ℤ
| (m : ℕ) (n : ℕ) := (m % n : ℕ)
| 0       -[1+ n] := 0
| (m+1:ℕ) -[1+ n] := -(n - m % nat.succ n : ℕ)
| -[1+ m] (n : ℕ) := n - nat.succ (m % n)
| -[1+ m] -[1+ n] := -(nat.succ m % nat.succ n : ℕ)

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
