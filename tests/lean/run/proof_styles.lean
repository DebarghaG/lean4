/-!
# Five Different Proof Styles in Lean 4

This file demonstrates five different approaches to proving mathematical facts,
showcasing various proof techniques available in Lean's core library.
-/

/-! ## Style 1: Using `omega` for arithmetic

The `omega` tactic solves linear arithmetic over integers and naturals.
-/

-- Basic inequalities
theorem basic_ineq (n : Nat) : n ≤ n + 1 := by omega

theorem add_comm_nat (a b : Nat) : a + b = b + a := by omega

theorem add_assoc_nat (a b c : Nat) : (a + b) + c = a + (b + c) := by omega

-- Trichotomy
theorem trichotomy (a b : Int) : a < b ∨ a = b ∨ a > b := by omega

-- Sum bounds
theorem sum_bound (a b : Nat) (ha : a ≤ 10) (hb : b ≤ 10) : a + b ≤ 20 := by omega

-- Average is between min and max
theorem avg_bound (a b : Int) (h : a ≤ b) : a ≤ (a + b) / 2 ∧ (a + b) / 2 ≤ b := by
  constructor <;> omega

/-! ## Style 2: Using `simp` for simplification

The `simp` tactic uses rewrite rules to simplify expressions.
-/

-- List operations
theorem list_append_nil (l : List α) : l ++ [] = l := by simp

theorem list_length_append (l1 l2 : List α) : (l1 ++ l2).length = l1.length + l2.length := by
  simp [List.length_append]

theorem list_reverse_reverse (l : List α) : l.reverse.reverse = l := by simp

-- Option operations
theorem option_map_some (f : α → β) (a : α) : Option.map f (some a) = some (f a) := by simp

theorem option_bind_some (a : α) (f : α → Option β) : (some a).bind f = f a := by simp

-- Boolean logic
theorem bool_and_true (b : Bool) : (b && true) = b := by
  cases b <;> native_decide

theorem bool_or_false (b : Bool) : (b || false) = b := by
  cases b <;> native_decide

/-! ## Style 3: Term-mode proofs (direct proof terms)

These proofs construct the proof term directly without tactics.
-/

-- Transitivity of equality (term mode)
theorem trans_eq {α : Type} {a b c : α} (hab : a = b) (hbc : b = c) : a = c :=
  hbc ▸ hab

-- Symmetry of equality (term mode)
theorem symm_eq {α : Type} {a b : α} (h : a = b) : b = a :=
  h ▸ rfl

-- Congruence: if a = b then f a = f b (term mode)
theorem congr_arg' {α β : Type} (f : α → β) {a b : α} (h : a = b) : f a = f b :=
  h ▸ rfl

-- Modus ponens (term mode)
theorem modus_ponens {P Q : Prop} (hpq : P → Q) (hp : P) : Q :=
  hpq hp

-- And introduction (term mode)
theorem and_intro {P Q : Prop} (hp : P) (hq : Q) : P ∧ Q :=
  ⟨hp, hq⟩

-- Or introduction left (term mode)
theorem or_intro_left {P : Prop} (Q : Prop) (hp : P) : P ∨ Q :=
  Or.inl hp

-- Or introduction right (term mode)
theorem or_intro_right (P : Prop) {Q : Prop} (hq : Q) : P ∨ Q :=
  Or.inr hq

-- Implication chain (term mode)
theorem imp_trans {P Q R : Prop} (hpq : P → Q) (hqr : Q → R) : P → R :=
  fun hp => hqr (hpq hp)

/-! ## Style 4: Using `decide` for decidable propositions

The `decide` tactic works for propositions that can be computed.
-/

-- Concrete numeric facts
theorem two_plus_two : 2 + 2 = 4 := by decide

theorem three_lt_five : 3 < 5 := by decide

theorem ten_mod_three : 10 % 3 = 1 := by decide

theorem pow_example : 2^10 = 1024 := by native_decide

-- Boolean facts
theorem bool_example : (true && false) = false := by decide

theorem nat_beq_example : (5 == 5) = true := by native_decide

/-! ## Style 5: Induction proofs

Proving properties about recursive structures using induction.
-/

-- Sum of first n naturals
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

-- 2 * sumTo n = n * (n + 1)
theorem sum_formula (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumTo]
    -- Need to show: 2 * ((n+1) + sumTo n) = (n+1) * (n+2)
    -- From ih: 2 * sumTo n = n * (n + 1)
    have h1 : 2 * (n + 1 + sumTo n) = 2 * (n + 1) + 2 * sumTo n := Nat.mul_add 2 (n+1) (sumTo n)
    rw [h1, ih]
    -- Now: 2 * (n + 1) + n * (n + 1) = (n + 1) * (n + 2)
    have h2 : 2 * (n + 1) + n * (n + 1) = (2 + n) * (n + 1) := by
      rw [Nat.add_mul]
    rw [h2, Nat.mul_comm, Nat.add_comm 2 n]

-- Length of replicated list
theorem replicate_length (n : Nat) (a : α) : (List.replicate n a).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate, ih]

-- Power of 2 is always positive
def pow2 : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * pow2 n

theorem pow2_pos (n : Nat) : pow2 n ≥ 1 := by
  induction n with
  | zero => simp [pow2]
  | succ n ih =>
    unfold pow2
    omega

-- 2^n > n for all n
theorem pow2_gt (n : Nat) : pow2 n > n := by
  induction n with
  | zero => simp [pow2]
  | succ n ih =>
    unfold pow2
    have h := pow2_pos n
    omega

-- Append is associative (by induction on first list)
theorem append_assoc (l1 l2 l3 : List α) : (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) := by
  induction l1 with
  | nil => rfl
  | cons h t ih => simp [ih]

-- Reverse distributes over append
theorem reverse_append (l1 l2 : List α) : (l1 ++ l2).reverse = l2.reverse ++ l1.reverse := by
  induction l1 with
  | nil => simp
  | cons h t ih => simp [ih]

/-! ## Bonus: Combining styles -/

-- A number is either even or odd
theorem even_or_odd (n : Nat) : (∃ k, n = 2 * k) ∨ (∃ k, n = 2 * k + 1) := by
  induction n with
  | zero => left; exact ⟨0, rfl⟩
  | succ n ih =>
    cases ih with
    | inl h =>
      right
      obtain ⟨k, hk⟩ := h
      exact ⟨k, by omega⟩
    | inr h =>
      left
      obtain ⟨k, hk⟩ := h
      exact ⟨k + 1, by omega⟩

-- If n is even, n+1 is odd (and vice versa)
theorem even_succ_odd (n : Nat) (h : ∃ k, n = 2 * k) : ∃ k, n + 1 = 2 * k + 1 := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by omega⟩

theorem odd_succ_even (n : Nat) (h : ∃ k, n = 2 * k + 1) : ∃ k, n + 1 = 2 * k := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by omega⟩

-- Every natural number squared plus itself is even
theorem sq_plus_n_even (n : Nat) : ∃ k, n * n + n = 2 * k := by
  -- n² + n = n(n+1), and consecutive numbers include an even
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    -- (n+1)² + (n+1) = n² + 2n + 1 + n + 1 = n² + n + 2(n+1)
    obtain ⟨k, hk⟩ := ih
    -- Goal: ∃ k, (n+1)*(n+1) + (n+1) = 2*k
    -- (n+1)*(n+1) + (n+1) = (n+1)*(n+2) = (n+1)*n + (n+1)*2 = n*n + n + 2*(n+1)
    refine ⟨k + n + 1, ?_⟩
    -- Simplify (n+1)*(n+1) + (n+1)
    have expand : (n + 1) * (n + 1) + (n + 1) = n * n + n + 2 * (n + 1) := by
      simp [Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.mul_comm]
      omega
    rw [expand, hk]
    omega
