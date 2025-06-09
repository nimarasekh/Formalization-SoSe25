import Mathlib.Tactic

-- Let's do some basic tactics exercises.



section logic

/-
For the following exercises, you can use the tactics:
1. `rfl` - to close goals that are literally equal.
2. `rw` - to rewrite terms along equalities.
3. `intro` - to introduce assumptions.
4. `exact` - to provide exact matches for goals.
5. `apply` - to apply functions to goals.
6. `have` - to introduce new assumptions.
7. `constructor` - to prove equivalences and conjunctions.
8. `obtain` - to split assumptions in conjunctions and existential quantifiers.
9. `left` - to prove disjunctions.
10. `right` - to prove disjunctions.
11. `rcases` - to split disjunctions.
12. `use` - to provide witnesses for existential quantifiers.
-/

example (P Q : Prop) : P ∧ Q → Q := by
  intro h
  obtain ⟨hP, hQ⟩ := h
  exact hQ

example (P Q : Prop) : P → P ∨ Q := by
  intro p
  left
  exact p

example (P R Q : Prop) (f : P → Q) (g : Q → R): P → R := by
  intro h
  apply g
  apply f
  exact h


example (P Q R S : Prop) (h : P → R) (h' : Q → S) : P ∧ Q → R ∧ S := by
  intro ⟨hp, hq⟩
  exact ⟨h hp, h' hq⟩

example (P Q R : Prop) (h : P ∧ Q → R) (hp : P) (hq : Q) : R := by
  apply h
  constructor
  · exact hp
  · exact hq

-- The following also requires the function `Nat.zero_le`.
#check Nat.zero_le
example : ∃ n : ℕ, ∀ m : ℕ, (n ≤ m) := by
  use 0
  apply Nat.zero_le

example (X : Type) (P Q : X → Prop) : (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by
  intro ⟨x, hp, hq⟩
  use x


-- Can you solve the next one so that the `use` tactic is used in the last line?
example (X : Type) (x : X) (P : X → Prop) : (∀ x, P x) → ∃ x, P x := by
  intro h
  have h': P x := h x
  use x



-- For the next exercise as part of the proof use `have` to obtain a term in `P ∧ R`.
example (P Q R S T : Prop) (f : P → Q) (g : R → S) (h : Q ∧ S → T) : P ∧ R → T := by
  intro k
  exact h ⟨ (f k.1), (g k.2)⟩

-- For the next exercise you also need the function `le_trans`.
#check le_trans

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  exact le_trans h₀ h₁

-- For the next exercise, you can also use `ring`.
-- You will also need `add_zero`.
#check add_zero

example (a b : ℝ) : a = b ↔ b - a = 0 := by
 constructor
 .  intro h
    rw[h]
    ring
 .  intro h
    rw[<- add_zero a]
    rw[<- h]
    ring
example (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
 sorry

example (X : Type) (P Q : X → Prop) : (∀ x, P x ∧ Q x) ↔ ((∀ x, Q x) ∧ (∀ x, P x)) := by
 sorry

end logic

section evenfunction

def EvenFunction (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

#check EvenFunction

-- For this next exercise you can use `calc`.
example (f g : ℝ → ℝ) (hf : EvenFunction f) : EvenFunction (f + g) ↔ EvenFunction g := by
  sorry

end evenfunction

section min

variable (a b c : ℝ)

-- We have a min function in Lean:
#check min
-- It has various properties:
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

-- You will also need the following facts about inequalities:
#check le_antisymm
#check le_trans

-- Now use those to prove the following.
example : min a b = min b a := by
  sorry

example : min a (min b c) = min (min a b) c := by
  sorry

end min
