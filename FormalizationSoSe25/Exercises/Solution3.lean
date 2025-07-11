import Mathlib.Tactic
import FormalizationSoSe25.Exercises.Exercise3

-- Let's do some basic tactics exercises.

/-
For the following exercises, use the tactics:
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

section logic

example (P Q : Prop) : P ∧ Q → Q := by
  intro hpq
  exact hpq.2

example (P Q : Prop) : P → P ∨ Q := by
  intro hp
  left
  exact hp

example (P R Q : Prop) (f : P → Q) (g : Q → R): P → R := by
  intro p
  exact g (f p)

example (P Q R S : Prop) (h : P → R) (h' : Q → S) : P ∧ Q → R ∧ S := by
  intro hpq
  obtain ⟨hp, hq⟩ := hpq
  constructor
  · exact h hp
  · exact h' hq

-- The following also requires the function `Nat.zero_le`.
#check Nat.zero_le
example : ∃ n : ℕ, ∀ m : ℕ, (n ≤ m) := by
  use 0
  intro m
  apply Nat.zero_le

example (X : Type) (P Q : X → Prop) : (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩

-- Can you solve the next one so that the `use` tactic is used in the last line?
example (X : Type) (x : X) (P : X → Prop) : (∀ x, P x) → ∃ x, P x := by
  intro f
  have h := f x
  use x

-- For the next exercise as part of the proof use `have` to obtain a term in `P ∧ R`.
example (P Q R S T : Prop) (f : P → Q) (g : R → S) (h : Q ∧ S → T) : P ∧ R → T := by
  intro hpq
  obtain ⟨p, r⟩ := hpq
  have qs : Q ∧ S := by {
    constructor
    · exact (f p)
    · exact (g r)
    }
  exact h qs

-- For the next exercise you also need the function `le_trans`.
#check le_trans

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  · apply h₁

-- For the next exercise, you can also use `ring`.
-- You will also need the `add_zero`.
#check add_zero

example (a b : ℝ) : a = b ↔ b - a = 0 := by
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    rw [← add_zero a]
    rw [← h]
    ring

-- For the next exercise you can also use `linarith`.
example (a b c : ℝ) : a + b ≤ c ↔ a ≤ c - b := by
  constructor
  · intro
    linarith
  · intro
    linarith

example (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  apply Iff.intro
  · intro h
    obtain ⟨hP, hQ | hR⟩ := h
    · left
      constructor
      · exact hP
      · exact hQ
    · right
      constructor
      · exact hP
      · exact hR
  · intro h
    rcases h with hPQ | hPR
    · obtain ⟨hP, hQ⟩ := hPQ
      constructor
      · exact hP
      · left
        exact hQ
    · obtain ⟨hP, hR⟩ := hPR
      constructor
      · exact hP
      · right
        exact hR

example (X : Type) (P Q : X → Prop) : (∀ x, P x ∧ Q x) ↔ ((∀ x, Q x) ∧ (∀ x, P x)) := by
  constructor
  · intro h
    constructor
    · intro x
      obtain ⟨_ , hQ⟩ := h x
      exact hQ
    · intro x
      obtain ⟨hP, _ ⟩ := h x
      exact hP
  · intro h
    intro x
    obtain ⟨hQ, hP⟩ := h
    constructor
    · exact hP x
    · exact hQ x

end logic

section evenfunction

#check EvenFunction

-- For this next exercise you can use `simp` and `calc`.
example (f g : ℝ → ℝ) (hf : EvenFunction f) : EvenFunction (f + g) ↔ EvenFunction g := by
  constructor
  · intro hfg x
    have hfg' : (f  + g) x = (f  + g) ( -x ) := by rw [hfg x]
    simp at hfg'
    calc
      g x = f x + g x - f x := by ring
      _ = (f (-x) + g (-x)) - f (-x) := by rw [hfg', hf x]
      _ = g (-x) := by ring
  · intro hg x
    simp
    rw [hf, hg]


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
example : min a b = min b a := by {
  apply le_antisymm
  · apply le_min
    · exact min_le_right a b
    · exact min_le_left a b
  · apply le_min
    · exact min_le_right b a
    · exact min_le_left b a
  }

example : min a (min b c) = min (min a b) c := by {
  apply le_antisymm
  · apply le_min
    apply le_min
    · apply min_le_left
    · apply le_trans (?_ : min a (min b c) ≤ min b c) (?_ : min b c ≤ b)
      apply min_le_right
      apply min_le_left
    apply le_trans ?_ (?_ : min b c ≤ c)
    apply min_le_right
    apply min_le_right
  apply le_min
  · apply le_trans (b := min a b)
    apply min_le_left
    apply min_le_left
  apply le_min
  · apply @le_trans _ _ _ (min a b)
    apply min_le_left
    apply min_le_right
  apply min_le_right
  }

  end min
