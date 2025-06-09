import Mathlib.Tactic

-- Let's do some basic tactics exercises.

section rw

/-
In this section, only use the `rw` tactic.
You will also need the following functions: -/
#check mul_comm
#check mul_assoc

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw[<- mul_assoc]
  rw[mul_comm a b]

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw[mul_assoc]
  rw[mul_comm]
  rw[mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw[<- mul_assoc, mul_comm a b, mul_assoc]


example (a b c : ℝ) : a * b * c = b * c * a := by
  rw[mul_comm (b*c) a, mul_assoc]



example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw[mul_comm a (b*c), mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry

example (a b c d e f : ℝ) (h : a * b = c *
 d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw[<- mul_assoc,h,h',mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  sorry

-- For this next exercise, you should also need:
#check sub_self

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  sorry

end rw

section logic

/-
For the following exercises, use the tactics:
- `intro`
- `exact`
- `constructor`
- `left`
- `right`
- `apply`
- `obtain`
- `rcases`
- `rw`
-/

example (P Q R S : Prop) (h : P → R) (h' : Q → S) : P ∧ Q → R ∧ S := by
  sorry

example (α : Type) (P Q : α → Prop) : (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by
  sorry

-- For the next exercise you also need the function
#check le_trans

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  sorry

-- For the next exercise, you can also use `ring`.
-- You will also need the following:
#check add_zero

example (a b : ℝ) : a = b ↔ b - a = 0 := by
 sorry

example (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
 sorry

example (α : Type) (P Q : α → Prop) : (∀ x, P x ∧ Q x) ↔ ((∀ x, Q x) ∧ (∀ x, P x)) := by
 sorry

end logic
