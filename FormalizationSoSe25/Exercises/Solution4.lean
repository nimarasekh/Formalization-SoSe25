import Mathlib.Tactic

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
13. `simp` - to simplify terms.
-/

section contradiction
/- In this section we also use `by_contra`. -/

-- This first one should not require `by_contra`.
example (P : Prop) (h : P) : ¬¬P := by
  intro hp
  exact hp h

example (P : Prop) (h : ¬¬P) : P := by
  by_contra hP
  exact h hP

example (P : Prop) : (P → ¬P) → ¬P := by
  intro h hn
  exact h hn hn

-- Let's prove the famous De Morgan's laws.
-- Note these two are harder than the three previous ones.
example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h
    constructor
    · by_contra hP
      apply h
      left
      exact hP
    · by_contra hQ
      apply h
      right
      exact hQ
  · intro h hPQ
    obtain ⟨hnP, hnQ⟩ := h
    rcases hPQ with hP | hQ
    · exact hnP hP
    · exact hnQ hQ

example (P Q : Prop) : ¬ (P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h
    by_contra hPQ
    apply h
    constructor
    · by_contra hP
      apply hPQ
      left
      exact hP
    · by_contra hQ
      apply hPQ
      right
      exact hQ
  · intro h
    intro hPQ
    obtain ⟨hP, hQ⟩ := hPQ
    rcases h with hnP | hnQ
    · exact hnP hP
    · exact hnQ hQ

end contradiction

section indexed_operations

-- For the exercises in this section you will need to use:
#check Set.mem_iUnion
#check Set.mem_inter_iff

/- You can use them directly, but it's probably easier to use:
`simp only [Set.mem_iUnion]`
`simp only [Set.mem_iInter]`
`simp only [Set.mem_inter_iff]`
-/

example {α I : Type} (A : I → Set α)  (s : Set α) : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example {α I : Type} (A B : I → Set α) : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i

example {α I : Type} (A : I → Set α) (s : Set α) : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [Set.mem_union, Set.mem_iInter]
  constructor
  · intro h i
    rcases h with hS | hAi
    · right
      exact hS
    · left
      exact hAi i
  · intro h
    by_cases xs : x ∈ s
    · left
      exact xs
    · right
      intro i
      have hAi : x ∈ A i ∨ x ∈ s := h i
      rcases hAi with hA | hS
      · exact hA
      · exfalso
        exact xs hS

end indexed_operations

section set_theory

example (X : Type ) (a : X) : a ∈ (∅ : Set X) → False := by
  intro h
  exact h


example (X : Type) (A B : Set X) (hAinB : A ⊆ B) : A ∪ B = B := by
  ext b
  constructor
  · intro hAB
    rcases hAB with hA | hB
    · exact hAinB hA
    · exact hB
  · intro hB
    right
    exact hB

example (X : Type) (A B : Set X) (hab : A ∩ B = ∅) : A \ B = A := by
  ext a
  constructor
  · intro hAnB
    obtain ⟨hA, hB⟩ := hAnB
    exact hA
  · intro hA
    constructor
    · exact hA
    · intro xnB
      have hAandB : a ∈ A ∩ B := ⟨hA, xnB⟩
      rw [hab] at hAandB
      exact hAandB


example (X : Type) ( A B C : Set X): A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  ext x
  constructor
  · intro y
    obtain ⟨hA, hBC⟩ := y
    rcases hBC with hB | hC
    · left
      constructor
      · exact hA
      · exact hB
    · right
      constructor
      · exact hA
      · exact hC
  · intro y
    rcases y with hAB | hAC
    · obtain ⟨hA, hB⟩ := hAB
      constructor
      · exact hA
      · left
        exact hB
    · obtain ⟨hA, hC⟩ := hAC
      constructor
      · exact hA
      · right
        exact hC

example  (X : Type) ( A B C : Set X) : (A \ B) \ C = A \ (B ∪ C) := by
  ext x
  constructor
  · intro xabc
    obtain ⟨xamb, xnc⟩ := xabc
    obtain ⟨xa, xnb⟩ := xamb
    constructor
    · exact xa
    · intro xbc
      rcases xbc with xb | xc
      · exact xnb xb
      · exact xnc xc
  · intro xabc
    obtain ⟨xa, xnbc⟩ := xabc
    constructor
    · constructor
      · exact xa
      · intro xnb
        apply xnbc
        left
        exact xnb
    · intro xbc
      apply xnbc
      right
      exact xbc

example (X : Type) ( A B C : Set X) : (A \ B) \ C = A \ (B ∪ C) := by
  ext x
  constructor
  · intro xAnBC
    obtain ⟨xAnB, xnC⟩ := xAnBC
    obtain ⟨xA, xnB⟩ := xAnB
    constructor
    · exact xA
    · intro xBC
      rcases xBC with xB | xC
      · exact xnB xB
      · exact xnC xC
  · intro xAnBnC
    obtain ⟨xA, xnBnC⟩ := xAnBnC
    constructor
    · constructor
      · exact xA
      · intro xB
        apply xnBnC
        left
        exact xB
    · intro xC
      apply xnBnC
      right
      exact xC

end set_theory

section functions_basics

/- The `Empty` type is a type with no elements.
That means if I have `x : Empty`, then `cases x` will close every goal!
Let's prove that every function out of `Empty` is injective. -/
example (X : Type) (f : Empty →  X) : Function.Injective f := by
  intro x y hxy
  cases x

/- The `Unit` type is a type with one element.
That means if `x : Unit`, then `x = Unit.unit`.
We obtain that via `cases x`.
Let's use that to prove that every function out of `Unit` is injective. -/
example (X : Type) (f : Unit →  X) : Function.Injective f := by
  intro x y hxy
  cases x
  cases y
  rfl

-- Recall that if a type `X` is inhabited, then there is a default element `default : X`.
example (X : Type) [Inhabited X] (f : X →  Unit) : Function.Surjective f := by
  intro y
  use default

example (X Y : Type) (A B : Set Y) (f : X → Y) : f ⁻¹' (A ∩ B) = f ⁻¹' A ∩ f ⁻¹' B := by
  ext y
  rfl

example {X Y : Type} {f : X → Y} (A : Set X) (h : Function.Injective f) : f ⁻¹' (f '' A) ⊆ A := by
  intro x hx
  obtain ⟨y, hy⟩ := hx
  obtain ⟨hx, hxy⟩ := hy
  have xy : y = x := by
    apply h
    exact hxy
  rw [← xy]
  exact hx

example {X Y : Type} {f : X → Y} (B : Set Y) : f '' (f ⁻¹' B) ⊆ B := by
  intro y hy
  obtain ⟨x, hx⟩ := hy
  obtain ⟨hx', hxy⟩ := hx
  rw [← hxy]
  exact hx'

example {X Y : Type} {f : X → Y} (B : Set Y) (h : Function.Surjective f) : B ⊆ f '' (f ⁻¹' B) := by
  intro y hy
  obtain ⟨x, hxy⟩ := h y
  use x
  constructor
  · simp
    rw [hxy]
    exact hy
  · exact hxy

example {X Y : Type} {A B : Set X} (f : X → Y) (h : A ⊆ B) : f '' A ⊆ f '' B := by
  intro y hy
  obtain ⟨x, hx⟩ := hy
  obtain ⟨hx', hxy⟩ := hx
  use x
  constructor
  · apply h
    exact hx'
  · exact hxy


example {X Y : Type} {A B : Set Y} (f : X → Y)  (h : A ⊆ B) : f ⁻¹' A ⊆ f ⁻¹' B := by
  intro x hx
  apply h
  exact hx

example {X Y : Type} {A B : Set Y} (f : X → Y) : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B := by
  ext x
  constructor
  · intro hx
    obtain hxA | hxB := hx
    · left
      exact hxA
    · right
      exact hxB
  · intro hx
    obtain hxA | hxB := hx
    · left
      exact hxA
    · right
      exact hxB

example {X Y : Type} {A B : Set X} (f : X → Y) : f '' (A ∩ B) ⊆ f '' A ∩ f '' B := by
  intro y hy
  obtain ⟨x, hx⟩ := hy
  obtain ⟨hxAB, hxy⟩ := hx
  obtain ⟨hxA, hxB⟩ := hxAB
  constructor
  · use x
  · use x

example {X Y : Type} {A B : Set X} (f : X → Y) (h : Function.Injective f) : f '' A ∩ f '' B ⊆ f '' (A ∩ B) := by
  intro y hy
  obtain ⟨hxA, hxB⟩ := hy
  obtain ⟨x₀, hxyA⟩ := hxA
  obtain ⟨x₁, hxyB⟩ := hxB
  obtain ⟨hx₀, hAx₀⟩ := hxyA
  obtain ⟨hx₁, hBx₁⟩ := hxyB
  have hfx01 : f x₀ = f x₁ := by {
    rw [hBx₁]
    exact hAx₀
  }
  have hx01 : x₀ = x₁ := by {
    apply h
    exact hfx01
  }
  use x₀
  constructor
  · constructor
    · exact hx₀
    · rw [hx01]
      exact hx₁
  · rw [hx01]
    exact hBx₁


example {X Y : Type} {A B : Set X} (f : X → Y) : f '' A \ f '' B ⊆ f '' (A \ B) := by
  intro y hy
  obtain ⟨hxA, hxB⟩ := hy
  obtain ⟨x₀, hxyA⟩ := hxA
  obtain ⟨x₁, hxyB⟩ := hxyA
  use x₀
  constructor
  · constructor
    · exact x₁
    · by_contra hhx
      apply hxB
      rw [← hxyB]
      use x₀
  · exact hxyB

example {X Y : Type} {A B : Set Y} (f : X → Y) : f ⁻¹' A \ f ⁻¹' B ⊆ f ⁻¹' (A \ B) := by
  intro x hx
  obtain ⟨hxA, hxB⟩ := hx
  constructor
  · exact hxA
  · by_contra hhx
    apply hxB
    exact hhx

example {X Y : Type} {A : Set X} {B : Set Y} (f : X → Y) : f '' A ∩ B = f '' (A ∩ f ⁻¹' B) := by
  ext y
  constructor
  · intro hy
    obtain ⟨hxA, hxB⟩ := hy
    obtain ⟨x, hxy⟩ := hxA
    obtain ⟨hxxA, hxyB⟩ := hxy
    use x
    constructor
    · constructor
      · exact hxxA
      · simp
        rw [hxyB]
        exact hxB
    · exact hxyB
  · intro hy
    obtain ⟨x, hxB⟩ := hy
    obtain ⟨hxAB, hxy⟩ := hxB
    obtain ⟨hxxA, hxyB⟩ := hxAB
    constructor
    · rw [←  hxy]
      simp
      use x
    · rw [← hxy]
      exact hxyB

example {X Y : Type} {A : Set X} {B : Set Y} (f : X → Y) : f '' (A ∩ f ⁻¹' B) ⊆ f '' A ∩ B := by
  intro y hy
  obtain ⟨x, hxB⟩ := hy
  obtain ⟨xAB, hxy⟩ := hxB
  obtain ⟨hxxA, hxyB⟩ := xAB
  constructor
  · rw [← hxy]
    use x
  · rw [← hxy]
    exact hxyB

example {X Y : Type} {A : Set X} {B : Set Y} (f : X → Y) : A ∩ f ⁻¹' B ⊆ f ⁻¹' (f '' A ∩ B) := by
  intro x hx
  obtain ⟨hxA, hxB⟩ := hx
  constructor
  · use x
  · exact hxB

example {X Y : Type} {A : Set X} {B : Set Y} (f : X → Y) : A ∪ f ⁻¹' B ⊆ f ⁻¹' (f '' A ∪ B) := by
  intro x hx
  rcases hx with hxA | hxB
  · left
    use x
  · right
    exact hxB

end functions_basics


section squares_and_roots
/- For the next exercises we need to know some facts about
squares and square roots.-/
#check Real.sq_sqrt
#check Real.sqrt_sq
#check sq_nonneg

-- You also want to benefit from the `calc` tactic.
example : Set.InjOn Real.sqrt { x | x ≥ 0 } := by
  intro x hx y hy hxy
  calc
   x = (Real.sqrt x)^2 := by rw [Real.sq_sqrt hx]
   _ = (Real.sqrt y)^2 := by rw [hxy]
   _ = y := by rw [Real.sq_sqrt hy]


example : Set.InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x hx y hy hxy
  simp at hx
  simp at hy
  simp at hxy
  calc
    x = Real.sqrt (x^2) := by rw [Real.sqrt_sq hx]
    _ = Real.sqrt (y^2) := by rw [hxy]
    _ = y := by rw [Real.sqrt_sq hy]

example : (Set.range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := hy
    exact sq_nonneg x
  · intro hy
    use Real.sqrt y
    simp
    rw [Real.sq_sqrt]
    exact hy

end squares_and_roots
