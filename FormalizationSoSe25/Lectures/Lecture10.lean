import Mathlib.Tactic

/-
Last time we did a little algebra.

Let us summarize what we have done so far, and what remains to be done.
-/

section WhatShouldYouDo?
/-
There is no lecture on `04.07.2025`, however, there is homework.

Until `04.07.2025` send me an email with the following 3 information:
- What you have formalized until the moment of the email.
- A realistic assessment of the amount you will formalize until your talk on `18.07.2025`.
- An overview of the talk you aim to give. It should run around 15 minutes.
 * What tools will you use?
 * What mathematics will you talk about?
 * A breakdown of the talk.

If I don't receive an email until `04.07.2025`, you will have failed this course.
-/

end WhatShouldYouDo?

section WhatWeLearned
/-
This semester we learned about the proof assistant `Lean 4`.
We covered the following topics:
- The internal logic of proof assistants (mathematics and logic on the same level).
- The syntax of `Lean 4`.
- The tactics of `Lean 4`.
- The library of `Lean 4` (Mathlib).
- Structures, classes, instances in `Lean 4`.
-/
end WhatWeLearned


section tactics
/-
Here is a list of tactics we saw this semester:

1. `rfl` - to close goals that are literally equal.
2. `rw` - to rewrite terms along equalities.
3. `intro` - to introduce assumptions.
4. `revert` - to revert assumptions and goals, opposite to `intro`.
5. `exact` - to provide exact matches for goals.
6. `apply` - to apply functions to goals.
7. `have` - to introduce new assumptions.
8. `let` - similar to `have`, but for defining new variables.
9. `constructor` - to prove equivalences and conjunctions.
10. `rcases` - to split disjunctions.
11. `obtain` - to split assumptions in conjunctions and existential quantifiers.
12. `rintro` - to introduce assumption directly with `rcases`
13. `left` - to prove the left side of the disjunction.
14. `right` - to prove the right side of the disjunction.
15. `use` - to provide witnesses for existential quantifiers.
16. `specialize` - to specialize a function to a particular input.
17. `calc` - to do calculations step by step.
18. `linarith` - to solve linear inequalities and contradictions.
19. `norm_num` - to solve numerical equations.
20. `decide` - to solve decidable propositions.
21. `tauto` - to solve tautologies.
22. `ext` - to prove equalities of sets and functions via extensionality.
23. `norm_cast` - to normalize expressions with casts.
24. `simp` - to simplify expressions.
25. `simp only` - to simplify expressions with specific rules.
26. `assumption` - to close goals with existing assumptions.
27. `refine` - to break down goals into smaller steps.
28. `unfold` - to unfold definitions.
29. `induction` - to perform induction on natural numbers or other inductive types.
30. `induction'` - alternative version for induction
31. `cases` - to perform case analysis on inductive types.
32. `by_cases` - to perform case by case analysis on propositions.
33. `exfalso` - replaces the goal with `false`
34. `by_contra` - to prove by contradiction.
35. `contradiction` - to deduce a contradiction from assumptions.
36. `group` - to solve group-theoretic equations.
37. `abel` - to solve abelian group equations.
38. `noncomm_ring` - to solve non-commutative ring equations.
39. `ring` - to simplify computational expressions in rings.
40. `field_simp` - to simplify expressions in fields, especially with divisions.
-/

end tactics

section mathematics
/-
Here is some mathematics we saw this semester:
- Logic:
  * Propositional logic, quantifiers.
  * Proofs by contradiction, contraposition,
  * Logical equivalences, De Morgan's laws.
  * Proof by induction
- Set theory:
  * Sets, unions, intersections, complements, subsets.
  * Finite and infinite sets.
  * Functions, injective, surjective, bijective functions, image, preimage.
  * Axiom of choice
- Algebra:
  * Groups, rings, fields, vector spaces.
  * Homomorphisms, isomorphisms.
  * Subgroups, normal subgroups, ideals, quotients
- Number theory:
  * Natural numbers, integers, rational numbers
  * Divisibility, prime numbers, greatest common divisor.
  * Non-rationality of square roots, infinite primes

All of this and many more topics are available in `Mathlib`.
-/

end mathematics

section structures
/-
In order to develop mathematics in Lean, we need `structures`.
-/
structure MyStructure where
  (x : Nat)
  (y : Nat)
  (z : Nat)

def myStructure : MyStructure where
  x := 1
  y := 2
  z := 3
/-
A variation of structures are `classes`.
Classes are structures with a special property:
they can be used to define instances.
-/
class MyClass where
  (x : Nat)
  (y : Nat)
  (z : Nat)

instance myClassInstance : MyClass where
  x := 1
  y := 2
  z := 3

/-
Using `classes` and `instances` we can define every interesting
mathematical structure and concept.
-/
end structures

section Analysis
/-
I did not talk about analysis and topology throughout. Why not?

Topological spaces are easy to define in this setting.
-/
#check TopologicalSpace
#check MetricSpace

variable (X : Type) [topX : TopologicalSpace X]

#check topX.IsOpen

/-
But a first concept one wants is continuity and convergence.
-/

#check Continuous

#print continuous_def
#print Metric.continuous_iff

example (X : Type*) [MetricSpace X] : Continuous (fun x : X => x) := by
  apply continuous_def.2
  intro U hU
  simp
  exact hU

/-
Convergence relies on the notion of filters.
So a careful study requires some actual mathematics.
-/
#check Filter.Tendsto

example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Filter.Tendsto f F G) (hg : Filter.Tendsto g G H) : Filter.Tendsto (g ∘ f) F H :=
  Filter.Tendsto.comp hg hf

end Analysis
