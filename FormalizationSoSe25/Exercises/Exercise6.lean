import Mathlib.Tactic
import FormalizationSoSe25.Lectures.Lecture6

section group_five
/-
In the `Lecture6.lean` we defined `Group₄` as a particular group structure.
-/
#check Group₄

-- Here is a different group structure.
class Group₅ (G : Type*) extends Monoid₁ G, Inv₁ G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙

export Group₅ (inv_dia)

/-
We want to see that although `Group₅` seems weaker than `Group₄`, we can actually
recover the original definition.
-/


/-
Let's start with the easy case.
Show that every `Group₄` gives us a `Group₅`.
Here you probably want to use `Group₅.mk`.
-/

#check Group₅.mk
def group4_to_group5 {G : Type*} [Group₄ G] : Group₅ G :=
  Group₅.mk (Group₄.inv_dia)


/-
Now, we also go the other way around.
This requires some lemmas.

These two lemmas should be provable using only:
- `rw`
- `exact`
- `have`
and the structure of `Monoid₁` and `Group₅`.
-/


lemma equal_inverses {M : Type*} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  sorry


lemma dia_inv' {G: Type*} [Group₅ G] (a : G) : a ⋄ a⁻¹ = 𝟙 := by
  sorry

/-
Now, use this last lemma to go from `Group₅` to `Group₄`.
Here you probably want to use `Group₄.mk`.
-/
def group5_to_group4 {G : Type*} [Group₅ G] : Group₄ G := sorry

/-
Let us end this by observing that the two constructions are inverse to each other.
-/
lemma group4_to_group5_to_group4 {G : Type*} [h : Group₄ G] : @group5_to_group4 G (@group4_to_group5 G h) = h  := by
 sorry

lemma group5_to_group4_to_group5 {G : Type*} [h : Group₅ G] : @group4_to_group5 G (@group5_to_group4 G h) = h  := by
  sorry

end group_five

section ordered_monoid
/-
Let us now try to make new structures.
We go step by step.

First we define a new structure `LE₁` that defines a relation on a type `α`.
-/

class LE₁ (α : Type) where
  /-- The Less-or-Equal relation. -/
  le : α → α → Prop

@[inherit_doc] infix:50 " ≤₁ " => LE₁.le

/-
Your job is now to slowly define and extend from here:

Recall a preorder is a relation on a type that is reflexive and transitive.
- Reflexivity means that for all `a`, `a ≤ a`.
- Transitivity means that for all `a`, `b`, `c`, if `a ≤ b` and `b ≤ c` then `a ≤ c`.

Define a class called `Preorder₁` that extends `LE₁` with these two properties.
They should be named and have the following docstrings:
- `refl` should have the docstring "The reflexivity property."
- `trans` should have the docstring "The transitivity property."
-/

/- DELETE THIS FILL ANSWER HERE-/

/-
A partial order is a preorder with the additional property of antisymmetry.
- Antisymmetry means that for all `a`, `b`, if `a ≤ b` and `b ≤ a` then `a = b`.

Define a class called `PartialOrder₁` that extends `Preorder₁` with this property.
It should be named `antisymm` and have the docstring "The antisymmetry property.".
-/

/- DELETE THIS FILL ANSWER HERE-/

/-
We now bring in some algebraic structure.
We have already defined `Monoid₁` in the lecture.
-/

#check Monoid₁

/-
A commutative monoid is a monoid with the additional property of commutativity.
- Commutativity means that for all `a`, `b`, `a ⋄ b = b ⋄ a`.

Define a class called `CommMonoid₁` that extends `Monoid₁` with this property.
It should be named `dia_comm` and have the docstring "Diamond is commutative."
-/

/- DELETE THIS FILL ANSWER HERE-/

/-
We now combine the two structures into one.
An ordered commutative monoid is a structure that is a
commutative monoid and also a partial order, with the following property:
- For all `a`, `b`, `c`, if `a ≤ b` then `a ⋄ c ≤ b ⋄ c`.
This means that the multiplication is compatible with the order.

Define a class called `OrderedCommMonoid₁` that extends `PartialOrder₁` and `CommMonoid₁`
 with this property. It should be named `le_mul_left₁` and have the docstring
"The multiplication is compatible with the order."
-/

/- DELETE THIS FILL ANSWER HERE-/

/-
The class `OrderedCommMonoid₁` has many new properties.
`export` all of them.
-/

/- DELETE THIS FILL ANSWER HERE-/

/-
Now we want to prove some about ordered commutative monoids.

Write a lemma called `le_mul_right₁` that states
- for all `a`, `b`, `c`, if `a ≤₁ b` then `c ⋄ a ≤₁ c ⋄ b`.

Here:
- There should be an implicit type `α` in `Type*`.
- `OrderedCommMonoid₁` should be a typeclass.
- `a`, `b`, `c` should be of type `α` and also implicit.
- There should only be an explicit hypothesis named `h` that `a ≤₁ b`.

Now prove it!
Again, this should be provable using only `rw`, `apply` and `exact`,
and the properties of `OrderedCommMonoid₁`.
-/

/- DELETE THIS FILL ANSWER HERE-/

/-
Finally, let us get an instance of a `OrderedCommMonoid₁`.
We will use the natural numbers.

Here we call some basic facts about inequalities for natural numbers.
-/
#check 0
#check 2 ≤ 3
#check le_refl
#check le_trans
#check le_antisymm
#check Nat.add
#check Nat.add_comm
#check Nat.add_assoc
#check Nat.add_zero
#check Nat.zero_add
#check Nat.add_le_add_right

/-
We now have the following structure of `OrderedCommMonoid₁`.

Uncomment the next line if you have solved the previous exercises.-/
-- #print OrderedCommMonoid₁

/-
Define an `instance` in `OrderedCommMonoid₁ ℕ`.
Use the properties given above.
-/

/- DELETE THIS FILL ANSWER HERE-/

end ordered_monoid
