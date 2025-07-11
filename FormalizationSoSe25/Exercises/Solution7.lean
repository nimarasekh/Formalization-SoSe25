import Mathlib.Tactic
import FormalizationSoSe25.Lectures.Lecture7

section morphisms
/-
We saw in the previous exercise how to define ordered commutative monoids.
We now want to look at morphisms thereof.

Let's get started with the definition of an order-preserving function.
-/
@[ext]
structure OrderPresHom (α β : Type*) [LE α] [LE β] where
  toFun : α → β
  le_of_le : ∀ a a', a ≤ a' → toFun a ≤ toFun a'

/-
Now, it's your turn.
Define a `structure`:
- It is called `OrderPresMonoidHom`.
- It takes two types `M` and `N` in `Type*` as input.
- It extends `MonoidHom₁` and `OrderPresHom`.
- It should admit the `ext` tactic.

Hint: This requires `M` and `N` having instances of `Monoid` and `LE`.
-/

@[ext]
structure OrderPresMonoidHom (M N : Type*) [Monoid M] [LE M] [Monoid N] [LE N] extends
MonoidHom₁ M N, OrderPresHom M N

/-
As we saw in the lecture, we generalize from here and define a more general class.
Concretely, we want to define a class `OrderPresHomClass`.
- The input is `F` in `Type*`, `X Y` in  `outParam Type*`.
- `X` and `Y` have instances of `LE`.

It has two fields:
- `toFun : F → X → Y`
- `le_of_le : ∀ f x x', x ≤ x' → toFun f x ≤ toFun f x'`
-/

class OrderPresHomClass (F : Type*) (X Y : outParam Type*) [LE X] [LE Y] where
  toFun : F → X → Y
  le_of_le : ∀ f x x', x ≤ x' → toFun f x ≤ toFun f x'

/-
The following are optional, but are useful exercises:
(1) Define an `instance` of `CoeFun F (fun _ ↦ M → N)`
    - It should be defined as `OrderPresHomClass.toFun`.
    - The assumption should include an instance of `OrderPresHomClass F M N`.
    - Can you use that to determine what other types and instances are necessary?
(2) Also, define an `attribute [coe]` for `OrderPresHomClass.toFun`
(3) For two types `X` and `Y` define an `instance` in
    `OrderPresHomClass (OrderPresHom X Y) X Y`.
    - This requires specifying the `toFun` and `le_of_le` fields.
    - What instances and types do we need for this instance to work?
-/

instance {F : Type*} {M N : outParam Type*} [LE M] [LE N] [OrderPresHomClass F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := OrderPresHomClass.toFun

attribute [coe] OrderPresHomClass.toFun

instance (X Y : Type*) [LE X] [LE Y] : OrderPresHomClass (OrderPresHom X Y) X Y where
  toFun := OrderPresHom.toFun
  le_of_le := OrderPresHom.le_of_le

/-
The next exercise is really necessary:
Define a class `OrderPresMonoidHomClass`.
- The input is `F` in `Type*`, `M` and `N` in `outParam Type*`.
- It extends `MonoidHomClass₂ F M N` and `OrderPresHomClass F M N`.

Hint: Think about which `instance` you need to assume for `M` and `N`.
-/

class OrderPresMonoidHomClass (F : Type*) (M N : outParam Type*) [Monoid M] [LE M] [Monoid N] [LE N]
  extends MonoidHomClass₂ F M N, OrderPresHomClass F M N

/-
We need examples.
Define an `instance` in
`OrderPresMonoidHomClass (OrderPresMonoidHom M N) M N`, for types `M`, `N` in `Type*`

Hint: In order for this definition work, which `instance` must `M` and `N` have?
-/
instance (M N : Type*) [LE M] [Monoid M] [LE N] [Monoid N] : OrderPresMonoidHomClass (OrderPresMonoidHom M N) M N where
  toFun := fun f => f.toOrderPresHom.toFun
  le_of_le := fun f => f.le_of_le
  map_one := fun f => f.toMonoidHom₁.map_one
  map_mul := fun f m n => f.toMonoidHom₁.map_mul m n

/-
We have now established enough background definitions to state and prove a lemma.

Here, we use the `IsOrderedMonoid` class, which `extends` the classes:
- `PartialOrder`
- `Monoid`
- and additionally includes `IsOrderedMonoid.mul_le_mul_right`
(it resembles `OrderedCommMonoid₁` from `Exercise6`).
-/
#check IsOrderedMonoid
/-
Now, state and prove the lemma `le_of_le_sum`.
The assumptions are:
- `M`, `N`, `F` are types in `Type*`.
- `M` and `N` must have `instance` of `IsOrderedMonoid`.
-  There is `f` in `F`, `m₁` `m₂` `m'₁` in `M` and `h` in `m₁ ≤ m'₁`
- The lemma is of type `f m₁ * f m₂ ≤ f m'₁ * f m₂`.

Hint 1: Which additional `instance` must `M` and `N` have so that the definition makes sense?

Hint 2: In the proof you can benefit from the following:
-/
#check MonoidHomClass₂.map_mul
#check IsOrderedMonoid.mul_le_mul_right
-- You can uncomment the next line after you have defined `OrderPresHomClass`
#check OrderPresHomClass.le_of_le

lemma le_of_le_sum {M N F : Type*} [CommMonoid M] [PartialOrder M] [IsOrderedMonoid M] [CommMonoid N] [PartialOrder N] [IsOrderedMonoid N] [OrderPresMonoidHomClass F M N] (f : F) {m₁ m₂ m'₁ : M} (h : m₁ ≤ m'₁) :
    f m₁ * f m₂ ≤ f m'₁ * f m₂ := by
    calc
      f m₁ * f m₂ = f (m₁ * m₂) :=(MonoidHomClass₂.map_mul f m₁ m₂).symm
      _ ≤ f (m'₁ * m₂) := by {
        apply OrderPresHomClass.le_of_le f _ _ _
        apply IsOrderedMonoid.mul_le_mul_right
        exact h
      }
      _ = f m'₁ * f m₂ := MonoidHomClass₂.map_mul f m'₁ m₂

/-
Now, use the lemma to prove an example.
The assumptions are:
- `M`, `N` are types in `Type*`.
- `f` is of type `OrderPresMonoidHom M N`
-  There is `m₁` `m₂` `m'₁` in `M` and `h` in `m₁ ≤ m'₁`
- The example is of type `f m₁ * f m₂ ≤ f m'₁ * f m₂`.
-/

example {M N : Type*}[CommMonoid M] [PartialOrder M] [IsOrderedMonoid M] [CommMonoid N] [PartialOrder N] [IsOrderedMonoid N] (f : OrderPresMonoidHom M N) {m₁ m₂ m'₁ : M} (h : m₁ ≤ m'₁) :
    f m₁ * f m₂ ≤ f m'₁ * f m₂ := le_of_le_sum f h

end morphisms

section subgroups
/-
In the lecture we saw how to define submonoids and construct
their intersection.

In this exercise we want to repeat the same exercise with subgroups.
-/

/-
Define the structure `Subgroup₁` that represents a subgroup of a group `G`.
- The input is `G : Type*` and `[Group G]`.
- It should admit the `ext` tactic.
- It should have the following fields:
  - `carrier : Set G` representing the carrier of the subgroup.
  - `mul_mem {a b}`: a proof that if `a` and `b` are in the carrier, then their product is also in the carrier.
  - `one_mem`: a proof that the unit element of the group is in the carrier.
  - `inv_mem {a}`: a proof that if `a` is in the carrier, then its inverse is also in the carrier.
-/

@[ext]
structure Subgroup₁ (G : Type*) [Group G] where
  /-- The carrier of a subgroup. -/
  carrier : Set G
  /-- The product of two elements of a subgroup belongs to the subgroup. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the subgroup. -/
  one_mem : 1 ∈ carrier
  /-- The inverse of an element of a subgroup belongs to the subgroup. -/
  inv_mem {a} : a ∈ carrier → a⁻¹ ∈ carrier

/-
Next define and `instance`
- The input is `G : Type*` and `[Group G]`.
- It takes value in `SetLike (Subgroup₁ G) G`

This proves that subgroups in `G` can be seen as sets in `G`.
-/
instance {G : Type*} [Group G] : SetLike (Subgroup₁ G) G where
  coe := Subgroup₁.carrier
  coe_injective' _ _ := Subgroup₁.ext

/-
If you have defined the `structure` named `Subgroup₁`
and an `instance` of `SetLike (Subgroup₁ G) G`, then
uncomment the next two lines and fill in the `sorry`.
-/

instance {G : Type*} [Group G] : Min (Subgroup₁ G) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩
      inv_mem := fun ⟨hx, hx'⟩ ↦ ⟨S₁.inv_mem hx, S₂.inv_mem hx'⟩
    }⟩

/-
To apply the instance, define an `example`.
- The input is `G : Type*` and `[Group G]`, `(H K : Subgroup₁ G)`.
- It should be an expression of type `Subgroup₁ G`.
- It should be the intersection of `H` and `K`, constructed above.
-/
example {G : Type*} [Group G] (H K : Subgroup₁ G) : Subgroup₁ G := H ⊓ K

end subgroups

section quotient
/-
In this section we want to construct quotients of commutative monoids.

Fill out the `sorry` you find below, to complete the proof.
Use the parts that have been solved as a guide how you can approach the rest.
-/

def Submonoid.Setoid {M : Type*} [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := fun ⟨w₁, hw₁, z₁, hz₁, h₁⟩ ⟨w₂, hw₂, z₂, hz₂, h₂⟩ ↦
      ⟨w₁ * w₂, N.mul_mem hw₁ hw₂, z₁ * z₂, N.mul_mem hz₁ hz₂, by
      rw [mul_comm z₁ _ , ← mul_assoc _ z₂ _ , ← h₂, ← mul_assoc _ w₁ _, h₁, mul_assoc, mul_comm z₁, mul_assoc]
      ⟩
  }

instance {M : Type*} [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk {M : Type*} [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

instance {M: Type*} [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂ (· * ·) (by
      rintro a b ⟨ ab , ⟨hab , ⟨c , ⟨hc , habc⟩⟩⟩⟩  x y ⟨ xy , ⟨hxy , ⟨z , ⟨hz , hxyz⟩⟩⟩⟩
      simp
      use (ab * xy)
      constructor
      · exact Submonoid.mul_mem N hab hxy
      · use (c * z)
        constructor
        · exact Submonoid.mul_mem N hc hz
        · rw [mul_assoc a, mul_assoc b, ← mul_assoc x, ← mul_assoc y, mul_comm x,  mul_comm y, mul_assoc, mul_assoc, hxyz, ← mul_assoc a, ← mul_assoc b, habc]

  )
  mul_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    apply Quotient.sound
    simp
    use 1
    constructor
    · exact N.one_mem
    · use 1
      constructor
      · exact N.one_mem
      · rw [mul_one (a * b * c), mul_one (a * (b * c)), mul_assoc]
  one := QuotientMonoid.mk N 1
  one_mul := by
    rintro ⟨a⟩
    apply Quotient.sound
    use 1
    constructor
    · exact N.one_mem
    · use 1
      constructor
      · exact N.one_mem
      · simp
  mul_one := by
    rintro ⟨a⟩
    apply Quotient.sound
    use 1
    constructor
    · exact N.one_mem
    · use 1
      constructor
      · exact N.one_mem
      · simp

end quotient
