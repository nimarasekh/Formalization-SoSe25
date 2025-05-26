import Mathlib.Tactic

universe u

section set_operations
  def SetInv (X : Type*) : Set (X × X) → Set (X × X) := by
    intro sub e
    have ⟨ e1, e2 ⟩ := e
    exact sub ⟨ e2, e1 ⟩
  def SetDiag (X : Type*) : X → X := fun x : X => x
  def SetProd (X : Type*) : Set (X × X) → Set (X × X) → Set (X × X) := by
    intro sub₁ sub₂ e₁

end set_operations


class CoarseSpace (X : Type u) where
  IsControlled : Set (X × X) → Prop
  IsControlled_union : ∀ s t : Set (X × X), IsControlled s → IsControlled t → IsControlled (s ∪ t)
