import Mathlib.Tactic

--universe u

section set_operations
  def SetInv {X : Type*} (sub : Set (X × X)) : Set (X × X) := by
    rintro  ⟨ e1, e2 ⟩
    exact sub ⟨ e2, e1 ⟩

  def SetDiag (X : Type*) : Set (X×X) := {⟨x,x⟩| x : X }

  def SetProd {X : Type*} (sub₁ : Set (X × X))  (sub₂ : Set (X × X)) : Set (X × X) := by
    rintro e
    have indicator : (X × X) → Prop := by
      rintro ⟨x₁, x₂⟩
      exact ∃ x₃: X, sub₁ ⟨x₁,x₃ ⟩ ∧ ∃ x₄, sub₂ ⟨x₄, x₂⟩
    exact indicator e

end set_operations


class CoarseSpace (X : Type*) where
  IsControlled : Set (X × X) → Prop
  IsControlled_union : ∀ s t : Set (X × X), IsControlled s → IsControlled t → IsControlled (s ∪ t)
  IsControlled_diag : Set (X×X) := SetDiag X
  IsControlled_inv : ∀ s : Set (X×X), IsControlled s → IsControlled (SetInv s)
  IsControlled_prod : ∀ s t : Set (X × X), IsControlled s → IsControlled t → IsControlled (SetProd s t)

#print MetricSpace
#check Real.exists_isLUB
#check dist (3: ℝ) (5: ℝ)


-- proof that any metric space is coarse


def π₁ {X : Type*} {s : Set (X×X)} (x:X× X) (h : x∈ s) : X := by
  let ⟨ x₁, x₂⟩ := x
  exact x₁

def π₂ {X : Type*} {s : Set (X×X)} (x:X× X) (h : x∈ s) : X := by
  let ⟨ x₁, x₂⟩ := x
  exact x₂

def dist_set {X : Type*} [MetricSpace X] (s : Set (X×X)) : Set ℝ := { dist (π₁ x h) (π₂ x h) | (x:X×X) (h:x∈ s) }

lemma nonempty_set_distset {X : Type*} [MetricSpace X] (s : Set (X×X)) : s.Nonempty → (dist_set s).Nonempty := by
  intro non_s
  have (x : X× X) (h : x ∈ s):= by
    exact non_s
  sorry



def exists_diam {X : Type*} [MetricSpace X] (s : Set (X×X)) : Prop := (dist_set s).Nonempty ∧ BddAbove (dist_set s)


instance (X : Type*) [MetricSpace X] : CoarseSpace X where
  IsControlled := exists_diam
  IsControlled_union := by
    rintro s t ⟨non_s, bd_s⟩ ⟨non_t, bd_t⟩
    constructor
    have hs : ∃ x : ℝ , x ∈ (dist_set s) := by
      exact non_s
    sorry






  IsControlled_diag := sorry
  IsControlled_inv := sorry
  IsControlled_prod := sorry
