import Mathlib.Tactic

/- This section defines a product between subsets of X×X (for X some set) as well as an operation for taking inverses
  and the diagonal set as a neutral element. These will be needed in order to define coarse spaces.
-/

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

/- Now we define the class CoarseSpace analogously to a Topology. A coarse space consists of a set X and a coarse structure
ε ⊆ P(X×X) ("controlled sets"), where ε is closed under union, inverse and product as well as contains the diagonal.-/

class CoarseSpace (X : Type*) where
  IsControlled : Set (X × X) → Prop
  IsControlled_union : ∀ s t : Set (X × X), IsControlled s → IsControlled t → IsControlled (s ∪ t)
  IsControlled_diag : Set (X×X) := SetDiag X
  IsControlled_inv : ∀ s : Set (X×X), IsControlled s → IsControlled (SetInv s)
  IsControlled_prod : ∀ s t : Set (X × X), IsControlled s → IsControlled t → IsControlled (SetProd s t)



/- In the following, we want to establish that every MetricSpace is coarse by showing that an arbitrary
MetricSpace is an instance of a CoarseSpace. This holds, if we define S ⊆ X×X controlled ↔ sup{d(x,y)| (x,y) ∈ S} < ∞.
We start with a section for auxiliary lemmas and definitions.
-/

section lemmas_defs_for_metric_coarse
-- Coordinate projections π₁, π₂ for elements x ∈ s ⊆ X×X

def π₁ {X : Type*} {s : Set (X×X)} (x:X× X) (h : x∈ s) : X := by
  let ⟨ x₁, x₂⟩ := x
  exact x₁

def π₂ {X : Type*} {s : Set (X×X)} (x:X× X) (h : x∈ s) : X := by
  let ⟨ x₁, x₂⟩ := x
  exact x₂

-- The dist_set of s ⊆ X×X is defined as {d(x,y)| (x,y) ∈ S} ⊆ ℝ

def dist_set {X : Type*} [MetricSpace X] (s : Set (X×X)) : Set ℝ := { dist (π₁ x h) (π₂ x h) | (x:X×X) (h:x∈ s) }

-- Lemma for showing that the dist_set of a nonempty set is nonempty

lemma nonempty_set_distset {X : Type*} [MetricSpace X] (s : Set (X×X)) : s.Nonempty → (dist_set s).Nonempty := by
  intro non_s
  have (x : X× X) (h : x ∈ s):= by
    exact non_s
  sorry



def exists_diam {X : Type*} [MetricSpace X] (s : Set (X×X)) : Prop := (dist_set s).Nonempty ∧ BddAbove (dist_set s)

end lemmas_defs_for_metric_coarse

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
