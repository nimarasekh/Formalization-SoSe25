import Mathlib.Tactic

/-
Here are a set of exercises about algebra and linear algebra.
They vary in difficulty and cover a variety of topics.
Feel free to skip and pick whatever exericise you like.
-/

section subgroups

/-
Here are some exercises about subgroups of a group.

The first exercises in this section are somewhat easier
than the other ones about groups.
-/

variable {G H : Type*} [Group G] [Group H]

open Subgroup

example (f : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap f S ≤ comap f T := by
  intro x hx
  simp
  simp at hx
  apply hST
  exact hx

example (f : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map f S ≤ map f T := by
  intro x ⟨t, tS, ht⟩
  have this : t ∈ T := hST tS
  simp
  use t

variable {K : Type*} [Group K]

-- Remember you can use the `ext` tactic to prove an equality of subgroups.
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) :
    comap (ψ.comp φ) U = comap φ (comap ψ U) := by
  ext
  constructor
  · intro h
    simp at h
    simp [h]
  · intro h
    simp at h
    simp [h]

-- Pushing a subgroup along one homomorphism and then another is equal to
-- pushing it forward along the composite of the homomorphisms.
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
    map (ψ.comp φ) S = map ψ (S.map φ) := by
  ext
  constructor
  · intro h
    simp at h
    simp [h]
  · intro h
    simp at h
    simp [h]


-- For this exercise recall that subgroups have the identity element.
#check Subgroup.one_mem

lemma eq_bot_iff_card {K : Subgroup G} :
    K = ⊥ ↔ Nat.card K = 1 := by
  suffices (∀ x ∈ K, x = 1) ↔ ∃ x ∈ K, ∀ a ∈ K, a = x by
    simpa [eq_bot_iff_forall, Nat.card_eq_one_iff_exists]
  constructor
  · intro h
    use 1
    constructor
    · exact Subgroup.one_mem K
    · intro a ha
      have : a = 1 := h a ha
      rw [this]
  · rintro ⟨x, hx, h⟩
    intro a ha
    have : a = x := h a ha
    rw [this]
    rw [h 1]
    exact Subgroup.one_mem K

/-
For this last exercise we need the following fact about divisibility and the previous lemma.
-/
#check card_dvd_of_le

lemma inf_bot_of_coprime (K L : Subgroup G)
    (h : (Nat.card K).Coprime (Nat.card L)) : K ⊓ L = ⊥ := by
  apply eq_bot_iff_card.2
  have h₀ : K ⊓ L ≤ K := by simp
  have h₀' : K ⊓ L ≤ L := by simp
  have h₁ : Nat.card (K ⊓ L : Subgroup G) ∣ Nat.card K := card_dvd_of_le h₀
  have h₂ : Nat.card (K ⊓ L : Subgroup G) ∣ Nat.card L := card_dvd_of_le h₀'
  have h₃ : Nat.card (K ⊓ L : Subgroup G) ∣ gcd (Nat.card K) (Nat.card L) := by
    apply Nat.dvd_gcd h₁ h₂
  have h₄ : gcd (Nat.card ↥K) (Nat.card ↥L) = 1 := by
    apply Nat.coprime_iff_gcd_eq_one.1 h
  rw [h₄] at h₃
  norm_num at h₃
  norm_num
  rw [h₃]

end subgroups

section groups_conjugate
/-
In this exercise we look at the conjugation action of subgroups.
-/
variable {G H : Type*} [Group G] [Group H]

/-
First for a subgroup we define the conjugate subgroup.
We already need the following facts about subgroups:
-/
#check Subgroup.one_mem
#check Subgroup.inv_mem
#check Subgroup.mul_mem

def conjugate (x : G) (G₁ : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ G₁ ∧ a = x * h * x⁻¹}
  one_mem' := by
    simp
    use 1
    constructor
    · exact Subgroup.one_mem G₁
    · simp
  inv_mem' := by
    simp
    intro x y hy hxz
    use y⁻¹
    constructor
    · exact Subgroup.inv_mem G₁ hy
    · simp [hxz]
      group
  mul_mem' := by
    intro a b ⟨c , ⟨hc, eqc⟩⟩ ⟨d , ⟨hd, eqd⟩⟩
    use c * d
    constructor
    · exact @Subgroup.mul_mem G inferInstance  G₁ c d hc hd
    · simp [eqc, eqd]

lemma conjugate_one (K : Subgroup G) : conjugate 1 K = K := by
  ext g
  constructor
  · intro k
    simp [conjugate] at k
    exact k
  · intro k
    simp [conjugate]
    exact k

instance : MulAction G (Subgroup G) where
  smul := conjugate
  one_smul := by
    intro K
    ext g
    constructor
    · intro hg
      simp [HSMul.hSMul] at hg
      rw [conjugate_one K] at hg
      exact hg
    · intro h
      simp [HSMul.hSMul]
      rw [conjugate_one K]
      exact h
  mul_smul := by
    intro x y K
    ext g
    constructor
    · intro ⟨g₁ , hg₁, eq₁⟩
      use  y * g₁ * y⁻¹
      constructor
      · simp [HSMul.hSMul, conjugate]
        exact hg₁
      · rw [eq₁]
        group
    · intro ⟨g₁ , ⟨g₂, ⟨hg₂, eq₂⟩⟩, eq₁⟩
      simp [HSMul.hSMul, conjugate]
      use g₂
      constructor
      · exact hg₂
      · rw [eq₁, eq₂]
        group

end groups_conjugate

noncomputable section groups_index
/-
We now look at some exercises about the index of a subgroup and the cardinality.
-/
variable {G: Type*} [Group G] {K L : Subgroup G}

open MonoidHom

#check Nat.card_pos -- The nonempty argument will be automatically inferred for subgroups
#check Subgroup.index_eq_card
#check Subgroup.index_mul_card
#check Nat.eq_of_mul_eq_mul_right

lemma aux_card_eq [Finite G] (h' : Nat.card G = Nat.card K * Nat.card L) :
    Nat.card (G ⧸ K) = Nat.card L := by
    calc
      Nat.card (G ⧸ K) = K.index := by rw [← Subgroup.index_eq_card K]
      _ = K.index * (Nat.card K) / (Nat.card K):= by norm_num
      _ = Nat.card G / Nat.card K := by rw [Subgroup.index_mul_card]
      _ = Nat.card K * Nat.card L / Nat.card K := by rw [h']
      _ = Nat.card L := by norm_num

variable [K.Normal] [L.Normal] [Fintype G] (h : Disjoint K L) (h' : Nat.card G = Nat.card K * Nat.card L)

#check Nat.bijective_iff_injective_and_card
#check ker_eq_bot_iff
#check restrict
#check ker_restrict
#check ker_prod
#check QuotientGroup.mk'
#check MulEquiv.ofBijective

def iso₁ : L ≃* G ⧸ K := by
  apply MulEquiv.ofBijective ((QuotientGroup.mk' K).restrict L)
  apply (Nat.bijective_iff_injective_and_card ((QuotientGroup.mk' K).restrict L)).2
  constructor
  · apply (ker_eq_bot_iff ((QuotientGroup.mk' K).restrict L)).1
    rw [(QuotientGroup.mk' K).ker_restrict L]
    simp [h]
  · exact (aux_card_eq h').symm

/-
This one is harder.
For this one you want to use the same results reviewed before `iso₁`,
along with the following:
-/
#check Nat.card_prod

def iso₂ : G ≃* (G ⧸ K) × (G ⧸ L) := by
  apply MulEquiv.ofBijective <| (QuotientGroup.mk' K).prod (QuotientGroup.mk' L)
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · rw [← ker_eq_bot_iff, ker_prod]
    simp
    simp [Disjoint] at h
    simp [h]
  · rw [Nat.card_prod]
    rw [aux_card_eq h']
    have h'' : Nat.card G = Nat.card L * Nat.card K := by rw [h']; exact Nat.mul_comm _ _
    rw [aux_card_eq h'']
    rw [h'']

#check MulEquiv.symm
#check MulEquiv.trans
#check MulEquiv.prodCongr

def finalIso : G ≃* K × L := by
   have h₁ : G ≃* (G ⧸ K) × (G ⧸ L) := iso₂ h h'
   have h₂ : (G ⧸ K) ≃* L := MulEquiv.symm (iso₁ h h')
   have h'' : Disjoint L K := by {
    simp [Disjoint]
    simp [Disjoint] at h
    intro x hx hy
    exact (h hy hx)
   }
   have h''' : Nat.card G = Nat.card L * Nat.card K := by
    rw [h']
    rw [Nat.mul_comm]
   have h₃ : (G ⧸ L) ≃* K := MulEquiv.symm (iso₁ h'' h''')
   have h₄ : (G ⧸ L) × (G ⧸ K) ≃* K × L := MulEquiv.prodCongr h₃ h₂
   have h₅ : G ≃* (G ⧸ L) × (G ⧸ K) := iso₂ h'' h'''
   exact MulEquiv.trans h₅ h₄

end groups_index

section rings_ideals
/-
In this section we look at basic exercises about rings and ideals.
They should be reasonably straightforward.
-/

/-
If `R` is a ring, then the zero ideal is an ideal of `R`.
-/
def zeroIdeal (R : Type*) [Ring R] : Ideal R where
  carrier := {0}
  zero_mem' := by
    simp
  add_mem' := by
    intros a b ha hb
    rw [ha, hb]
    simp
  smul_mem' := by
    intros c a ha
    rw [ha]
    simp

/-
If `R` and `S` are rings, and `f : R →+* S` is a ring homomorphism,
then the preimage of an ideal `I` of `S` under `f` is an ideal of `R`.
-/
def preimageIdeal {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (I : Ideal S) : Ideal R where
  carrier := f ⁻¹' I
  zero_mem' := by
    rw [Set.mem_preimage, RingHom.map_zero]
    exact I.zero_mem
  add_mem' := by
    intros a b ha hb
    rw [Set.mem_preimage, RingHom.map_add]
    exact I.add_mem ha hb
  smul_mem' := by
    intros c a ha
    simp [Set.mem_preimage] at *
    exact I.smul_mem' (f c) ha

end rings_ideals

section chinese_remainder
/-
Let's look at rings and ideals and use that to prove the Chinese Remainder Theorem.
This section is significantly harder.
-/

-- Recall that for a ring and an idea, we have a quotient map.
example {R : Type*} [CommRing R] (I : Ideal R) : R →+* R ⧸ I :=
  Ideal.Quotient.mk I

#check Ideal.Quotient.eq_zero_iff_mem
#check Ideal.Quotient.lift

variable {ι R : Type*} [CommRing R]
open Ideal Quotient Function

/-
Let us start by constructing the homomorphism from ``R ⧸ ⨅ i, I i`` to ``Π i, R ⧸ I i``
featured in the Chinese Remainder Theorem. We only need the following:
-/
#check RingHom.mem_ker
#check ker_Pi_Quotient_mk

def chineseMap (I : ι → Ideal R) : (R ⧸ ⨅ i, I i) →+* Π i, R ⧸ I i :=
  Ideal.Quotient.lift (⨅ i, I i) (Pi.ringHom fun i : ι ↦ Ideal.Quotient.mk (I i))
    (by  simp [← RingHom.mem_ker, ker_Pi_Quotient_mk])

/-
The next two are sanity checks and should follow by definition with `rfl`.
-/
lemma chineseMap_mk (I : ι → Ideal R) (x : R) :
    chineseMap I (Quotient.mk _ x) = fun i : ι ↦ Ideal.Quotient.mk (I i) x :=
  rfl

lemma chineseMap_mk' (I : ι → Ideal R) (x : R) (i : ι) :
    chineseMap I (mk _ x) i = mk (I i) x :=
  rfl

/-
We now want to show `chineseMap` is injective.

Here we also want the following:
-/
#check injective_lift_iff
#check ker_Pi_Quotient_mk

lemma chineseMap_inj (I : ι → Ideal R) : Injective (chineseMap I) := by
  rw [chineseMap, injective_lift_iff, ker_Pi_Quotient_mk]

theorem isCoprime_Inf {I : Ideal R} {J : ι → Ideal R} {s : Finset ι}
    (hf : ∀ j ∈ s, IsCoprime I (J j)) : IsCoprime I (⨅ j ∈ s, J j) := by
  classical
  simp_rw [isCoprime_iff_add] at *
  induction s using Finset.induction with
  | empty =>
      simp
  | @insert i s _ hs =>
      rw [Finset.iInf_insert, inf_comm, one_eq_top, eq_top_iff, ← one_eq_top]
      set K := ⨅ j ∈ s, J j
      calc
        1 = I + K                  :=  by {
        -- For this first step we need `Finset.mem_insert_of_mem`
          apply Eq.symm
          apply hs
          intro j hj
          exact hf j (Finset.mem_insert_of_mem hj)
        }
        _ = I + K * (I + J i)      := by {
          -- For this next step we need `Finset.mem_insert_self`
          rw [hf i (Finset.mem_insert_self i s)]
          rw [mul_one]
        }
        _ = (1 + K) * I + K * J i  := by ring
        _ ≤ I + K ⊓ J i            := by {
          -- For this last step you can start with the `gcongr` tactic
          -- and also benefit from `mul_le_left` and `mul_le_inf`
          gcongr
          apply mul_le_left
          apply mul_le_inf
        }

/-
We now want to show `chineseMap` is surjective.
This one is quite involved.
-/

lemma chineseMap_surj [Fintype ι] {I : ι → Ideal R}
    (hI : ∀ i j, i ≠ j → IsCoprime (I i) (I j)) : Surjective (chineseMap I) := by
  classical
  intro g
  choose f hf using fun i ↦ Ideal.Quotient.mk_surjective (g i)
  have key : ∀ i, ∃ e : R, mk (I i) e = 1 ∧ ∀ j, j ≠ i → mk (I j) e = 0 := by
    intro i
    have hI' : ∀ j ∈ ({i} : Finset ι)ᶜ, IsCoprime (I i) (I j) := by {
      intro j hj
      simp at hj
      have hij: i ≠ j := by {
        intro k
        exact hj k.symm
      }
      exact hI _ _ hij
    }
    rcases isCoprime_iff_exists.mp (isCoprime_Inf hI') with ⟨u, hu, e, he, hue⟩
    replace he : ∀ j, j ≠ i → e ∈ I j := by simpa using he
    refine ⟨e, ?_, ?_⟩
    · simp [eq_sub_of_add_eq' hue, map_sub, eq_zero_iff_mem.mpr hu]
    · exact fun j hj ↦ eq_zero_iff_mem.mpr (he j hj)
  choose e he using key
  use mk _ (∑ i, f i * e i)
  ext i
  rw [chineseMap_mk', map_sum, Fintype.sum_eq_single i]
  · simp [(he i).1, hf]
  · intros j hj
    simp [(he j).2 i hj.symm]

/-
Finally, we combine all these things in the Chinese Remainder Theorem Isomorphism.
-/
noncomputable def chineseIso [Fintype ι] (f : ι → Ideal R)
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i :=
  { Equiv.ofBijective _ ⟨chineseMap_inj f, chineseMap_surj hf⟩,
    chineseMap f with }

end chinese_remainder

section vectorspaces
/-
Let's prove that the preimage of a subspace under a linear map is a subspace.
This one should not be too complicated.

Recall the notation for preimage of a function `f` is `f ⁻¹'`.
Also recall we learned one useful trick about preimages:
-/
#check Set.mem_preimage

/-
Of course, we also need some basic facts about linear maps:
-/
#check LinearMap.map_zero
#check LinearMap.map_add
#check LinearMap.map_smul

variable {K V W : Type} [Field K] [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]

def preimage  (f : V →ₗ[K] W) (H : Submodule K W) :
    Submodule K V where
  carrier := f ⁻¹' H
  zero_mem' := by
    rw [Set.mem_preimage, LinearMap.map_zero]
    exact H.zero_mem
  add_mem' := by
    intro a b ha hb
    rw [Set.mem_preimage, LinearMap.map_add]
    exact H.add_mem ha hb
  smul_mem' := by
    intro c a ha
    rw [Set.mem_preimage, LinearMap.map_smul]
    exact H.smul_mem c ha

end vectorspaces

section dimension
/-
Let's prove that if a linear map between two vector spaces is bijective,
then their dimensions are equal.

The following should be useful:
-/

#check LinearMap.rank_le_of_injective
#check LinearMap.rank_le_of_surjective

variable {K V W : Type} [Field K] [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]

example (f : V →ₗ[K] W) (hf : Function.Bijective f) : Module.rank K V = Module.rank K W := by
  have h₁ : Module.rank K V ≤ Module.rank K W := LinearMap.rank_le_of_injective f hf.1
  have h₂ : Module.rank K W ≤ Module.rank K V := LinearMap.rank_le_of_surjective f hf.2
  exact le_antisymm h₁ h₂

end dimension

section matrix

open Matrix
/-
Let's try to see that the product of two invertible matrices is also invertible.
Concretely, we check the determinant of the product of two matrices is non-zero.

This can help:
-/
#check det_mul

variable {K : Type} {n : ℕ} [Field K] (A B : Matrix (Fin n) (Fin n) K)

example (eqA : A.det ≠ 0) (eqB : B.det ≠ 0) : (A * B).det ≠ 0 := by
  rw [det_mul]
  exact mul_ne_zero eqA eqB

end matrix
