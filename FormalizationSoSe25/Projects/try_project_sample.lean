-- Here is a first `import Mathlib.Tactic` to get things started.
-- Based on the definitions you need, you can add more imports right below.
import Mathlib.Tactic
-- Theoretically, you could just write `import Mathlib`, but this will be somewhat slower.

-- aus Exercise 8

open Finset Fintype
variable {X G : Type*} [DecidableEq X] [AddCommGroup G] [PartialOrder G]
/-
wie mache ich das #X automatisch als natürliche Zahl von Lean interpretiert wird?
X.card = #X := by rfl
-/

example (A : Finset X) : A.card = #A := by rfl

example (A B : Finset X) :
  #(A ∪ B) = #A  + #B  -  #(A ∩ B)  := by rw [card_union]


/-
Kardinalität verallgemeinern zu Funktion f. Allerdings komme ich hier nicht weiter.
Habe überlegt mit image f (A∪B) zu arbeiten aber das funktioniert iwie auch noch nicht.
Hab das Gefühl, dass Lean nicht erkennt das f (A ∪ B) auch in G lebt.
-/
lemma union_finset {A B : Finset X} :
  (A ∪ B) = Finset X := by sorry

example (A B : Finset X) (f : Finset X → G) :
  f (A ∪ B) = f A + f B - f (A ∩ B) := by
  rcases
  · left
    f (A ∪ B) = Set.image f (A ∪ B) = {x : G | ∃ (a : X), a ∈ A ∪ B ∧ f a = x }:= by sorry
  · right
    sorry
/-
- mein Syntax ist noch falsch, aber ich glaube die Idee wird klar
- hier ist Finset glaube ich die falsche Verwendung, ich bräuchte eher ein Multiset,
damit die doppelten Elemente berücksichtigt werden, die ich mit dem Schnitt wieder abziehen möchte
- warum die Taktik nicht funktioniert weiß ich nicht.
-/

example (A B : Finset X) (f : Finset X → G) :
  f (A ∪ B) ≤  f A + f B := by
  calc
     f (A ∪ B) =  f A  + f B  -  f (A ∩ B)  := by sorry -- rw [card_union]
    _≤ f A + f B := by sorry -- simp ist Sammeltaktik

example (A B : Finset X) :
  #(A ∪ B) ≤ #A + #B := by
  calc
    #(A ∪ B) = #A  + #B  -  #(A ∩ B)  := by rw [card_union]
    _≤ #A + #B := by simp -- simp ist Sammeltaktik


lemma Schnitt {A B C : Finset X}:(A ∩ C ∩ (B ∩ C)) = (A ∩ C ∩ B):= by
  calc
    (A ∩ C ∩ (B ∩ C)) = (A ∩ C ∩ (C ∩ B)) := by rw [Finset.inter_comm B C]
    _= (A ∩ C ∩ C ∩ B) := by simp
    _= (A ∩ (C ∩ C) ∩ B) := by simp
    _= (A ∩ C ∩ B) := by simp


example (A B C : Finset X) :
  #(A ∪ B ∪ C) ≥ #A + #B + #C - #(A ∩ B) - #(A ∩ C) - #(B ∩ C) := by
  let H : Finset X := A ∪ B
  calc
    #(A ∪ B ∪ C) = #(H ∪ C) := by sorry
    _= #H + #C - #(H ∩ C) := by rw [card_union]
    _= #A + #B - #(A ∩ B) + #C - #((A ∪ B) ∩ C) := by sorry
    _= #A + #B - #(A ∩ B) + #C - #((A ∩ C) ∪ (B ∩ C)) := by rw [← Finset.union_inter_distrib_right]
    _= #A + #B - #(A ∩ B) + #C - (#(A ∩ C) + #(B ∩ C) - #(A ∩ C ∩ (B ∩ C))) := by rw [card_union]
    _= #A + #B - #(A ∩ B) + #C - (#(A ∩ C) + #(B ∩ C) - #(A ∩ C ∩ B)) := by rw [Schnitt]
    _= #A + #B - #(A ∩ B) + #C - #(A ∩ C) - #(B ∩ C) + #(A ∩ B ∩ C) := by sorry -- Idee: rw [sub_add_eq_sub_sub] oder rw [Nat.sub_add_eq]
    _≥ #A + #B - #(A ∩ B) + #C - #(A ∩ C) - #(B ∩ C) := by simp
    _= #A + #B + #C - #(A ∩ B) - #(A ∩ C) - #(B ∩ C) := by sorry -- Idee: Kommutativität der natürlichen Zahlen aber zählt Lean die Kardinalität von Mengen auch als natürliche Zahlen?



section induction_assumption_try

open Finset

variable {ι α G : Type*} [DecidableEq α]
  [AddCommGroup G] [PartialOrder G]
  /-
  [IsOrderedAddMonoid G] liefert Fehlermeldung, deswegen habe ich es erstmal weggelassen, da dann kein Fehler mehr auftaucht
  -/

theorem sum_biUnion_le_sum (s : Finset ι) (S : ι → Finset α) (f : α → G) :
    ∑ a ∈ s.biUnion S, f a ≤ ∑ i ∈ s, ∑ a ∈ S i, f a := by
    sorry

/-
worüber soll hier die Induktion laufen?
-/

end induction_assumption_try
