-- Here is a first `import Mathlib.Tactic` to get things started.
-- Based on the definitions you need, you can add more imports right below.

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.BigOperators

-- Theoretically, you could just write `import Mathlib`, but this will be somewhat slower.

-- aus Exercise 8
open BigOperators
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
lemma inter_finset_funktion {A B : Finset X} {f : Finset X → G} :
  f (A ∩ B) ≤ f A := by sorry

lemma union_finset {A B : Finset X} :
  (A ∪ B) = Finset X := by sorry

example (A B : Finset X) (f : Finset X → G) :
  f (A ∪ B) = f A + f B - f (A ∩ B) := by
  rcases
  · left
    f (A ∪ B) = Set.image f (A ∪ B) = {x : G | ∃ (a : X), a ∈ A ∪ B ∨ f a = x }:= by sorry
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

open BigOperators
open Finset

variable {ι α G : Type*} [DecidableEq α]
  [AddCommGroup G] [PartialOrder G]
variable (r : ℕ)

  /-
  [IsOrderedAddMonoid G] liefert Fehlermeldung, deswegen habe ich es erstmal weggelassen, da dann kein Fehler mehr auftaucht
  -/

-- trunkierte Version von theorem inclusion_exclusion_sum_biUnion, aufgeteilt in gerade und ungerade Fälle

/- wie mache ich hier dass die range Funktion bis 2r geht? range (2r) soll {0,1,...,2r-1} sein
deswegen habe ich im Exponenten in der Summe p statt p-1 (bzw. p+1), weil die Summe jetzt
mit 0 startet und nicht mit 1 und bis 2r-1 geht statt bis 2r. Die Anzahl der Elemente über die
abgeschätzt wird bleibt dadurch ja aber gerade.-/

theorem incl_excl_sum_biUnion_trunk_even (s : Finset ι) (S : ι → Finset α) (f : α → G) :
  ∑ a ∈ s.biUnion S, f a ≥ ∑ p ∈ (range (2r)).filter (·.Nonempty), (-1) ^ p • ∑ a ∈ p.inf' S, f a := by sorry

theorem incl_excl_sum_biUnion_trunk_odd (s : Finset ι) (S : ι → Finset α) (f : α → G) :
  ∑ a ∈ s.biUnion S, f a ≤ ∑ p ∈ (range (2r+1)).filter (·.Nonempty), (-1) ^ p • ∑ a ∈ p.inf' S, f a := by sorry

end induction_assumption_try
