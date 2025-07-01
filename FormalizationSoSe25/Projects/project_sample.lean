-- Here is a first `import Mathlib.Tactic` to get things started.
-- Based on the definitions you need, you can add more imports right below.
import Mathlib.Tactic
-- Theoretically, you could just write `import Mathlib`, but this will be somewhat slower.

-- aus Exercise 8

open Finset Fintype
variable {X : Type*} [DecidableEq X]

example (A B : Finset X) :
  #(A ∪ B) = #A  + #B  -  #(A ∩ B)  := by rw [card_union]

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
    _= #A + #B - #(A ∩ B) + #C - #(A ∩ C) - #(B ∩ C) + #(A ∩ B ∩ C) := by sorry -- Idee: rw [sub_add_eq_sub_sub]
    _≥ #A + #B - #(A ∩ B) + #C - #(A ∩ C) - #(B ∩ C) := by simp
    _= #A + #B + #C - #(A ∩ B) - #(A ∩ C) - #(B ∩ C) := by sorry -- Idee: Kommutativität der natürlichen Zahlen aber zählt Lean die Kardinalität von Mengen auch als natürliche Zahlen?
