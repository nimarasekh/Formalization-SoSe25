import Mathlib.Tactic


section review


/-
Last time we discussed how to combine
- `morphisms`
- `structures`, `classes`, `instances`, and `hierarchies`.
by using `morphism classes`.

We similarly learned how to combine
- `subobjects`
- `structures`, `classes`, `instances`, and `hierarchies`.
by using `subobject classes`.
-/

end review

/-
Today we will do some combinatorics and elementary number theory
-/


section finite_sets
/-
We already saw that for a type `X` we can define a
type of subsets of `X` as `Set X`.
We can also define a type of finite subsets of `X` as `Finset X`.
-/
variable (X : Type*)
#check Finset X
/-
`Finset` has the same constructors as `Set`
-/

variable (A B C : Finset X) [DecidableEq X]
/-
Note, here we need to assume that `X` has a decidable equality.
-/
#check DecidableEq X
/-
It logical assumption about a type, which allows determining the finiteness of a subset.
-/

#check A ∩ B
#check A ∪ B
#check A \ B
#check (∅ : Finset ℕ)
/-
Many common types are known to be decidable, such as `ℕ`.
-/
variable (C D : Finset ℕ)
#check C ∩ D
/-
Besides the regular operations, finite subsets have a well-defined cardinality.
-/
#check A.card

/-
If we open the namespace `Finset`, we can simplify the notation.
-/

open Finset
#check A.card
#check #A

example : A.card = #A := by rfl
example : (∅ : Finset X).card = 0 := by rfl

/-
We can use our previous set builder notation to construct finite sets.
-/
#check ({0, 2, 5} : Finset Nat)

example : Finset ℕ := {0, 1, 2}

example : ({0, 1, 2} : Finset Nat).card = 3 := by rfl

/-Finally we can define `Fintype` with the property that the total subset is finite. -/

#check Fintype

variable (X : Type*) [Fintype X]
/-
For a `Fintype` we can also define a cardinality.
-/
example : ℕ :=  Fintype.card X
/-
As usual, if we want to avoid the `Fintype.`, we can open the namespace.
-/
open Fintype

example : ℕ := card X

/-
We can now see that the cardinality of the `Fintype` recovers
the cardinality of the maximal subset.
-/
#check Finset.univ
#print Finset.univ

example : (Finset.univ : Finset X).card  = card X := by rfl
example : (@Finset.univ X _ ).card  = card X := by rfl
/-
Note here is an interesting examples, where Lean could not figure out the instance
(or maybe I overcomplicated things).
-/
end finite_sets

section combinatorics
/-
In the last section we defined finite sets.
We in particular saw it comes with a well-defined notion of cardinality.
In this section we will review some combinatorial facts about finite sets.
-/

open Finset Fintype

/-
we will start with operations on finite subsets of a type.
-/
variable {α β : Type*} [DecidableEq α] [DecidableEq β] (s t : Finset α) (f : α → β)

example : #(s ×ˢ t) = #s * #t := by rw [card_product]
example : #(s ×ˢ t) = #s * #t := by simp

example : #(s ∪ t) = #s + #t - #(s ∩ t) := by rw [card_union]

example (h : Disjoint s t) : #(s ∪ t) = #s + #t := by rw [card_union_of_disjoint h]
example (h : Disjoint s t) : #(s ∪ t) = #s + #t := by simp [h]

example (h : Function.Injective f) : #(s.image f) = #s := by rw [card_image_of_injective _ h]

example (h : Set.InjOn f s) : #(s.image f) = #s := by rw [card_image_of_injOn h]

/-
Similarly, if a type is a `Fintype`, then it has a well-defined cardinality.
-/
variable {α β : Type*} [Fintype α] [Fintype β]

example : card (α × β) = card α * card β := by simp

example : card (α ⊕ β) = card α + card β := by simp

example (n : ℕ) : card (Fin n → α) = (card α)^n := by simp

end combinatorics

section natural_numbers
/-
Elementary number theory studies the properties of the natural numbers.
So, let's review some basic notions.
-/

/-
Natural numbers have two equal notations.
-/
#check ℕ
#check Nat

example : ℕ = Nat := by rfl

/-
Natural numbers are an example of an `inductive type`.
An inductive type is a type that is defined by specifying its constructors.
-/

#print Nat
#print Nat.rec


def recursion {X : Type} (x : X) (f : X → X) : ℕ → X
  | 0 => x
  | n + 1 => f (recursion x f n)

def recursion' {X : Type} (x : X) (s : X → X) : ℕ → X :=
  Nat.rec x (fun _ y => s y)

-- Here is a simple example define factorial using recursion.
def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

/-
We can use induction to define many functions, wihch you can try in the exercises.

The recursion principle implies that `Nat` comes with an induction principle.
It also comes with an induction tactics, that are very useful.

Indeed, there are at least three ways to use tactics for `ℕ`:
- `induction`
- `cases`
- `induction'`

Here is a simple example of all three tactics:
-/


example (n : ℕ) : n  ≥ 0 := by
  induction n with
  | zero => rfl
  | succ n nh => {
    calc
      n + 1 ≥ n := Nat.le_succ n
      _     ≥  0 := nh
    }

example (n : ℕ) : n  ≥ 0 := by
  cases n with
  | zero => rfl
  | succ n => calc
      n + 1 ≥ n := Nat.le_succ n
      _     ≥  0 := Nat.zero_le n

example (n : ℕ) : n  ≥ 0 := by
  induction' n with n nh
  · rfl
  · calc
      n + 1 ≥ n := Nat.le_succ n
      _     ≥  0 := Nat.zero_le n

/-
We can also use `rcases` when trying to prove something in `ℕ`, but that does not do induction.
It rather separates out into `n = 0` and `n > 0`.
-/

example (n : ℕ) : n  ≥ 0 := by
  rcases n with n | nh
  · rfl
  · simp

/-
In this case it wasn't useful at all, but it's good to know.
-/
end natural_numbers

section number_theory
/-
Let's look at some elementary number theory.
We start by reviewing some relevant definitions.
-/

/-
Recall that `k ∣ n` means that `k` divides `n` i.e.
there exists a natural number `m` such that `n = k * m`.
Here `∣` is given by `\|` and denotes "divides".
-/
example : (2 ∣ 4) := by
  use 2

example : (3 ∣ 18) := by
  use 6

example : ¬ (3 ∣ 5) := by
  intro ⟨ k, h ⟩
  cases k with
  | zero => simp at h
  | succ k => cases k with
    | zero => simp at h
    | succ k =>  {
      have step : 3 * (k + 1 + 1) > 5 := by
        calc
          3 * (k + 1 + 1) = 3 * k + 6 := by rfl
          _ ≥ 6 := by simp
          _ > 5 := by simp
      rw [← h] at step
      contradiction
    }

example : ¬ (3 ∣ 5) := by
  intro ⟨k, h⟩
  match k with
  | 0 => simp at h  -- 3 * 0 = 0 ≠ 5
  | 1 => simp at h  -- 3 * 1 = 3 ≠ 5
  | k' + 2 =>
    -- Now k ≥ 2, so 3 * k ≥ 6 > 5, contradiction
    have step : 3 * (k' + 2) > 5 := by
      calc
        3 * (k' + 2) = 3 * k' + 6 := by ring
        _ ≥ 6 := Nat.le_add_left _ _
        _ > 5 := by decide
    rw [← h] at step
    contradiction


/-
When things don't divide we can use gcd, to see what the
biggest common divisor is.
-/
#check gcd
#check gcd 12 9

example : gcd 12 9 = 3 := by rfl

/-
`Nat.Coprime` tells us whether two numbers are coprime.
-/
#check Nat.Coprime
#print Nat.Coprime

example : Nat.Coprime 2 3 := by
  rfl

example : Nat.Coprime 12 7 := by
  rfl

/- `Nat.Prime` tells us whether a number is prime. -/
#check Nat.Prime
#print Nat.Prime

example : Nat.Prime 2 := by
  decide

example : Nat.Prime 7 := by
  decide

/- For some numbers there is an explicit proof.-/
#check Nat.prime_three

#check Nat.dvd_mul
end number_theory

section irrationals

/-
Let us try our first theorem.
We want to prove that the square of `2` is not rational.
As usual the proof requires several steps.

First we want to see that if `2 ∣ m ^ 2` then `2 ∣ m`.
Let us prove this in four different ways.
-/

theorem even_of_even_sqr₄ {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two] at h
  rw [Nat.prime_two.dvd_mul] at h
  rcases h with h1 | h2
  · exact h1
  · exact h2

theorem even_of_even_sqr₃ {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two] at h
  rw [Nat.prime_two.dvd_mul] at h
  cases h
  · assumption
  · assumption

theorem even_of_even_sqr₂ {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

theorem even_of_even_sqr₁ {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

/-
Finally, for every natural number `n` we can generate the list
of all prime factors of `n`.
-/
#check Nat.primeFactorsList
#eval Nat.primeFactorsList 36

example : 2 ∈ Nat.primeFactorsList 36 := by
  simp


/-
In general, constructing such a list is not easy.
Here are some facts that can help us.
-/
#check Nat.prime_of_mem_primeFactorsList
#check Nat.prod_primeFactorsList
#check Nat.primeFactorsList_unique


/-
In the exercises we want to use the prime factorization list to prove that
the square root of `2` is not rational. For that we need some computational
facts about the prime factorization of a number.
-/
theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

set_option trace.Meta.Tactic.simp true
theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

/-
With the theorem at hand we can now prove that the
square root of `2` is not rational.

See `Exercise8`.
-/
end irrationals


section infinite_primes
/-
We now review a very classical theorem in
elementary number theory, namely that there
are infinitely many primes.
-/

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat apply Nat.succ_le_succ
    apply zero_le

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m <;> contradiction

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  revert h0 h1
  revert h m
  decide

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  match m with
  | 0 => exfalso; exact h0 rfl
  | 1 => exfalso; exact h1 rfl
  | m + 2 => simp

/-
As part of the lecture we establish the following theorem.
It will be necessary when trying to prove that there are infinitely many primes.
-/
theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  -- We first consider the case where `n` is prime.
  · use n, np
  -- For the rest of the proof we assume that `n` is not prime.
  · induction' n using Nat.strong_induction_on with n ih
  -- We now proceed by strong induction on `n`.
  -- This means we assume the result holds for all `m < n`.
    rw [Nat.prime_def_lt] at np
    push_neg at np
    rcases np h with ⟨m, mltn, mdvdn, mne1⟩
    /-
    Up to here we established that `n` has a factor `m` that is less than `n`.
    If we establish that `m` is bigger than `2`, then we can use
    the strong induction hypothesis to deduce that `m` has a prime factor.
    -/
    have : m ≠ 0 := by
      intro mz
      rw [mz, zero_dvd_iff] at mdvdn
      linarith

    have mgt2 : 2 ≤ m := two_le this mne1
    -- Almost done!
    by_cases mp : m.Prime
    -- Either `m` is prime itself:
    · use m, mp
    -- Or `m` is not prime, in which case it has a prime factor.
    · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
      use p, pp
      apply pdvd.trans mdvdn

/-
With this theorem we can now prove that there are infinitely many primes.
See `Exercise8`.
-/

end infinite_primes
