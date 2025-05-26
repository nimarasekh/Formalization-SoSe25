-- Here are couple basic exercises to get you started with Lean.

section exercises1s
-- ###NON-TACTICS EXERCISES###
--  Recall that Nat are the natural numbers in Lean.
#check Nat

-- The function Nat.mul_assoc gives us the associativity of multiplication.
#check Nat.mul_assoc

variable (a b c : Nat)

-- Use the function Nat.add_assoc to complete this exercise.
-- (Do not use any tactics!)
def exercise1 : (a * b) * c = a * (b * c) := sorry

-- Of course, if a = b, then we must also have b = a
-- In fact there is a function for that:
#check Eq.symm

-- Compose your solution to the first question and Eq.symm to solve the following:
-- (Do not use any tactics!)
def exercise2:  a * (b * c) = (a * b) * c := sorry

-- We have seen addition and multiplication of natural numbers.
-- Of course they are also distributive.
-- Both left and right:
#check Nat.left_distrib
#check Nat.right_distrib

-- We already know that multiplication is commutative!
#check Nat.mul_comm
-- So we should be able to prove right distributivity directly.
-- That's hard! Let's try some first step towards it:
def exercise3 : (b + c) * a  = a * b + a * c:= sorry

-- How about actual right distributivity?
-- That's hard with direct methods and we will see how to tackle it with tactics!

-- ###TACTICS EXERCISES###
-- Let's solve questions 1-3 with tactics.
-- We will use the `rw` tactic to rewrite the left-hand side of the equation
-- to the right-hand side.

-- Let's try this out with the first exercise:
def exercise1tactics : (a * b) * c = a * (b * c) := by sorry
  -- use the tactic `rw` to rewrite the left-hand side

  -- If you are confused, Solution for exercise1tactics:
  -- rw [Nat.mul_assoc a b c]

-- Now use `rw` simililarly to solve the other two exercises:
def exercise2tactics:  a * (b * c) = (a * b) * c := by sorry

def exercise3tactics : (b + c) * a  = a * b + a * c:= by sorry

-- Now, we can use the `rw` tactic to solve the exercise 4:
def exercise4 : (b + c) * a  = b * a + c * a:= by sorry

end exercises1s
-- --------------------------------------------
section general_stuff
-- some of my own notes
#check And
variable (p q r: Prop)
#check And p q
#check p ∧ q

variable (t : p)
#check t

end general_stuff

section proposition_as_types

variable {p q : Prop}
theorem t1a: p → q → p := fun hp : p ↦ fun hq : q ↦ hp

theorem t1 (hp : p) (hq : q) : p := hp
#check t1

#print t1

axiom h : p
#check h

theorem t2: q → p := (t1  h)

end proposition_as_types

section lean_syntax

#eval String.append "Hello, " "lean"

#eval String.append "it is " (if 1>2 then "yes" else "no")

#eval (1-2 : Int)

def add1 (n : Nat) : Nat := n+1
#eval add1 2

#check add1

def Str : Type := String

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := {x:= 0.0, y := 0.0}
#eval origin

def zeroX (p : Point) : Point := {p with x := 0}

#check Point.x

#eval "something ".append " else"

def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
{ x := f p.x, y :=  f p.y}

end lean_syntax
