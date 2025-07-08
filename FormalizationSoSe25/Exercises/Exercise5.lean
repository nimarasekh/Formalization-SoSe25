import Mathlib.Tactic

section triple_constructors

-- Recall the integers are defined as `\bZ`.
#check ℤ

@[ext]
structure new_triple where
   x : ℤ
   y : ℤ
   z : ℤ

/-
Use `structure` to construct a new constructor:
* It is called `new_triple`
* The data should be three integers `x` `y` `z` in `ℤ`
* It should satisfy `extensionality`
-/

/-
Now, solve the following exercises about `new_triple`:




1. Create three instances of `new_triple` using three different approaches:
   * With `.mk`
   * With `⟨⟩`
   * With `where`
   using the numbers `x = 1`, `y = 2`, `z = -3`.
-/

def t1 :  new_triple := new_triple.mk 1 2 3
#check t1

def t2 : new_triple := ⟨1, 2, 3⟩
def t3 : new_triple where
   x := 1
   y := 2
   z := 3
/-
2. Uncomment the following line and prove it.
-/

example (x₁ y₁ z₁ x₂ y₂ z₂ : ℤ) : (x₁ = x₂) ∧ (y₁ = y₂) ∧ (z₁ = z₂) ↔ (⟨x₁, y₁, z₁⟩ : new_triple )= (⟨x₂, y₂, z₂⟩ : new_triple) := by
   constructor
   rintro ⟨e1, e2, e3⟩
   ext
   exact e1
   exact e2
   exact e3

   intro h
   obtain ⟨h1, h2, h3⟩ := h
   simp










/-
3. Define a namespace `new_triple` and define the following functions:
    * `add` that adds two `new_triple` objects.
    * `mul` that multiplies two `new_triple` objects.
    * `sub` that subtracts two `new_triple` objects.
  Close the namespace `new_triple`.
-/

namespace new_triple

   def add(a b : new_triple) : new_triple where
      x := a.x + b.x
      y := a.y + b.y
      z := a.z + b.z

    def mul(a b : new_triple) : new_triple where
      x := a.x * b.x
      y := a.y * b.y
      z := a.z * b.z

    def sub(a b : new_triple) : new_triple where
      x := a.x - b.x
      y := a.y - b.y
      z := a.z - b.z

end new_triple

/-
4. Use `#eval` to compute
    * addition of `⟨1, 2, -3⟩` and `⟨2, -5, 6⟩)`
    * multiplication of `(⟨2, -3, 2⟩` and `⟨1, -2, 2⟩`
    * subtraction of `⟨-1, 2, -3⟩` and `⟨4, 1, 3⟩)`
   For this you want to use `#eval` to evaluate an expression.
-/

#eval new_triple.add ⟨1, 2, -3⟩ ⟨2, -5, 6⟩


/-
5. Reopen the namespace `new_triple` and prove:
   * `mul` is commutative by defining and proving `mul_comm`.
   * `mul` is associative by defining and proving `mul_assoc`.
   Close the namespace `new_triple`.
-/

open new_triple
def new_triple.mul_comm (a b : new_triple) : mul a b = mul b a := by
   ext
   simp [mul]
   ring
   simp [mul]
   ring
   simp [mul]
   ring


def new_triple.mul_assoc(a b : new_triple) : mul (mul a b) c = mul a (mul b c) := by
   ext
   simp [mul]
   ring
   simp [mul]
   ring
   simp [mul]
   ring



/-
6. Use `#check` to compare the definition of `new_triple.mul_comm` and `mul_comm`.
-/
#check new_triple.mul_comm
#check mul_comm


end triple_constructors
