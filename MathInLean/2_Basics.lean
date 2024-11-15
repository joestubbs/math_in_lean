import Mathlib.Tactic

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm a c]

example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]
  rw [mul_comm a c]
  rw [mul_assoc b c a]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
 calc
   (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by rw [mul_add, add_mul, add_mul ]
   _ = a * a + (b * a + a * b) + b * b := by rw [← add_assoc, add_assoc (a * a) ]
   _ = a * a + (a * b + a * b) + b * b := by rw [mul_comm b a]
   _ = a * a + 2 * (a * b) + b * b := by rw [two_mul]


-- or, just use the ring tactic!!
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring


-- sometimes one needs to combine ring with local hypotheses, e.g.,
example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rewrite 2 [h]
  ring

variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))


example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  rw [mul_comm d a]
  ring


-- Create a local namespace to avoid conflicts with Ring theorems in Mathlib
namespace LocalRing

variable (R : Type*) [Ring R]

theorem add_zero (a : R) : a + 0 = a := by
  rw [add_comm]
  rw [zero_add] -- have to know this fact

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]


#check neg_add_cancel

theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_right_neg, add_comm, zero_add]

end LocalRing

#check add_left_cancel

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add ]
    rw [ add_zero ]
    rw [ add_zero ]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by
    rw [add_zero]
    refine add_eq_of_eq_sub ?h

  rw [add_left_cancel h]

example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a : R) : a - a = a + -a := by
  rw [sub_eq_add_neg]



theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg]
  rw [add_comm]
  rw [neg_add_cancel]


example (a : ℝ) : a - a = 0 := by
  exact self_sub ℝ a

example (a : R) : a + 0 * a = a := by

example (a b : R) : f(a b)

f(a 0*b)


example : (3 : ℝ) → 3 - 3 = 0 := by
  apply self_sub 3


-- Section 2.3

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans)

example (x y z : ℝ) (h0 : x ≤ y) (h1 : y ≤ z) : x ≤ z := by
  apply le_trans
  apply h0
  exact h1


example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
