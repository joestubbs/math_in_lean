import Mathlib.Tactic
open BigOperators
open Finset

-- Start with some list definitions
open List

-- A function that returns a list natural numbers between 1
-- and the input, inclusive.
def LNat_x (x : ℕ) : (List ℕ) :=
  if x = 0 then
    []
  else if x = 1 then
    [1]
  else
    List.append [x] (LNat_x (x-1))

#eval LNat_x 3

def mult (a b : ℕ) := a * b

#eval mult 2 3

#eval List.foldl mult 1 (LNat_x 4)


-- Define the euclid numbers function, returned as a list
def LEuc_x (x : ℕ) : (List ℕ) :=
  if x = 0 then
    []
  else if x = 1 then
    [2]
  else
    -- compute the product of all previous euclid numbers and add 1
    -- then append it to the list
    List.append (LEuc_x (x-1)) [List.foldl mult 1 (LEuc_x (x-1)) + 1]

#eval LEuc_x 5

#eval (LEuc_x 4)[3]!
#eval List.foldl mult 1 (LEuc_x 3)

#eval (LEuc_x 5)[0]!

#eval (LEuc_x 5)[4]!


theorem Euc_prod (x : ℕ) (h: x ≥ 1) : (LEuc_x x)[x-1]! = List.foldl mult 1 (LEuc_x (x-1)) +1 := by
  induction' x with x ih
  · contradiction
  · simp

theorem Euc_closed_form : (LEuc_x x)[x-1]! =((LEuc_x x)[x-2]!)^2 - (LEuc_x x)[x-2]! + 1  := by
  sorry



def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · rw [fac]
    exact zero_lt_one
  rw [fac]
  exact mul_pos n.succ_pos ih

theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  induction' n with n ih
  · exact absurd ipos (not_lt_of_ge ile)
  rw [fac]
  rcases Nat.of_le_succ ile with h | h
  · apply dvd_mul_of_dvd_right (ih h)
  rw [h]
  apply dvd_mul_right

theorem sum_id (n : ℕ) : ∑ i in range (n + 1), i = n * (n + 1) / 2 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, mul_add 2, ← ih]
  ring



-- Some finset definitions
variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)
#check Finset.sum s f

def S_3 : (Finset ℕ ) := { 1, 2, 3 }
#eval S_3


-- The range function of Finset returns a finite set of naturals,
-- from 0 to the input - 1:
#eval Finset.range 3

#eval ∏ x in S_3, x

#eval ∏ x in range 3, (x+1)

#eval Finset.range 2

#eval Finset.range 1

-- A function that returns the nth Euclid number by creating
-- a product over a set.
def euc (n : ℕ) : ℕ :=
  if n = 0 then
    1
  else if n = 1 then
    2
  else
      ∏ x ∈ range (n-1), (euc (x+1)) + 1
  termination_by n
  decreasing_by simp; sorry
  --   refine Nat.lt_of_le_of_lt x (n-1) n

#eval! euc 1
#eval! euc 2
#eval! euc 3
#eval! euc 4
#eval! euc 5

theorem euc_closed (n : ℕ) (h: n ≥ 1) : euc n = (euc n-1)^2 - (euc n-1) + 1 := by
  induction' n with n ih
  · contradiction
  · cases n
    · simp
      have h1: euc 1 = 2 := by sorry;
    · simp
