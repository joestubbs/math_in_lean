import Mathlib.Tactic
import Mathlib.SetTheory.Ordinal.Arithmetic

open BigOperators
open Finset


--  Function defining the nth Euclid number:
def euclid : ℕ -> ℕ
  | 0 => 1
  | 1 => 2
  | n+1 => (euclid n)^2 - (euclid n) + 1

#eval euclid 4 = 43
#eval ∏ x ∈ range 3, euclid (x+1) + 1 = 43

-- Helper lemma needed for the Euclid identity
theorem factor (n : ℕ) : n^2 - n = n*(n-1) := by
  rw [Nat.pow_two]
  exact Eq.symm (Nat.mul_sub_one n n)

-- A basic identity about the Euclid numbers; this is the definition
-- given in Knuth.
theorem euc_id1 (n : ℕ) (h: n ≥ 1): euclid n = ∏ x ∈ range (n-1), euclid (x+1) + 1 := by
  induction' n with n ih
  · contradiction
  · cases n
    · rw [euclid]
      simp
    · rename_i n
      simp
      rw [euclid]
      simp
      rw [factor]
      rw [Finset.prod_range_succ]
      rw [mul_comm]
      apply mul_eq_mul_right_iff.mpr
      constructor
      simp at ih
      rw [ih]
      simp
      intro
      contradiction



-- Below is some scratch work experimenting with alternative ways of defining
-- the Euclid numbers.

-- Start with some list definitions
open List

-- A function that returns a list natural numbers between 1
-- and the input, inclusive.
def LNat (x : ℕ) : (List ℕ) :=
  if x = 0 then
    []
  else if x = 1 then
    [1]
  else
    List.append (LNat (x-1)) [x]

#eval LNat 3

def mult (a b : ℕ) := a * b

#eval mult 2 3

#eval List.foldl mult 1 (LNat 4)


-- Define the euclid numbers function, returned as a list
def Leuc (x : ℕ) : (List ℕ) :=
  if x = 0 then
    [1]
  else if x = 1 then
    [1, 2]
  else
    -- compute the product of all previous euclid numbers and add 1
    -- then append it to the list
    List.append (Leuc (x-1)) [List.foldl mult 1 (Leuc (x-1)) + 1]

#eval Leuc 5
#eval Leuc 5 = [1, 2, 3, 7, 43, 1807]

#eval (Leuc 4)[4]! = 43
#eval List.foldl mult 1 (Leuc 3) = 42

#eval (Leuc 5)[1]! = 2

#eval (Leuc 5)[5]! = 1807


theorem Euc_prod (x : ℕ) (h: x ≥ 1) : (Leuc x)[x]! = List.foldl mult 1 (Leuc (x-1)) +1 := by
  induction' x with x ih
  · contradiction
  · simp
    sorry

theorem Euc_closed_form : (Leuc x)[x]! =((Leuc x)[x-1]!)^2 - (Leuc x)[x-1]! + 1  := by
  sorry


-- Explore defining the Euclid numbers using Finsets

-- First, some simple finset definitions
variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)
#check Finset.sum s f

def S_3 : (Finset ℕ ) := { 1, 2, 3 }
#eval S_3

def S_2n (n : ℕ) : (Finset ℕ ) := Finset.image (fun n => 2*n) (Finset.range n)

def S_n (n : ℕ) : (Finset ℕ ) := Finset.image (fun n => n+1) (Finset.range n)

#eval S_n 5
#eval S_2n 5


-- The range function of Finset returns a finite set of naturals,
-- from 0 to the input - 1:
#eval Finset.range 3

#eval ∏ x in S_3, x

#eval ∏ x in range 3, (x+1)

#eval Finset.range 2

#eval Finset.range 1

#eval ∏ x∈ Finset.range 0, (x+1) + 1


-- A function that returns the nth Euclid number by creating
-- a product over a Finset.
def euc (n : ℕ) : ℕ :=
  if n = 0 then
    1
  else if n = 1 then
    2
  else
      ∏ x ∈ range (n-1), (euc (x+1)) + 1
  termination_by n
  decreasing_by sorry

#eval! euc 1 = 2
#eval! euc 2 = 3
#eval! euc 3 = 7
#eval! euc 4 = 43
#eval! euc 5 = 1807


theorem range_lt (m x : ℕ) (h: x ∈ Finset.range m) : x < m := by
 exact List.mem_range.mp h

-- A slight variant on the previous definition
def euc2 (n: ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 2
  | n+1 => ∏ x ∈ (Finset.range n).attach, (euc2 (x+1)) + 1
  decreasing_by
  simp
  apply range_lt
  obtain ⟨ _, p ⟩ := x
  assumption




theorem euc_closed (n : ℕ) (h: n ≥ 1) : euc n = (euc n-1)^2 - (euc n-1) + 1 := by
  induction' n with n ih
  · contradiction
  sorry
    -- cases n
    -- · simp
    --   have h1: euc 1 = 2 := by sorry;
    -- · simp
