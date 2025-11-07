import Computability.Oracle
import Computability.TuringDegree
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring

/-

Plan

1. Curry-Howard Correspondence
  - Lemma about Props, term as its proof
  - Combine contrapositives
  - Look into core

2. Equality
  - Define f and g (ℕ² → ℕ)
  - Attempt 1: simp
  - Attempt 2: congr
  - Attempt 3: one_mul

3. Combining Proofs
  - Show odd squares are 1 mod 2
  - Show even squares are not 1 mod 2
  - Combine to show biconditional
  - Collatz example

4. Quotients
  - Definition
  - Relationship to propext + funext

-/

namespace Demo

/-
            Curry-Howard Correspondence
-/

lemma trivial_3 : ∀ {A B : Prop}, A ∨ B ↔ B ∨ A := by
  aesop

lemma combine_contrapositives' : ∀ {A B : Prop}, (A → B) → (¬ A → ¬ B) → (A ↔ B) := by
  intro A
  intro B
  intro H1
  intro H2
  constructor
  case mp =>
    exact H1
  case mpr =>
    contrapose
    exact H2

lemma trivial : 2 + 2 = 4 := by
  simp

lemma trivial_2 (x y : ℕ) : (x + y) ^ 2 = (x ^ 2) + (2 * y * x) + (y ^ 2) := by
  ring_nf

#check ℕ

#check iff_def







/-
            Equality
-/
def f (x y : ℕ) : ℕ := x + y
def g (x y : ℕ) : ℕ := 1 * (x + y)

lemma simple_addition_works : f 2 3 = f 1 4 := by
  unfold f
  simp

lemma simple_addition_does_not_work : f 2 3 = f 1 4 := by
  congr
  all_goals sorry

lemma simple_addition_with_some_help : f 2 3 = f 1 4 := by
  aesop

#check funext₂ (f := f) (g := g)
#check one_mul

lemma simple_addition_hard_work : f = g := by
  unfold f g
  funext x y
  rw [one_mul]























/-
            Combining Proofs
-/

#check combine_contrapositives'

def Even (n : ℕ) : Prop := n % 2 = 0

theorem even_iff_equiv_zero {n : ℕ} : Even n ↔ Even (n ^ 2) := sorry

lemma even_square_equiv_zero {n : ℕ}  : Even n → Even (n ^ 2) := by
  intro n_even
  unfold Even at *
  apply (@Nat.ModEq.pow 2 n 0 2) n_even

lemma odd_square_not_equiv_zero {n : ℕ} : (¬ Even n) → (¬ Even (n ^ 2)) := by
  intro not_n_even
  intro n_sq_even
  apply not_n_even
  unfold Even at *
  clear not_n_even
  apply (@Nat.modEq_zero_iff_dvd 2 n).mpr
  apply (@Nat.modEq_zero_iff_dvd 2 (n ^ 2)).mp at n_sq_even
  have two : 2 = 1 + 1 := by aesop
  nth_rewrite 2 [two] at n_sq_even
  rw [pow_add] at n_sq_even
  simp at *
  rw [Nat.prime_two.dvd_mul] at n_sq_even
  cases' n_sq_even; repeat assumption

theorem even_iff_equiv_zero' : Even n ↔ Even (n ^ 2) := by
  apply combine_contrapositives' even_square_equiv_zero odd_square_not_equiv_zero





def collatz := fun n => if n % 2 == 0 then n / 2 else 3 * n + 1

def collatz_iterated := fun (num_times n : ℕ) =>
  if num_times = 0 then (n = 1) else collatz_iterated (num_times - 1) (collatz n)

theorem collatz_conjecture : ∀ n, ∃ num_times, collatz_iterated num_times n := by
 sorry


/-
100 Famous Theorems
https://leanprover-community.github.io/100.html

6. Gödel’s Incompleteness Theorems
11. The Infinitude of Primes
24. The Independence of the Continuum Hypothesis
25. Schroeder-Bernstein Theorem
36. Brouwer Fixed Point Theorem
63. Cantor’s Theorem
99. Buffon Needle Problem
-/


















/-
            Quotients

Set-theoretically, `Quotient s` can seen as the set of equivalence classes of `α` modulo the
`Setoid` instance's relation `s.r`. Functions from `Quotient s` must prove that they respect `s.r`:
to define a function `f : Quotient s → β`, it is necessary to provide `f' : α → β` and prove that
for all `x : α` and `y : α`, `s.r x y → f' x = f' y`. `Quotient.lift` implements this operation.

The key quotient operators are:
 * `Quotient.mk` places elements of the underlying type `α` into the quotient.
 * `Quotient.lift` allows the definition of functions from the quotient to some other type.
 * `Quotient.sound` asserts the equality of elements related by `r`
 * `Quotient.ind` is used to write proofs about quotients by assuming that all elements are
   constructed with `Quotient.mk`.
-/


theorem sound {α : Sort u} {s : Setoid α} {a b : α} : a ≈ b → Quotient.mk s a = Quotient.mk s b :=
  Quot.sound

#check @Quot.lift (ℕ →. ℕ) TuringEquivalent (ℕ →. ℕ)













end Demo
