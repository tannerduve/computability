import Mathlib.Computability.Primrec
import Mathlib.Computability.Partrec
import Mathlib.Computability.Reduce
import Mathlib.Computability.TuringDegree
import Mathlib.Data.Part
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Lemma





infix:50 " ≤ᵀ " => TuringReducible
infix:50 " ≡ᵀ " => TuringEquivalent

-- Need to show: addition, multiplication, ITE, modular arithmetic

def empty : Set (ℕ →. ℕ) := {λ _ => 0}

def Recursive (f : ℕ →. ℕ) : Prop :=
  RecursiveIn empty f

def join (f g : ℕ →. ℕ) : ℕ →. ℕ :=
  λ n =>
    if n % 2 = 0 then
      (f (n / 2)).map (λ x => 2 * x)
    else
      (g (n / 2)).map (λ y => 2 * y + 1)

infix:99 "⊔" => join

-- Essentially left (and right) of the inverse of join
def twice_into_that_monad : ℕ →. ℕ := λ n => Part.some n

def inl_join (f : ℕ →. ℕ) : ℕ →. ℕ :=
  λ n => (f n).map (λ x => 2 * x)

def inr_join (f : ℕ →. ℕ) : ℕ →. ℕ :=
  λ n => (f n).map (λ x => 2 * x + 1)

lemma inl_join_left_inverse : ∀ h, (λ n => ((f n).map (λ x => 2 * x))) ⊔ ((inr_join h) ∘ (λ n => n / 2)) = f := by
  intro h
  sorry



lemma inl_join_inverse : ∀ h, inl_join (join f h) = f := by
  -- intro h
  -- apply funext
  -- intro x
  -- unfold inl_join
  -- unfold join


  -- unfold inl_join
  -- simp
  -- unfold join
  -- simp
  sorry


lemma inr_join_inverse : ∀ h, inr_join (join h g) = g := sorry


lemma reduce_join {f g : ℕ →. ℕ} :
  f ≤ᵀ (f ⊔ g) ∧ g ≤ᵀ (f ⊔ g) := by
  constructor
  unfold TuringReducible
  sorry
  sorry



  -- have f_equiv_to_inl_join : f =
  -- apply RecursiveIn.comp (O := {f⊔g})
-- I want to write an expression that calculates f from f⊔g and have to inl
-- So to write it as a composition of other functions, do it monadically
-- and just apply composition


lemma reduce_join₁ {f g h : ℕ →. ℕ} :
  f ≤ᵀ h → g ≤ᵀ h → f ⊔ g ≤ᵀ h := sorry

-- lemma add_partrec : ∀ (x y : ℕ),

-- WANT --
theorem join_recursive : ∀ (f g: ℕ →. ℕ), Recursive (join f g) := sorry


/-
Lean for DLampz
-/

-- Define some functions
def double : ℕ -> ℕ :=
  fun n => 2 * n
def double_as_sum : ℕ -> ℕ :=
  fun n => n + n

def add_three : ℕ -> ℕ :=
  fun n => n + 3

#eval double 9
#eval double_as_sum 9



-- Want to show that double = double_as_sum
-- Same as showing for every n, double n = double_as_sum n

theorem doubles_equiv : ∀ n, double n = double_as_sum n := by
  intro n
  unfold double
  unfold double_as_sum
  induction n
  case zero =>
    simp
  case succ k ih =>
    rw [mul_add]
    simp
    rw [ih]
    simp [Nat.add_add_add_comm k 1 k 1]

#check @funext ℕ (fun _ => ℕ) double double_as_sum doubles_equiv

theorem doubles_equiv' : double = double_as_sum :=
  funext doubles_equiv

lemma add_three_intersects_double : ∃ n, add_three n = double n := by
  use 3
  simp [add_three, double]

lemma false_implies_all : ∀ (P : Prop), False -> P := by
  intro P F
  have H : Or False P := by
    left
    exact F
  rw [false_or] at H
  exact H

lemma add_three_not_double : ¬ (∀ n, add_three n = double n) := by
  intro contra
  specialize contra 10

  -- simp [add_three, double] at contra

  unfold add_three at contra
  unfold double at contra
  simp at contra
