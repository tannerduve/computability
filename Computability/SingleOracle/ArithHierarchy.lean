import Computability.SingleOracle.Jump

open Nat.RecursiveIn.Code

noncomputable section

def Delta0_0 (A : Set ℕ) [DecidablePred A] : Prop := True
def Sigma0_0 := Delta0_0
def Pi0_0 := Delta0_0

/-
Iterated jump operator - works with total functions
-/
def TuringJump (n : ℕ) (f : ℕ → ℕ) : ℕ → ℕ :=
  match n with
  | 0 => f
  | n + 1 => (TuringJump n f)⌜

/-- The `n`-fold jump of the empty oracle (totally undefined). Used as an oracle function. -/
def arithJumpBase : ℕ → ℕ → ℕ
| 0     => λ _ => 0  -- Empty oracle returns 0 for all inputs
| n + 1 => (arithJumpBase n)⌜

/-- The classical `∅⁽ⁿ⁾` set: the domain of the `n`-fold jump of the empty oracle. -/
def arithJumpSet (n : ℕ) : Set ℕ :=
  {x | (eval (arithJumpBase n) (decodeCode (Nat.unpair x).1) (Nat.unpair x).2).Dom}

-- For now, we'll use a simpler definition of decidability relative to an oracle
noncomputable def decidableIn (O : ℕ → ℕ) (A : Set ℕ) : Prop :=
  ∃ f : ℕ → Bool, ComputableIn O f ∧ ∀ n, A n ↔ f n = true

-- Define recursively enumerable relative to an oracle using the infrastructure we have
noncomputable def recursively_enumerable_in (O : ℕ → ℕ) (A : Set ℕ) : Prop :=
  ∃ f : ℕ → ℕ, Nat.RecursiveIn O f ∧ A = {x | ∃ n, f (Nat.pair x n) = 1}

/-
The arithmetical hierarchy:
  Σ⁰₀ = Δ⁰₀ = Π⁰₀ = decidable sets
  Σ⁰₁ = recursively enumerable sets
  Σ⁰ₙ = sets that are r.e. in ∅⁽ⁿ⁻¹⁾
  Π⁰ₙ = complements of Σ⁰ₙ sets
  Δ⁰ₙ = Σ⁰ₙ ∩ Π⁰ₙ
-/
def Sigma0 (n : ℕ) (A : Set ℕ) : Prop :=
  match n with
  | 0 => decidableIn (λ _ => 0) A  -- Decidable without oracle
  | k + 1 => recursively_enumerable_in (arithJumpBase k) A

def Pi0 (n : ℕ) (A : Set ℕ) : Prop :=
  Sigma0 n Aᶜ

def Delta0 (n : ℕ) (A : Set ℕ) : Prop :=
  Sigma0 n A ∧ Pi0 n A

notation "Σ⁰_" => Sigma0
notation "Π⁰_" => Pi0
notation "Δ⁰_" => Delta0
