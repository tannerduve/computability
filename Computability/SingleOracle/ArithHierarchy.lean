import Computability.SingleOracle.Jump

noncomputable section

def Delta0_0 (A : Set ℕ) [DecidablePred A] : Prop := True
def Sigma0_0 := Delta0_0
def Pi0_0 := Delta0_0

/-
Iterated jump operator
-/
def TuringJump (n : ℕ) (f : ℕ →. ℕ) : ℕ →. ℕ :=
  match n with
  | 0 => f
  | n + 1 => (TuringJump n f)⌜

/-- The `n`-fold jump of the empty oracle (totally undefined). Used as an oracle function. -/
def arithJumpBase : ℕ → ℕ →. ℕ
| 0     => λ _ => Part.none
| n + 1 => jump (arithJumpBase n)

/-- The classical `∅⁽ⁿ⁾` set: the domain of the `n`-fold jump of the empty oracle. -/
def arithJumpSet (n : ℕ) : Set ℕ :=
  (arithJumpBase n).Dom

noncomputable def decidableIn (O : ℕ →. ℕ) (A : Set ℕ) : Prop :=
  ∃ f : ℕ → Bool, SingleOracle.ComputableIn O f ∧ ∀ n, A n ↔ f n = true

/-
The arithmetical hierarchy:
  Σ⁰₀ = ∆⁰₀ = Π⁰₀ = ∅
  Σ⁰₁ = {n | ∃ m, ∀ k, (m + k) ∈ A}
  Σ⁰ₙ = {n | ∃ m, ∀ k, (m + k) ∈ Σ⁰ₙ₋₁}
  Π⁰ₙ = Σ⁰ₙᶜ
  ∆⁰ₙ = Σ⁰ₙ ∩ Π⁰ₙ
-/
def Sigma0 (n : ℕ) (A : Set ℕ) : Prop :=
  match n with
  | 0 => decidableIn (fun _ => Part.none) A
  | k + 1 => recursively_enumerable_in₂ (arithJumpBase k) A

def Pi0 (n : ℕ) (A : Set ℕ) : Prop :=
  Sigma0 n Aᶜ

def Delta0 (n : ℕ) (A : Set ℕ) : Prop :=
  Sigma0 n A ∧ Pi0 n A

notation "Σ⁰_" => Sigma0
notation "Π⁰_" => Pi0
notation "Δ⁰_" => Delta0
