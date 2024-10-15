import Mathlib.Computability.Primrec
import Mathlib.Computability.Partrec
import Mathlib.Computability.Reduce
import Mathlib.Data.Part
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Lemma
/-
Defining oracle computability and Turing degrees. Following http://www.piergiorgioodifreddi.it/wp-content/uploads/2010/10/CRT1.pdf
-/

inductive RecursiveIn (g : ℕ → ℕ) : (ℕ →. ℕ) → Prop
  | zero : RecursiveIn g (λ _ => 0)
  | succ : RecursiveIn g Nat.succ
  | left : RecursiveIn g (λ n => (Nat.unpair n).1)
  | right : RecursiveIn g (λ n => (Nat.unpair n).2)
  | oracle : RecursiveIn g g
  | pair {f h : ℕ →. ℕ} (hf : RecursiveIn g f) (hh : RecursiveIn g h) :
      RecursiveIn g (λ n => (pair <$> f n <*> h n))
  | comp {f h : ℕ →. ℕ} (hf : RecursiveIn g f) (hh : RecursiveIn g h) :
      RecursiveIn g (λ n => f n >>= h)
  | prec {f h : ℕ →. ℕ} (hf : RecursiveIn g f) (hh : RecursiveIn g h) :
      RecursiveIn g (λ p =>
        let (a, n) := Nat.unpair p
        n.rec (f a) (λ y IH => do
          let i ← IH
          h (Nat.pair a (Nat.pair y i))
        )
      )
  | rfind {f : ℕ →. ℕ} (hf : RecursiveIn g f) :
      RecursiveIn g (λ a =>
        Nat.rfind (λ n => (λ m => m = 0) <$> f (Nat.pair a n))
      )

def turing_reducible (f g : ℕ → ℕ) : Prop :=
  RecursiveIn g (λ n => Part.some (f n))

infix:50 "≤ᵀ" => turing_reducible

def turing_equivalent (f g : ℕ → ℕ) : Prop :=
  f ≤ᵀ g ∧ g ≤ᵀ f

infix:50 "≡ᵀ" => turing_equivalent

theorem turing_reduce_refl (f : ℕ → ℕ) : f ≤ᵀ f := RecursiveIn.oracle

theorem turing_equiv_symm {f g : ℕ → ℕ} (h : f ≡ᵀ g) : g ≡ᵀ f :=
  ⟨h.2, h.1⟩

def characteristic_function (A : ℕ → Prop) [∀ n, Decidable (A n)] : ℕ → ℕ
  | n => if A n then 1 else 0

def turing_reducible_sets (A B : ℕ → Prop) [∀ n, Decidable (A n)] [∀ n, Decidable (B n)] : Prop :=
  (characteristic_function A) ≤ᵀ (characteristic_function B)

theorem turing_reduce_trans {f g h : ℕ → ℕ} :
  f ≤ᵀ g → g ≤ᵀ h → f ≤ᵀ h := by
  -- the idea here is that if f is recursive in g then g can be used to compute f, but since g is recursive in h, h can be used to compute g, which can be used to compute f, so f is recursive in h, ie. f ≤ᵀ h
  intro hg hh
  unfold turing_reducible at *
  generalize (fun n ↦ Part.some (f n)) = fp at *
  induction hg
  · apply RecursiveIn.zero
  · apply RecursiveIn.succ
  · apply RecursiveIn.left
  · apply RecursiveIn.right
  · apply hh
  case pair pair f' h' g' gh_ih1 hf_ih2 hh' => sorry
