import Mathlib.Computability.Primrec
import Mathlib.Computability.Partrec
import Mathlib.Computability.Reduce
import Mathlib.Data.Part
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Lemma
import Lean.Elab.Tactic.Basic

/-
Defining oracle computability and Turing degrees. Following http://www.piergiorgioodifreddi.it/wp-content/uploads/2010/10/CRT1.pdf
-/

/-
The type of partial functions recursive in an oracle g is the smallest type containing
the constant zero, the successor, left and right projections, the oracle g, and is closed under
pairing, composition, primitive recursion, and μ-recursion.
-/
inductive RecursiveIn (g : ℕ →. ℕ) : (ℕ →. ℕ) → Prop
  | zero : RecursiveIn g (λ _ => 0)
  | succ : RecursiveIn g Nat.succ
  | left : RecursiveIn g (λ n => (Nat.unpair n).1)
  | right : RecursiveIn g (λ n => (Nat.unpair n).2)
  | oracle : RecursiveIn g g
  | pair {f h : ℕ →. ℕ} (hf : RecursiveIn g f) (hh : RecursiveIn g h) :
      RecursiveIn g (λ n => (Nat.pair <$> f n <*> h n))
  | comp {f h : ℕ →. ℕ} (hf : RecursiveIn g f) (hh : RecursiveIn g h) :
      RecursiveIn g (λ n => h n >>= f)
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

/-
f is turing reducible to g if f is recursive in g
-/
def turing_reducible (f g : ℕ →. ℕ) : Prop :=
  RecursiveIn g f

infix:50 "≤ᵀ" => turing_reducible

def turing_equivalent (f g : ℕ →. ℕ) : Prop :=
  f ≤ᵀ g ∧ g ≤ᵀ f

infix:50 "≡ᵀ" => turing_equivalent

-- Proof that turing_reducible is reflexive
theorem turing_reduce_refl (f : ℕ →. ℕ) : f ≤ᵀ f := RecursiveIn.oracle

theorem turing_red_refl : Reflexive turing_reducible := λ f => turing_reduce_refl f

-- Proof that turing_equvalent is reflexive
theorem turing_equiv_refl : Reflexive turing_equivalent := λ f => ⟨turing_reduce_refl f, turing_reduce_refl f⟩

-- Proof that turing_reducible is symmetric
theorem turing_equiv_symm {f g : ℕ →. ℕ} (h : f ≡ᵀ g) : g ≡ᵀ f :=
  ⟨h.2, h.1⟩

-- Proof that turing_equivalent is symmetric
theorem turing_equiv_symmetric : Symmetric turing_equivalent := λ _ _ => turing_equiv_symm

-- Proof that turing_reducible is transitive
theorem turing_reduce_trans {f g h : ℕ →. ℕ} :
  f ≤ᵀ g → g ≤ᵀ h → f ≤ᵀ h := by
  intro hg hh
  unfold turing_reducible at *
  generalize (fun a ↦ Part.some (f a)) = fp at *
  induction hg
  · apply RecursiveIn.zero
  · apply RecursiveIn.succ
  · apply RecursiveIn.left
  · apply RecursiveIn.right
  · apply hh
  case pair f' h' _ _ hf_ih hh_ih =>
    apply RecursiveIn.pair
    · apply hf_ih
    · apply hh_ih
  case comp f' h' _ _ hf_ih hh_ih =>
    apply RecursiveIn.comp
    · apply hf_ih
    · apply hh_ih
  case prec f' h' _ _ hf_ih hh_ih =>
    apply RecursiveIn.prec
    · apply hf_ih
    · apply hh_ih
  case rfind f' _ hf_ih =>
    apply RecursiveIn.rfind
    · apply hf_ih

#check Lean.Elab.Tactic.TacticM

-- Proof that turing_equivalent is transitive
theorem turing_equiv_trans : Transitive turing_equivalent :=
λ _ _ _ ⟨fg₁, fg₂⟩ ⟨gh₁, gh₂⟩ => ⟨turing_reduce_trans fg₁ gh₁, turing_reduce_trans gh₂ fg₂⟩

-- Equivalence relation instance for turing_equivalent
instance : Equivalence (turing_equivalent) where
  refl := turing_equiv_refl
  symm := turing_equiv_symm
  trans := @turing_equiv_trans
