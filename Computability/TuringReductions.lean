import Mathlib.Computability.Primrec
import Mathlib.Computability.Partrec
import Mathlib.Computability.Reduce
import Mathlib.Data.Part
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Lemma

/-
Defining oracle computability and Turing degrees. Following http://www.piergiorgioodifreddi.it/wp-content/uploads/2010/10/CRT1.pdf
-/
inductive RecursiveIn (g : ℕ →. ℕ) : (ℕ →. ℕ) → Prop
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

def turing_reducible (f g : ℕ →. ℕ) : Prop :=
  RecursiveIn g f

infix:50 "≤ᵀ" => turing_reducible

def turing_equivalent (f g : ℕ →. ℕ) : Prop :=
  f ≤ᵀ g ∧ g ≤ᵀ f

infix:50 "≡ᵀ" => turing_equivalent

theorem turing_reduce_refl (f : ℕ →. ℕ) : f ≤ᵀ f := RecursiveIn.oracle

theorem turing_red_refl : Reflexive turing_reducible := λ f => turing_reduce_refl f

theorem turing_equiv_refl : Reflexive turing_equivalent := λ f => ⟨turing_reduce_refl f, turing_reduce_refl f⟩

theorem turing_equiv_symm {f g : ℕ →. ℕ} (h : f ≡ᵀ g) : g ≡ᵀ f :=
  ⟨h.2, h.1⟩

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
  case pair pair f' h' _ _ hh_ih1 hh_ih2  =>
    apply RecursiveIn.pair
    · exact hh_ih1
    · exact hh_ih2
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

theorem turing_equiv_trans : Transitive turing_equivalent :=
λ _ _ _ ⟨fg₁, fg₂⟩ ⟨gh₁, gh₂⟩ => ⟨turing_reduce_trans fg₁ gh₁, turing_reduce_trans gh₂ fg₂⟩

-- Equivalence instance for turing_equivalent
instance : Equivalence (turing_equivalent) where
  refl := turing_equiv_refl
  symm := turing_equiv_symm
  trans := @turing_equiv_trans
