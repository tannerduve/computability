import Mathlib.Computability.Primrec
import Mathlib.Computability.Partrec
import Mathlib.Computability.Reduce


inductive RecursiveIn (g : ℕ → ℕ) : (ℕ →. ℕ) → Prop
  | zero : RecursiveIn g (pure 0)
  | succ : RecursiveIn g succ
  | left : RecursiveIn g (↑fun n : ℕ => (Nat.unpair n).1)
  | right : RecursiveIn g (↑fun n : ℕ => (Nat.unpair n).2)
  | oracle : RecursiveIn g (pure ∘ g)
  | pair {f h : ℕ →. ℕ} (hf : RecursiveIn g f) (hh : RecursiveIn g h) :
      RecursiveIn g (fun n => pair <$> f n <*> h n)
  | comp {f h : ℕ →. ℕ} (hf : RecursiveIn g f) (hh : RecursiveIn g h) :
      RecursiveIn g (fun n => h n >>= f)
  | prec {f h : ℕ →. ℕ} (hf : RecursiveIn g f) (hh : RecursiveIn g h) :
      RecursiveIn g (fun p =>
        let (a, n) := Nat.unpair p
        n.rec (f a) (fun y IH => do
          let i ← IH
          h (Nat.pair a (Nat.pair y i))
        )
      )
  | rfind {f : ℕ →. ℕ} (hf : RecursiveIn g f) :
      RecursiveIn g (λ a =>
        Nat.rfind (λ n =>
          (λ m => m = 0) <$> f (Nat.pair a n)
        )
      )

/-
part monad definition
def part (α : Type*) := Σ p : Prop, (p → α)

instance monad (part : Type → Type)
pure : Π {α : Type}, α → part α
bind : Π {α β : Type}, part α → (α → part β) → part β
pure a = ⟨true, λ _, a⟩
bind (p, f) g = ⟨(∃ h : p, g (f (h)).1), (λ h => (g (f (h.1)).2 h.2))⟩
m >>= f = bind m f
-/
