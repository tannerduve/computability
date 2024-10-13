import Mathlib.Computability.Primrec
import Mathlib.Computability.Partrec
import Mathlib.Computability.Reduce

inductive PartrecOracle : (ℕ →. ℕ) → Prop :=
| zero : PartrecOracle (λ _ => 0)
| succ : PartrecOracle Nat.succ
| left : PartrecOracle fun (n : ℕ) => (Nat.unpair n).1
| right: PartrecOracle fun (n : ℕ) => (Nat.unpair n).2
| pair : ∀ {f g : ℕ →. ℕ},
  PartrecOracle f → PartrecOracle g → PartrecOracle fun (n : ℕ) => Seq.seq (Nat.pair <$> f n) fun (x : Unit) => g n
| comp: ∀ {f g : ℕ →. ℕ}, PartrecOracle f → PartrecOracle g → PartrecOracle fun (n : ℕ) => g n >>= f
| prec : ∀ {f g : ℕ →. ℕ},
  PartrecOracle f →
    PartrecOracle g →
      PartrecOracle
        (Nat.unpaired fun (a n : ℕ) =>
          Nat.rec (f a)
            (fun (y : ℕ) (IH : Part ℕ) => do
              let i ← IH
              g (Nat.pair a (Nat.pair y i)))
            n)
| rfind : ∀ {f : ℕ →. ℕ},
  PartrecOracle f →
    PartrecOracle fun (a : ℕ) => Nat.rfind fun (n : ℕ) => (fun (m : ℕ) => decide (m = 0)) <$> f (Nat.pair a n)
| oracles {f : ℕ →. ℕ} : PartrecOracle f
