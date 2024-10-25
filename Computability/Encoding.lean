import Computability.TuringReductions
import Mathlib.Data.Option.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Denumerable

open Denumerable
-- To Do: Need to write encoding for oracle partial recursive functions to define universal machine
-- and relativized versions of basic theorems (Mario's paper and Soare's book for reference).

inductive codeo : Type
| zero : codeo
| succ : codeo
| left : codeo
| right : codeo
| oracle : codeo
| pair : codeo → codeo → codeo
| comp : codeo → codeo → codeo
| prec : codeo → codeo → codeo
| rfind' : codeo → codeo

def evalo (g : ℕ →. ℕ) : codeo → ℕ →. ℕ
| codeo.zero => pure 0
| codeo.succ => Nat.succ
| codeo.left => λ n => (Nat.unpair n).1
| codeo.right => λ n => (Nat.unpair n).2
| codeo.oracle => g
| codeo.pair cf cg => fun n => Nat.pair <$> evalo g cf n <*> evalo g cg n
| codeo.comp cf cg => λ n => (evalo g cg n >>= evalo g cf)
| codeo.prec cf cg =>
   Nat.unpaired fun a n =>
    n.rec (evalo g cf a) fun y IH => do
      let i ← IH
      evalo g cg (Nat.pair a (Nat.pair y i))
| codeo.rfind' cf =>
    Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun m => m = 0) <$> evalo g cf (Nat.pair a (n + m))).map (· + m)

def encode' : codeo → ℕ :=
λ c => match c with
| codeo.zero => 0
| codeo.succ => 1
| codeo.left => 2
| codeo.right => 3
| codeo.oracle => 4
| codeo.pair cf cg => 2 * (2 * Nat.pair (encode' cf) (encode' cg)) + 5
| codeo.comp cf cg => 2 * (2 * Nat.pair (encode' cf) (encode' cg) + 1) + 5
| codeo.prec cf cg => (2 * (2 * Nat.pair (encode' cf) (encode' cg)) + 1) + 5
| codeo.rfind' cf => (2 * (2 * encode' cf + 1) + 1) + 5

def decode' : ℕ → codeo
  | 0 => codeo.zero
  | 1 => codeo.succ
  | 2 => codeo.left
  | 3 => codeo.right
  | 4 => codeo.oracle
  | n + 5 =>
    let m := n.div2.div2
    have hm : m < n + 5 := by
      simp only [m, Nat.div2_val]
      apply lt_of_le_of_lt
      exact Nat.div_le_self (n / 2) 2
      apply lt_of_le_of_lt
      exact Nat.div_le_self n 2
      linarith
    have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
    match n.bodd, n.div2.bodd with
    | false, false => codeo.pair (decode' m.unpair.1) (decode' m.unpair.2)
    | false, true  => codeo.comp (decode' m.unpair.1) (decode' m.unpair.2)
    | true , false => codeo.prec (decode' m.unpair.1) (decode' m.unpair.2)
    | true , true  => codeo.rfind' (decode' m)

theorem encode'_decode' : ∀ c, encode' (decode' c) = c :=
λ c => match c with
  | 0 => by simp [encode', decode']
  | 1 => by simp [encode', decode']
  | 2 => by simp [encode', decode']
  | 3 => by simp [encode', decode']
  | 4 => by simp [encode', decode']
  | n + 5 => by
    let m := n.div2.div2
    have hm : m < n + 5 := by
      simp only [m, Nat.div2_val]
      apply lt_of_le_of_lt
      exact Nat.div_le_self (n / 2) 2
      apply lt_of_le_of_lt
      exact Nat.div_le_self n 2
      linarith
    have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
    have IH := encode'_decode' m
    have IH1 := encode'_decode' m.unpair.1
    have IH2 := encode'_decode' m.unpair.2
    conv_rhs => rw [← Nat.bit_decomp n, ← Nat.bit_decomp n.div2]
    simp only [decode']
    cases n.bodd <;> cases n.div2.bodd <;>
      simp [encode', decode', IH, IH1, IH2, Nat.bit_val]

instance denumCode : Denumerable codeo :=
  mk'
    ⟨encode', decode', fun c => by
        induction c <;> simp [encode', decode', Nat.div2_val, *],
    encode'_decode'⟩

/-- Returns a code for the constant function outputting a particular natural. -/
def const : ℕ → codeo
  | 0 => codeo.zero
  | n + 1 => codeo.comp codeo.succ (const n)

def const_inj : ∀ {n₁ n₂}, const n₁ = const n₂ → n₁ = n₂
  | 0, 0, _ => by simp
  | n₁ + 1, n₂ + 1, h => by
    dsimp [const] at h
    injection h with h₁ h₂
    simp only [const_inj h₂]

/-- A code for the identity function. -/
def id_code : codeo :=
  codeo.pair codeo.left codeo.right

/-- Given a code `c` taking a pair as input, returns a code using `n` as the first argument to `c`.
-/
def curry (c : codeo) (n : ℕ) : codeo :=
  codeo.comp c (codeo.pair (const n) id_code)

-- -- helper lemma to prove rfind' case of univ theorem, since rfind' is defined differently from rfind
-- lemma rfind' {f} (g : ℕ → ℕ) (hf : RecursiveIn g f) :
--     RecursiveIn g
--       (Nat.unpaired fun a m =>
--       (Nat.rfind fun n => (fun m => m = 0) <$> evalo g cf (Nat.pair a (n + m))).map (· + m)) := by
--       sorry

-- /-- A function is partial recursive relative to an oracle `g` if and only if there is a code implementing it.
-- Therefore, `evalo` is a **universal partial recursive function relative to `g`**. -/
-- theorem exists_code_rel {g : ℕ →. ℕ} {f : ℕ →. ℕ} : RecursiveIn g f ↔ ∃ c : codeo, evalo g c = f := by
--   constructor
--   · intro gf
--     induction gf
--     · exact ⟨codeo.zero, rfl⟩
--     · exact ⟨codeo.succ, rfl⟩
--     · exact ⟨codeo.left, rfl⟩
--     · exact ⟨codeo.right, rfl⟩
--     · exact ⟨codeo.oracle, rfl⟩
--     · sorry
--     · sorry
--     · sorry
--     · sorry
--   · rintro ⟨c, rfl⟩
--     induction c with
--     | zero =>
--       exact RecursiveIn.zero
--     | succ =>
--       exact RecursiveIn.succ
--     | left =>
--       exact RecursiveIn.left
--     | right =>
--       exact RecursiveIn.right
--     | oracle =>
--       exact RecursiveIn.oracle
--     | pair cf cg pf pg =>
--       exact pf.pair pg
--     | comp cf cg pf pg =>
--       apply RecursiveIn.comp
--       exact pg
--       exact pf
--     | prec cf cg pf pg =>
--       apply RecursiveIn.prec
--       exact pf
--       exact pg
--     | rfind' cf pf => sorry

def φ (g : ℕ →. ℕ) (e : ℕ) : ℕ →. ℕ :=
  evalo g (decode' e)
