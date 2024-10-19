import Computability.TuringDegrees
import Mathlib.Data.Option.Basic
import Mathlib.Tactic.Linarith
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

def evalo (g : ℕ →. ℕ) : codeo → ℕ →. ℕ :=
λ c => match c with
| codeo.zero => pure 0
| codeo.succ => Nat.succ
| codeo.left => λ n => (Nat.unpair n).1
| codeo.right => λ n => (Nat.unpair n).2
| codeo.oracle => g
| codeo.pair cf cg => λ n => (Nat.pair <$> evalo g cf n <*> evalo g cg n)
| codeo.comp cf cg => λ n => (evalo g cg n >>= evalo g cf)
| codeo.prec cf cg =>
   Nat.unpaired fun a n =>
    n.rec (evalo g cf a) fun y IH => do
      let i ← IH
      evalo g cg (Nat.pair a (Nat.pair y i))
| codeo.rfind' cf =>
    Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun m => m = 0) <$> evalo g cf (Nat.pair a (n + m))).map (· + m)

def mkpair (a b : ℕ) : ℕ := if a < b then b*b + a else a*a + a + b

def encode' : codeo → ℕ :=
λ c => match c with
| codeo.zero => 0
| codeo.succ => 1
| codeo.left => 2
| codeo.right => 3
| codeo.oracle => 4
| codeo.pair cf cg => 5 * (mkpair (encode' cf) (encode' cg)) + 5
| codeo.comp cf cg => 5 * (mkpair (encode' cf) (encode' cg)) + 6
| codeo.prec cf cg => 5 * (mkpair (encode' cf) (encode' cg)) + 7
| codeo.rfind' cf => 5 * (encode' cf) + 8

def unmkpair (n : ℕ) : ℕ × ℕ :=
  let s := Nat.sqrt n
  if n < s * s + s then
    let b := s
    let a := n - s * s
    (a, b)
  else
    let a := s
    let b := n - s * s - s
    (a, b)

def decode' : ℕ → Option codeo
  | 0 => some codeo.zero
  | 1 => some codeo.succ
  | 2 => some codeo.left
  | 3 => some codeo.right
  | 4 => some codeo.oracle
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
    | false, false =>
      match decode' m.unpair.1, decode' m.unpair.2 with
      | some cf, some cg => some (codeo.pair cf cg)
      | _, _ => none
    | false, true  =>
      match decode' m.unpair.1, decode' m.unpair.2 with
      | some cf, some cg => some (codeo.comp cf cg)
      | _, _ => none
    | true , false =>
      match decode' m.unpair.1, decode' m.unpair.2 with
      | some cf, some cg => some (codeo.prec cf cg)
      | _, _ => none
    | true , true  =>
      match decode' m with
      | some cf => some (codeo.rfind' cf)
      | none => none

instance : Primcodable codeo where
  encode := encode'
  decode := decode'
  encodek := by
    intros c
    induction' c
    case zero =>
      simp [encode', decode']
    case succ =>
      simp [encode', decode']
    case left =>
      simp [encode', decode']
    case right =>
      simp [encode', decode']
    case oracle =>
      simp [encode', decode']
    case pair cf cg ih1 ih2 =>
      sorry
  prim := sorry
