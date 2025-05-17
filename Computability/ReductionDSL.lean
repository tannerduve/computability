import Computability.Oracle
import Std.Data.HashMap.Basic
/-
Would be great to write a DSL for writing reductions that compiles into `RecursiveIn` proofs.
Can brainstorm/start implementing it here.
-/

inductive RedExpr
| var   : ℕ → RedExpr
| zero  : RedExpr
| succ  : RedExpr → RedExpr
| oracle : RedExpr
| pair  : RedExpr → RedExpr → RedExpr
| comp  : RedExpr → RedExpr → RedExpr
| prec  : RedExpr → RedExpr → RedExpr
| rfind : RedExpr → RedExpr

structure RedState where
  nextId   : ℕ
  bindings : Std.HashMap ℕ RedExpr

def Env := ℕ → Option RedExpr

def RedState.toEnv (s : RedState) : Env := λ i => s.bindings.get? i

def RedState.insert (s : RedState) (i : ℕ) (e : RedExpr) : RedState :=
  { s with bindings := s.bindings.insert i e }

def RedState.erase (s : RedState) (i : ℕ) : RedState :=
  { s with bindings := s.bindings.erase i}

abbrev RedM (α : Type) := StateM RedState α

instance : Monad RedM where
  pure a := fun s => (a, s)
  bind x f := fun s => do
    let (a, s') ← x s
    f a s'
  map f x := fun s => do
    let (a, s') ← x s
    pure (f a, s')

def RedM.get : RedM RedState := fun s => (s, s)

def RedM.set (s : RedState) : RedM PUnit := fun _ => (.unit, s)

def RedM.run (x : RedM α) (s : RedState) : α × RedState :=
  x s

def RedM.modify (f : RedState → RedState) : RedM PUnit := do
  let s ← get
  set (f s)
  pure PUnit.unit

def RedM.fresh : RedM ℕ := do
  let s ← get
  set { s with nextId := s.nextId + 1 }
  pure s.nextId

def RedM.emit (e : RedExpr) : RedM ℕ := do
  let id ← fresh
  modify (λ s => .insert s id e)
  pure id

def add1_oracle : RedM ℕ := do
  let x ← .emit .oracle
  let y ← .emit (.succ (.var x))
  .emit (.pair (.var x) (.var y))

inductive RedExpr.eval : Env → (ℕ →. ℕ) → RedExpr → (ℕ →. ℕ) → Prop
| var {env g i e f} :
    env i = some e →
    RedExpr.eval env g e f →
    RedExpr.eval env g (.var i) f
| var_none {env g i} :
    env i = none →
    RedExpr.eval env g (.var i) (λ _ => Part.none)
| zero {env g} :
    RedExpr.eval env g .zero (λ _ => some 0)
| succ {env g e f} :
    RedExpr.eval env g e f →
    RedExpr.eval env g (.succ e) (λ n => (f n).map (· + 1))
| oracle {env g} : RedExpr.eval env g .oracle g
| pair {env g cf cg f g'} :
    RedExpr.eval env g cf f →
    RedExpr.eval env g cg g' →
    RedExpr.eval env g (.pair cf cg)
      (λ n => Nat.pair <$> f n <*> g' n)
| comp {env g cf cg f g'} :
    RedExpr.eval env g cg g' →
    RedExpr.eval env g cf f →
    RedExpr.eval env g (.comp cf cg)
      (λ n => g' n >>= f)
| prec {env g cf cg f g'} :
    RedExpr.eval env g cf f →
    RedExpr.eval env g cg g' →
    RedExpr.eval env g (.prec cf cg)
      (Nat.unpaired fun a n =>
        n.rec (f a) fun y IH =>
          IH >>= fun i =>
            g' (Nat.pair a (Nat.pair y i)))
| rfind {env g cf f} :
    RedExpr.eval env g cf f →
    RedExpr.eval env g (.rfind cf)
      (Nat.unpaired fun a m =>
        (Nat.rfind fun x =>
          (fun y => y = 0) <$> f (Nat.pair a (x + m))
        ).map (· + m))

abbrev Compiled (g : ℕ →. ℕ) :=
  { f : ℕ →. ℕ // RecursiveIn {g} f }

def RedExpr.compile (env : Env) (g : ℕ →. ℕ) :
    RedExpr → Compiled g := by sorry
