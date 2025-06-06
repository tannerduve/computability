import Computability.Oracle
import Std.Data.HashMap.Basic
/-
# Reduction DSL for Oracle-Relative Computability

This file defines a small monadic DSL for expressing
computable reductions relative to a fixed oracle `g : ℕ →. ℕ`, along with an
evaluator and a compileAuxr that produces `RecursiveIn {g}` proofs. This is to allow users
to write reductions in a higher-level and more intuitive way than formal `RecursiveIn` inductive derivations.

## Main Components

* `RedExpr`: A syntax tree for reduction expressions, including:
  - basic constructors like `zero`, `succ`, `pair`, `comp`, `prec`, `rfind`
  - an `oracle` node for accessing the oracle
  - `var` nodes for referencing previously defined subexpressions

* `RedM`: A state monad for writing reductions using `do` notation. It
  provides:
  - automatic fresh variable management
  - `emit` for binding intermediate expressions to fresh variables

* `RedState`: Tracks the environment of bound expressions and fresh variable IDs.

* `RedExpr.eval`: A big-step inductive semantics for interpreting expressions as
  partial functions `ℕ →. ℕ`, relative to an environment and a fixed oracle.

* `RedExpr.compile`: A compile that walks a `RedExpr` and returns:
  - the partial function `f : ℕ →. ℕ` it computes
  - a proof that `f` is `RecursiveIn {g}`

## Notes

* The DSL guarantees well-scoped expressions: all `var i` nodes refer to bound
  expressions created via `emit`. This ensures `eval` never fails due to
  unbound variables when evaluating terms built via `RedM`.

* The compileAuxr mirrors the `RecursiveIn` structure closely, mapping each
  `RedExpr` constructor to the corresponding `RecursiveIn` rule.

* This framework allows writing intuitive, algorithm-style reductions and
  mechanically extracting both the resulting function and its `RecursiveIn` proof.
-/

/-
Syntax tree for reduction expressions.
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


/-
State monad for writing reductions.
It tracks the next available variable ID and a mapping of IDs to bound expressions.
-/
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

/-
Interpreter/operational semantics for reduction expressions.
-/
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

/-
A compiled reduction expression is a pair of:
1. A partial function `f : ℕ →. ℕ`
2. A proof that `f` is `RecursiveIn {g}`
-/
abbrev Compiled (g : ℕ →. ℕ) :=
  { f : ℕ →. ℕ // RecursiveIn {g} f }

/--
Compiler from `RedExpr` to `Compiled g`, producing both the partial function and its `RecursiveIn` proof.
-/
def RedExpr.compileAux (env : Env) (g : ℕ →. ℕ) : RedExpr → Option (Compiled g)
  | var i =>
    match env i with   -- well‑scoped ⇒ always some
    | some e => compileAux env g e
    | none   => none  -- unreachable for DSL terms
  | zero =>
    some ⟨fun _ => 0, RecursiveIn.zero⟩
  | succ e => do
    let ⟨f, hf⟩ ← compileAux env g e
    let f' : ℕ →. ℕ :=        --  n ↦ f n ▷ succ
      fun n => f n >>= fun x => Part.some (Nat.succ x)
    return ⟨f', RecursiveIn.comp RecursiveIn.succ hf⟩
  | oracle => some ⟨g, RecursiveIn.oracle g (by simp)⟩
  | pair cf cg => do
    let ⟨f, hf⟩ ← compileAux env g cf
    let ⟨g', hg'⟩ ← compileAux env g cg
    let f' : ℕ →. ℕ :=        -- n ↦ (f n ▷ pair) ▷ (g' n ▷ pair)
      fun n => (Nat.pair <$> f n <*> g' n)
    return ⟨f', RecursiveIn.pair hf hg'⟩
  | comp cf cg => do
    let ⟨f, hf⟩ ← compileAux env g cf
    let ⟨g', hg'⟩ ← compileAux env g cg
    let f' : ℕ →. ℕ :=        -- n ↦ (g' n ▷ f)
      fun n => g' n >>= f
    return ⟨f', RecursiveIn.comp hf hg'⟩
  | prec cf cg => do
    let ⟨f, hf⟩ ← compileAux env g cf
    let ⟨g', hg'⟩ ← compileAux env g cg
    let f' : ℕ →. ℕ :=        -- n ↦ (g' n ▷ f) ▷ (f a ▷ prec)
      fun p =>
        let (a, n) := Nat.unpair p
        n.rec (f a) fun y IH =>
          IH >>= fun i =>
            g' (Nat.pair a (Nat.pair y i))
    return ⟨f', RecursiveIn.prec hf hg'⟩
  | rfind cf => do
    let ⟨f, hf⟩ ← compileAux env g cf
    let f' : ℕ →. ℕ :=        -- n ↦ (f n ▷ rfind) ▷ (Nat.rfind ▷ f)
      fun a =>
        Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a n)
    return ⟨f', RecursiveIn.rfind hf⟩
partial_fixpoint

/-
A relational compiler
-/
inductive RedExpr.Compiles
    (env : Env) (g : ℕ →. ℕ) :
    RedExpr → Compiled g → Prop
| var_some {i e c} :
    env i = some e →
    Compiles env g e c →
    Compiles env g (.var i) c
| var_none {i} :
    env i = none →
    Compiles env g (.var i)
      ⟨(λ _ => Part.none), RecursiveIn.none (O := {g})⟩
| zero :
    Compiles env g .zero
      ⟨(λ _ => Part.some 0), RecursiveIn.zero⟩
| succ {e f hf} :
    Compiles env g e ⟨f, hf⟩ →
    Compiles env g (.succ e)
      ⟨(λ n => f n >>= fun x => Part.some (Nat.succ x)),
        RecursiveIn.comp RecursiveIn.succ hf⟩
| oracle :
    Compiles env g .oracle
      ⟨g, RecursiveIn.oracle g (by simp)⟩
| pair {e₁ e₂ f₁ h₁ f₂ h₂} :
    Compiles env g e₁ ⟨f₁, h₁⟩ →
    Compiles env g e₂ ⟨f₂, h₂⟩ →
    Compiles env g (.pair e₁ e₂)
      ⟨(λ n => Nat.pair <$> f₁ n <*> f₂ n),
        RecursiveIn.pair h₁ h₂⟩
| comp {e₁ e₂ f₁ h₁ f₂ h₂} :
    Compiles env g e₁ ⟨f₁, h₁⟩ →
    Compiles env g e₂ ⟨f₂, h₂⟩ →
    Compiles env g (.comp e₁ e₂)
      ⟨(λ n => f₂ n >>= f₁),
        RecursiveIn.comp h₁ h₂⟩
| prec {e₁ e₂ f₁ h₁ f₂ h₂} :
    Compiles env g e₁ ⟨f₁, h₁⟩ →
    Compiles env g e₂ ⟨f₂, h₂⟩ →
    Compiles env g (.prec e₁ e₂)
      ⟨λ p =>
          let (a,n) := Nat.unpair p
          n.rec (f₁ a) (λ y IH => IH >>= λ i => f₂ (Nat.pair a (Nat.pair y i))),
        RecursiveIn.prec h₁ h₂⟩
| rfind {e f hf} :
    Compiles env g e ⟨f, hf⟩ →
    Compiles env g (.rfind e)
      ⟨(λ a =>
          Nat.rfind (λ n => (λ m => m = 0) <$> f (Nat.pair a n))),
        RecursiveIn.rfind hf⟩

def freeVars (e : RedExpr) : Set ℕ :=
  match e with
  | .var i => {i}
  | .zero => ∅
  | .succ e => freeVars e
  | .oracle => ∅
  | .pair e₁ e₂ => freeVars e₁ ∪ freeVars e₂
  | .comp e₁ e₂ => freeVars e₁ ∪ freeVars e₂
  | .prec e₁ e₂ => freeVars e₁ ∪ freeVars e₂
  | .rfind e => freeVars e

def wellScoped (e : RedExpr) (env : Env) : Prop :=
  ∀ i, i ∈ freeVars e → (∃ v, env i = some v)

lemma compileAux_sound
    (env : Env) (g : ℕ →. ℕ) :
  ∀ {e : RedExpr} {c : Compiled g},
    (hscoped : wellScoped e env) →
    RedExpr.compileAux env g e = some c →
    RedExpr.Compiles env g e c := by
    intro e c scope hec
    simp [wellScoped] at scope
    induction e generalizing c
    · case var i =>
      simp [RedExpr.compileAux] at hec
      simp [freeVars] at scope
      cases' scope with v hv
      simp [hv] at hec
      apply RedExpr.Compiles.var_some
      apply hv
      sorry
    all_goals sorry


lemma compileAux_complete
    {env : Env} {g : ℕ →. ℕ} {e : RedExpr} {c : Compiled g}
    (hs : RedExpr.Compiles env g e c) :
  RedExpr.compileAux env g e = some c := by
  induction hs
  · case var_some i e' c' ha hb ih =>
    sorry
  all_goals sorry
