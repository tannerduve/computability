# Oracle Computability and Turing Degrees in Lean

This project formalizes **oracle-relative computability** and the **theory of Turing degrees** in Lean. We define a model of relative computability via partial recursive functions, and build a framework for expressing and proving properties of Turing reducibility, Turing equivalence, jump operators, and recursively enumerable sets.

## Key Modules

### `Oracle.lean`

Defines our model of relative computability:

- `RecursiveIn O f`: the function `f` is computable relative to oracles in the set `O`.
- Generalizations: `RecursiveIn'`, `RecursiveIn₂`, `ComputableIn`, `ComputableIn₂` for functions between `Primcodable` types.
- Lifting functions using `Primcodable` encoding.
- Universal oracle machine `evalo` and its correctness.

### `Encoding.lean`

- Gödels numbering for partial recursive functions with oracle sets indexed by a `Primcodable` type.
- Implements `encodeCodeo`, `decodeCodeo` for universal simulation.
- Proves: `RecursiveIn (range g) f ↔ ∃ c, evalo g c = f`.

### `TuringDegree.lean`

Builds Turing reducibility and degree structure:

- `f ≤ᵀ g`: `f` is Turing reducible to `g`.
- `f ≡ᵀ g`: Turing equivalence.
- `TuringDegree`: equivalence classes of `ℕ →. ℕ` under `≡ᵀ`.
- Defines `turingJoin` (`f ⊕ g`) as the least upper bound.
- Join lemmas:
  - `left_le_join`: `f ≤ᵀ f ⊕ g`
  - `right_le_join`: `g ≤ᵀ f ⊕ g`
  - `join_le`: `f ⊕ g ≤ᵀ h` if `f ≤ᵀ h` and `g ≤ᵀ h`
- Partial order instance for `TuringDegree`.

### `Jump.lean`

Defines the jump operator:

- `f⌜ := λ n => evalo (λ _ => f) (decodeCodeo n) n`
- `jumpSet A`: Halting problem relative to a decidable set `A`.
- Theorems (in progress):
  1. `f ≤ᵀ f⌜`
  2. `¬(f⌜ ≤ᵀ f)`
  3. `A ∈ re(f) ↔ A ≤₁ f⌜`
  4. If `A ∈ re(f)` and `f ≤ᵀ h` then `A ∈ re(h)`
  5. `g ≤ᵀ f ↔ g⌜ ≤ᵀ f⌜`
  6. `g ≡ᵀ f ↔ g⌜ ≡ᵀ f⌜`

### `AutGrp.lean`

Defines the automorphism group of the Turing degrees:

- `TuringDegree.automorphismGroup := OrderAut TuringDegree`
- Group structure via `OrderIso`.
- `Countable` instance is stated (`sorry`).

### `ReductionDSL.lean`

Monadic DSL for writing reductions that compile into `RecursiveIn` proofs:

- `RedExpr`: Syntax tree for reduction expressions.
- `RedM`: Monadic builder for well-scoped reduction programs.
- `RedExpr.eval`: Big-step semantics for `RedExpr`.
- `RedExpr.compileAux`: Functional compiler producing `(f : ℕ →. ℕ) × RecursiveIn {g} f`.
- `RedExpr.Compiles`: Relational compiler specification.
- Correctness:
  - `compileAux_sound`: functional compiler satisfies the relational spec.
  - `compileAux_complete`: completeness for well-scoped expressions.

---

## In Progress

- Prove the jump theorems (see `Jump.lean`).
- Complete `compileAux_sound` and `compileAux_complete` proofs.
- Prove `encodeCodeo ∘ decodeCodeo = id`.
- Show that the Turing degrees form an upper semilattice.

---

## Project Directions

- Prove countability of `TuringDegree.automorphismGroup`.
- Explore structure theore of the automorphism group
- Formalize a finite injury priority argument (e.g. Kleene–Post theorem).

---

## References

1. Mario Carneiro. [*Formalizing Computability Theory via Partial Recursive Functions*](https://arxiv.org/pdf/1810.08380), arXiv:1810.08380, 2018.  
2. Piergiorgio Odifreddi. *Classical Recursion Theory*, Vol. I. [PDF](http://www.piergiorgioodifreddi.it/wp-content/uploads/2010/10/CRT1.pdf)
