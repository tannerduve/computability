# Oracle Computability and Turing Degrees in Lean

This project formalizes **oracle-relative computability** and the **theory of Turing degrees** in Lean. We define a model of relative computability via partial recursive functions, building a framework for expressing and proving properties of Turing reducibility, Turing equivalence, jump operators, and recursively enumerable sets.

## Project Structure

The project contains two parallel approaches to oracle computability:

- **`Computability/`**: Oracle computability with sets of oracles (`Set (ℕ →. ℕ)`)
- **`Computability/SingleOracle/`**: Oracle computability with single oracles (`ℕ →. ℕ`)

## Key Modules

### `Oracle.lean`

Defines our model of relative computability:

- `RecursiveIn O f`: the function `f` is computable relative to oracles in the set `O`.
- Generalizations: `RecursiveIn'`, `RecursiveIn₂`, `ComputableIn`, `ComputableIn₂` for functions between `Primcodable` types.
- Basic lemmas showing that partial recursive functions are recursive in any oracle.
- Universal oracle machine `evalo` and related functions.

### `Encoding.lean`

Provides Gödel numbering for partial recursive functions:

- Defines `codeo` type for representing oracle programs
- Implements `encodeCodeo`, `decodeCodeo` for universal simulation
- Defines `evalo` function for evaluating encoded programs with oracles

### `TuringDegree.lean`

Builds basic Turing reducibility and degree structure:

- `f ≤ᵀ g`: `f` is Turing reducible to `g`
- `f ≡ᵀ g`: Turing equivalence  
- `TuringDegree`: equivalence classes of `ℕ →. ℕ` under `≡ᵀ`
- Partial order instance for `TuringDegree`
- Join operations (`turingJoin`, `f ⊕ g`) for combining degrees

### `Jump.lean`

Defines the jump operator and related concepts:

- `jump f` (`f⌜`): the jump of function `f`
- `jumpSet A`: Halting problem relative to a decidable set `A`
- Various definitions of recursively enumerable sets
- Core jump theorems including non-reducibility and characterizations

### `AutGrp.lean`

Basic structure for the automorphism group of Turing degrees:

- `TuringDegree.automorphismGroup := OrderAut TuringDegree`
- Group structure via `OrderIso`
- Countability properties

### `ArithHierarchy.lean`

Defines the classical arithmetical hierarchy:

- `arithJumpBase n`: the `n`-fold jump of the empty oracle
- `arithJumpSet n`: the set `∅⁽ⁿ⁾`
- `decidableIn O A`: `A` is decidable relative to oracle set `O`
- `Sigma0 n A`, `Pi0 n A`, `Delta0 n A`: hierarchy levels
- Notations `Σ⁰_`, `Π⁰_`, `Δ⁰_`
- Defines `K := arithJumpSet 1` as the halting set

## References

1. Mario Carneiro. [*Formalizing Computability Theory via Partial Recursive Functions*](https://arxiv.org/pdf/1810.08380), arXiv:1810.08380, 2018.  
2. Piergiorgio Odifreddi. *Classical Recursion Theory*, Vol. I. [PDF](http://www.piergiorgioodifreddi.it/wp-content/uploads/2010/10/CRT1.pdf)
