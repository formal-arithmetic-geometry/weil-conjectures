## Worker report

The module `Sheaf.LinearAlgebra.RationalLinearSystemParametrization` states
`Matrix.exists_rat_affine_parametrization_of_real_solution`. Its sole theorem has
proof `sorry`; it defines no additional notion. The node is unchanged except for
its `lean` record. No dependency repairs, new nodes, or statement correction are needed.

Hypothesis and clause correspondence:

- The fixed fields ℚ and ℝ are Mathlib's rational and real fields. Each
  `(q : ℝ)` is the usual rational inclusion, not an arbitrary ring map.
- `m,d ≥ 0` is `{m d : ℕ}`. The rational matrix is
  `A : Matrix (Fin m) (Fin d) ℚ`; the rational right side is `b : Fin m → ℚ`.
- The entrywise images are `A.map (fun q : ℚ ↦ (q : ℝ))` and
  `fun i ↦ (b i : ℝ)`. Mathlib `Matrix.map` applies exactly this map to every entry.
- Real solvability is the hypothesis `h : ∃ x : Fin d → ℝ, ... .mulVec x = ...`.
  Mathlib `Matrix.mulVec` is the row dot product, hence the finite sum of
  `A i a * x a` required by the node. No square-matrix assumption is imposed.
- `∃ (k : ℕ) (x₀ : Fin d → ℚ) (v : Fin k → Fin d → ℚ)` supplies the nonnegative
  number of directions, rational particular vector, and rational direction vectors.
  Indexing `v₁,...,vₖ` by `Fin k` only shifts the labels from one-based to zero-based.
- `A.mulVec x₀ = b` is the required rational particular-solution equation.
- `∀ j : Fin k, A.mulVec (v j) = 0` is every rational homogeneous equation;
  the zero is the zero vector in `Fin m → ℚ`.
- `∀ x : Fin d → ℝ, ... .mulVec x = ... → ∃ t : Fin k → ℝ, ...` quantifies
  over every real solution and supplies its real coefficients. The final equation
  `x = (fun a ↦ (x₀ a : ℝ)) + ∑ j : Fin k, t j • (fun a ↦ (v j a : ℝ))`
  is exactly the affine parametrization, with the ordinary pointwise vector
  addition and real scalar multiplication. It requires neither independence nor
  uniqueness of parameters, neither of which the node states.

Dependency declarations read and used: `def-weil-field` is a Mathlib leaf with
`mathlib_match = ["Field"]`, not a missing Lean record. The full class signature
and docstring in `Mathlib.Algebra.Field.Defs` were read: `Field (K : Type u)`
extends `CommRing K, DivisionRing K`, giving precisely the node's field notion.
The fields for ℚ and ℝ are inferred, rather than introducing redundant field
hypotheses on these fixed types. Imports `Mathlib.Data.Real.Basic` and
`Mathlib.Data.Matrix.Mul` provide these fields and the matrix/vector operations
(and transitively `Field`). `Matrix.map` and `Matrix.mulVec` signatures and
docstrings were read in `Mathlib.LinearAlgebra.Matrix.Defs` and
`Mathlib.Data.Matrix.Mul`, respectively. There are no proof-dependency nodes.

The theorem docstring records all five agent-origin proof steps: simultaneous
induction over the column count, the zero cases, explicit row and column
permutations, the rational pivot, the coefficients of the reduced system,
the lifted particular solution and directions, and the finite-sum expansion
for every real solution. Milne II §1 Lemma 1.3 is explicitly identified as
context only, as in the node and its stage-1 report; it is not claimed to prove
this linear algebra assertion.

Edge cases checked mathematically before writing:

- `d = 0`: the coordinate space has the unique empty vector; consistency forces
  every coordinate of b to vanish. Take `k = 0` and the empty particular vector.
- `m = 0`: there are no equations and the real solvability hypothesis is true;
  take `x₀ = 0` and the `d` coordinate directions. All real vectors are covered.
- `m = d = 0`: both checks coincide, and `k = 0` works.
- `A = 0`: real consistency forces `b = 0`; coordinate directions work. A
  nonzero right side with a zero row is excluded by `h`, not by an added assumption.
- `k = 0`: the direction equation is vacuous and the sum is zero, allowing a
  unique solution. For `A = (1), b = (2)` take `x₀ = (2)` and `k = 0`.
- A dependent-row example `A = ((1,1),(2,2)), b = (1,2)` admits particular
  vector `(1,0)` and direction `(-1,1)`, giving `(1-t,t)` for all real solutions.
  Thus no full-rank or parameter-independence hypothesis was smuggled in.

Searches actually run through the authorized wrapper:

- LeanFinder, query "A real-solvable rational linear system has a rational
  particular solution and rational kernel vectors spanning every real solution":
  eight hits, including simplex `extractSolution` and `findPositiveVector`,
  `Nat.isSemilinearSet_setOf_mulVec_eq`, number-field rational lattice-span,
  and Diophantine projection results. None is this theorem: simplex entries
  are computational/metaprogramming interfaces, semilinearity is over ℕ,
  and the other statements concern different spaces.
- Loogle, `Matrix.mulVec, Rat.cast`: two number-field embedding/basis-matrix
  identities, neither asserting consistency descent or all-solution parametrization.
- LeanSearch, query "A rational matrix equation with a real solution has rational
  affine directions that parametrize every real solution": eight hits, including
  `Matrix.map_mul_ratCast`, integer numerator/denominator facts, affine-direction
  facts, affine-basis spanning, and natural-number semilinearity. None states
  this rational inhomogeneous system result.
- Mathlib grep through `msearch.py`, query
  `ker.*baseChange|baseChange.*ker|rational_solution|rowReduce` in `LinearAlgebra`:
  three lines in `TensorProduct/Tower.lean`. I opened the full signature and
  proof of `ker_baseChange_comp_cancelBaseChange_symm`; it cancels repeated
  base change for an already extended domain and is not the desired theorem.
- Direct `rg` searches in both `lean/WeilConjectures` and `lean/Sheaf` for
  rational solutions/parametrizations, rational matrix-vector casts, and
  scalar-extension kernels found no exact declaration. The exact item-id
  `grep -rn` search in `lean/WeilConjectures` found none. A further exact-name
  and rational-parametrization search across Mathlib and both project trees
  found only the unrelated rational parametrization of the Pythagorean circle.

No statement dispute or node fault was found. Server compilation via
`scompile.py Q07 lem-sfb-rational-linear-system-parametrization <module>`
succeeded for both its sandbox and library module names. `autoImplicit false`
checks that all variables are bound explicitly; there are no universe parameters
because all coordinate types use the fixed fields ℚ and ℝ and finite indices.

## Second reading by Q07

This is the dispatcher's single worker's separate second pass over the finished
node and module; the maintainer supplies the independent review. No other agent
was started.

I reread the unchanged node statement beside the full theorem signature.
The two sizes are arbitrary natural numbers, the matrix is rectangular and
rational, the right side is rational, and the sole substantive assumption is
real consistency using the fixed usual inclusion. The existential witnesses
are one rational vector and a finite rational family; the first two conjuncts
are precisely the rational equations, and the last conjunct quantifies over
all real solutions, then real parameters, with the stated affine sum. The
sum and its scalar action live in `Fin d → ℝ`; no rational restriction is placed
on the parameters. No nonempty coordinate type, positive size, rank condition,
basis, or uniqueness is required. In particular, `Fin 0` supports every empty
case the node explicitly allows. The field dependency is the existing Mathlib
class, and no parallel definition or auxiliary statement was introduced.

I also reread the five proof paragraphs against the node's proof: the reduced
system coefficients, lifted homogeneous first coordinates, and the restoration
of column order are all present. All imports are used by the statement and
no proof-dependency import is omitted (the node has none). The signature in
`lean.statement` is extracted verbatim from `theorem` to before `:=`, all Lean
lines fit the 100-character limit, and the JSON differs from the base only in
`lean`. No mismatch was found and no statement change was made.
