## Worker report

The module `Sheaf.RingTheory.AffinoidQuotientNormTopology` states
`RestrictedSeries.affinoid_quotient_norm_topology`, with its single proof `sorry`.
There are no new definitions, helper axioms, dependency repairs, or statement changes.
The theorem docstring contains all seven steps of the accepted node proof.

Hypothesis and clause correspondence:

- The complete field with nontrivial real-valued nonarchimedean absolute value is
  `(K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]`.
  `NormedField` includes `Field`, the Mathlib match for `def-weil-field`.
  Nontriviality means that some scalar has norm greater than one; this is equivalent
  to a nonzero scalar having norm different from one, by taking its inverse if needed.
- The number of variables is arbitrary `r : ℕ`, including zero. The source ring is
  exactly `MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))`.
  This is the recorded dependency's source ring, with the same ring operations.
  `MvPowerSeries.IsRestricted` is coefficient decay in the cofinite filter. At
  polyradius one `MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin r ↦ 1)` is
  the supremum of coefficient norms, since every radius factor equals one.
- The nonzero commutative unital Banach algebra is `(C : Type v)` with
  `[NormedCommRing C] [Nontrivial C] [NormedAlgebra K C] [IsUltrametricDist C]
  `[CompleteSpace C]`. The universes `u` and `v` are independent.
  `NormedCommRing` supplies norm definiteness, triangle and submultiplicative bounds
  and the metric from differences. `NormedAlgebra` bundles the scalar action with
  its algebra map and norm compatibility: over a field its defining inequality
  implies the exact identity `norm_smul`, namely `‖a • c‖ = ‖a‖ * ‖c‖`.
  It does not impose `‖1‖ = 1` on the given norm of C.
- The scalar-compatible unital ring homomorphism is `q` with
  `hscalar : q.comp (constants K r) = algebraMap K C`. A ring homomorphism
  compatible with constants is exactly a K-algebra homomorphism on this ring.
  This uses the dependency's actual `RestrictedSeries.constants`, not a copy.
  `hsurj : Function.Surjective q` is surjectivity.
- `hcont` is continuity at every source point: each positive target radius ε
  has a positive source radius δ controlling `‖q t - q s‖` by the Gauss norm
  of `t.val - s.val`. This is precisely epsilon-delta continuity for the Gauss
  metric; using the ambient coefficientwise formal-series topology would be wrong.
- The conclusion's `∃ N : AlgebraNorm K C` states all algebra norm axioms on the
  original algebra C, including zero, definiteness, negation, submultiplicativity,
  and exact scalar homogeneity. The first conjunct identifies this norm at every
  c with the specified `sInf` of all Gauss norms of lifts `s` satisfying `q s = c`.
  Thus the existential norm has uniquely specified underlying data. Surjectivity
  ensures each set of lift norms is nonempty, and zero is a lower bound.
- `N 1 = 1` records the normalization proved in step 5. It follows from the
  given nonzero quotient, source norm of one, and submultiplicativity; it is not
  assumed for the original Banach norm. The following conjunct
  `∀ c d, N (c + d) ≤ max (N c) (N d)` is the nonarchimedean inequality.
- `@CompleteSpace C N.toRingNorm.toNormedRing.toUniformSpace` asserts completeness
  for the norm just obtained. `RingNorm.toNormedRing` keeps the original ring
  operations, and its distance is the norm of the difference.
- The open-set equivalence uses explicitly the topology of this same norm N on
  the left, and Gauss balls at every `s` in `q⁻¹(U)` on the right. Its right-hand
  side is exactly that `q⁻¹(U)` is Gauss-open. Together with surjectivity it is
  exactly the quotient topology assertion, without using formal-series topology.
- The last conjunct gives `∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ c, ...` with the two
  required inequalities `N c ≤ A * ‖c‖` and `‖c‖ ≤ B * N c`. These positive
  bounds also imply equality of the norm topologies, as the node says.

Dependencies read and used:

- `def-weil-field`: Mathlib `Field` in `Mathlib.Algebra.Field.Defs`, inherited by
  the normed-field binder. Its full definition extends `CommRing` and `DivisionRing`.
- `def-trf-restricted-series-presentation`: read the full module
  `Sheaf.RingTheory.RestrictedSeriesPresentation`, especially
  `RestrictedSeries.constants` and `RestrictedSeries.IsAffinoidQuotient`.
  The theorem reuses its exact restricted subring, constants, and quotient norm
  expression; it does not assume the conclusion `IsAffinoidQuotient` as input.
- The stated proof leaves `lem-trf-continuous-linear-map-norm-bound` and
  `lem-trf-banach-surjective-bounded-lifts` match `ContinuousLinearMap.bound` in
  `Mathlib.Analysis.Normed.Operator.Basic` and
  `ContinuousLinearMap.exists_preimage_norm_le` in
  `Mathlib.Analysis.Normed.Operator.Banach`. Their source signatures and docstrings
  were read; the latter module is imported without `public` for the proof plan.
- `lem-trf-restricted-series-gauss-completion` has no Lean record or Mathlib match
  in the read DAG. Its whole statement and dependencies were read. It is a proof
  dependency only: this theorem can state its exact hypothesis via Gauss balls
  without assuming or duplicating a Banach instance on the source. Its proof
  import can be added by the maintainer once the dependency is stated.

Source checked: the primary Bosch PDF
https://www.uni-muenster.de/IVV5WS/WebHop/user/weckerm/heft378.pdf was opened,
including printed p. 23 (PDF p. 24), Proposition 4(i)--(ii), and printed p. 31
(PDF p. 32), Proposition 19 and its paragraph about the Banach open mapping
alternative. The former supplies the quotient norm/topology/completeness; the
latter explains the alternate analytic route. The node's seven-step proof gives
comparison to the arbitrary given Banach algebra norm using bounded lifts.
The latest blueprint locality statement was also read; this item is an analytic
input beneath that statement, not the unit's own statement.

Edge cases checked before writing: `r = 0` has coefficient index `Fin 0 →₀ ℕ`,
with its one empty multi-index, so the source is the constants K and nothing
requires positive r. Zero c has the zero lift and norm zero; positive bounds
remain meaningful. Zero scalars are included in `AlgebraNorm` homogeneity.
The zero target algebra is expressly excluded by the node, as rendered by
`Nontrivial C`. Arbitrary nonzero targets, nonreduced quotients, any characteristic,
and nondiscrete nontrivial absolute values are allowed. Nothing assumes finite
vector-space dimension or attainment of the infimum. Empty and whole open sets
satisfy the quotient criterion. Independent source and target universes exclude
no permitted algebra. No statement dispute was found.

Searches made with the prescribed msearch wrapper:

- LeanFinder: "The quotient Gauss norm of a Tate algebra under a continuous
  surjection to a Banach algebra is complete and equivalent to its original norm".
  Eight results, including `spectralNorm.normedSpace`, `spectralMulAlgNorm` and
  normed-field completions; none states this Tate quotient result.
- Loogle: `"AlgebraNorm", "toNormedRing"`: zero results. Local source reading
  located `AlgebraNorm` and `RingNorm.toNormedRing`, which are reused.
- Mathlib grep: `quotient.*[Gg]auss|[Gg]auss.*quotient|gaussNorm.*[Nn]orm`:
  nineteen hits, all coefficient Gauss norm definitions or inequalities, no full
  quotient statement.
- LeanSearch: "A continuous surjection from a Tate algebra onto a Banach algebra
  induces an equivalent complete quotient Gauss norm": eight results, including
  `ContinuousLinearMap.isQuotientMap` and `exists_preimage_norm_le`. These are the
  general Banach ingredients, not this complete statement with the specified norm.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for quotient/Gauss combinations
  and the proposed declaration name, and node-id search in `lean/WeilConjectures`:
  no existing exact statement. The Sheaf hits were the presentation definition,
  `AffinoidPolynomialClosedPointComparison` and `GrauertRemmertPowerbounded`.
  Their declarations were read: they treat different conclusions/hypotheses.
  The upstream-name index has no binding for this node.

Validation: the first server compile exposed overlapping Algebra/NormedSpace
scalar-action instances. Replaced those two parameters by the single exact
`NormedAlgebra K C` binder; this is the bundled compatible structure the node
requires, with no added restriction. Every theorem proof remains `sorry`.

The corrected module compiled cleanly through scompile.py in both sandbox and
library contexts, without errors or warnings. The prescribed deliver2.py dry run
then printed OK: preflight and per-file compilation passed. Only the module,
the item's lean record, and this report are delivered.

## Second reading by Q35

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
