## Worker report

The module `Sheaf.Analysis.Normed.Module.AdmissibleScalarBalls` states
`LinearMap.exists_admissible_scalar_of_isCompact_closedBall`, with its proof
exactly `by sorry`. It introduces no definitions or helper theorems. The copied
node changes only its `lean` record; its natural-language statement is unchanged.

Clause-by-clause correspondence:

- The field K is `{K : Type u} [NormedField K]`. The inherited `Field K` is
  precisely the Mathlib match of `def-weil-field`, read in
  `Mathlib.Algebra.Field.Defs` (the `Field` declaration and docstring).
- The nonnegative scalar absolute value is the norm of `NormedField K`.
  Mathlib's real norm is nonnegative, equivalently a nonnegative-real-valued
  norm; its zero iff zero, value at one, and multiplicativity are the normed
  field laws (`norm_eq_zero`, `norm_one`, `norm_mul`). The additional hypothesis
  `hK : ∀ a b : K, ‖a + b‖ ≤ max ‖a‖ ‖b‖` is exactly the scalar
  ultrametric inequality. No nontriviality of this norm is required.
- The vector space and its norm are `{V : Type v} [NormedAddCommGroup V]
  [NormedSpace K V]`. They give an additive commutative group, a K-module,
  nonnegativity and norm zero iff vector zero, and exact homogeneity
  `norm_smul`. The defining inequality in `NormedSpace` implies this equality
  over a field; its declaration's docstring explicitly states this.
  `hV : ∀ y z : V, ‖y + z‖ ≤ max ‖y‖ ‖z‖` is the vector ultrametric law.
- The normed structures use the metric induced by the norm. In particular
  `dist a b = ‖a - b‖`: the defining `‖-a + b‖` convention is equal to this
  by norm invariance under negation. These metric/topology structures do not
  add a mathematical assumption to the node: its separating ultrametric norms
  already induce precisely these metrics and topologies.
- `hcompact : ∀ (a : K) (r : ℝ), 0 ≤ r →
  IsCompact (Metric.closedBall a r)` is compactness of every specified
  closed scalar ball, including radius zero. `Metric.closedBall a r` is
  `{b | dist b a ≤ r}`, hence exactly `{b | ‖b-a‖ ≤ r}`.
  `isCompact_iff_finite_subcover` in
  `Mathlib.Topology.Compactness.Compact` identifies this with the open-cover
  definition used by the node. No compactness of V is assumed.
- `U : Submodule K V` is the arbitrary linear subspace. `g : U →ₗ[K] K`
  is exactly an additive, scalar-preserving map, by `LinearMap` in
  `Mathlib.Algebra.Module.LinearMap.Defs`. This is an algebraic linear map,
  with no separately required continuity structure.
- `hg : ∀ u : U, ‖g u‖ ≤ ‖(u : V)‖` is the contractive bound on every
  element of the subspace, using its inclusion into V explicitly.
- `(x : V) (hx : x ∉ U)` is the vector outside the subspace.
- The complete conclusion is `∃ b : K, ∀ u : U,
  ‖b - g u‖ ≤ ‖x - (u : V)‖`, the asserted simultaneous scalar constraints.
  There is no closure, dimension, completeness, or characteristic restriction.

Dependencies and imports:

- Statement dependency `def-weil-field` uses its recorded Mathlib match `Field`,
  `Mathlib.Algebra.Field.Defs`, exposed through the public import
  `Mathlib.Analysis.Normed.Module.Basic`. No project-specific field is redefined.
- The latter import supplies `NormedField`, `NormedAddCommGroup`, `NormedSpace`,
  `Submodule`, and `LinearMap`; their definitions and relevant docstrings were read.
- The public import `Mathlib.Topology.Compactness.Compact` supplies `IsCompact`
  used in the statement and the recorded proof-dependency match
  `CompactSpace.iInter_nonempty` of
  `lem-sfb-compact-closed-finite-intersection`. Its full signature was read:
  arbitrary index universe, closed sets, and every finite intersection nonempty.
  It needs no additional import because this module is already a statement import.
- The theorem docstring reproduces all five DAG proof steps, including the empty
  finite intersection, relative closedness, and compactness of the initial ball.

Edge cases checked before writing:

- Radius zero is retained by `0 ≤ r`, not excluded by strict positivity.
  Each zero-radius ball is a singleton, which is compact.
- Trivially valued fields are allowed by `NormedField`; no
  `NontriviallyNormedField` or scalar of norm between zero and one is assumed.
  For finite fields with the discrete norm every scalar ball is compact.
- U can be the zero subspace: g is zero and b = 0 satisfies the required
  single constraint. If U is all V, or V is the zero space, there is no x
  satisfying `hx`, exactly as in the node.
- U is nonempty because it contains zero. The empty *finite family* in the
  proof has a witness in B_0; the docstring retains this separate case.
- Arbitrarily small positive radii and infinite-dimensional or nonclosed U
  are allowed. No positive lower bound on the radii is inserted.
- K and V have independent explicit universes u and v. A family indexed by
  `U : Type v` is admissible in `CompactSpace.iInter_nonempty` even when the
  scalar carrier is in a different universe.
- There is no `CompleteSpace V` hypothesis; nor is one added for K. Any
  completeness consequences of compact scalar balls are consequences only.

Searches for an existing declaration (all run for this item):

- `msearch.py`, LeanFinder: “A contractive linear functional over an ultrametric
  field with compact closed balls has a common admissible value b with norm
  (b - g u) at most norm (x - u) for all u in a subspace”. Eight results,
  including `riesz_lemma`, `exists_dual_vector''`, and
  `NormedAlgebra.exists_isMinOn_norm_sub_smul`. None is this assertion;
  Riesz results require a closed subspace and the dual-vector results use RCLike.
- `msearch.py`, Loogle: `"IsUltrametricDist", "closedBall"`. Eight results,
  including `IsUltrametricDist.closedBall_subset_trichotomy` and
  `IsUltrametricDist.closedBall_eq_or_disjoint`. They concern scalar ball
  containments and do not assert this indexed nonempty intersection.
- `msearch.py`, grep in `Analysis/Normed/Module`:
  `admissible.*[Bb]all|spherically|Ingleton|exists_extension_norm_eq`.
  Twenty-five results, including `exists_extension_norm_eq`. Its full
  signature was read in `Mathlib.Analysis.Normed.Module.HahnBanach`:
  it assumes `IsRCLikeNormedField`, so it is not the ultrametric statement.
- `msearch.py`, LeanSearch: “In an ultrametric normed vector space over a field
  with compact closed balls, the balls centered at g u with radii norm (x - u)
  have a common point when g is a contractive linear functional on a subspace”.
  Eight results, chiefly ultrametric equal-ball lemmas, plus finite dimension
  and real-ball contractibility results; none asserts the node's statement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`:
  `admissible.*[Bb]all|admissibleScalar|spherically|Ingleton`, followed by
  `admissibleScalar|exists_admissible_scalar|compact.*scalar.*ball|scalar.*ball`.
  The related `ContinuousLinearMap.exists_extension_of_proper_ultrametric`
  in `Sheaf.Analysis.Normed.Module.ProperUltrametricScalarExtension` was read
  in full. It states continuous whole-space extension and requires an element
  of norm strictly between zero and one; it is not this scalar-selection lemma.
- `grep -rn 'lem-sfb-admissible-scalar-balls' lean/WeilConjectures` returned
  no declaration. The new theorem's chosen name likewise had no project match.

Source check: the current blueprint at `literature/blueprint/latest/`, the unit's
direct-images proof paragraph (3), was read. As the DAG itself records, this
compact-ball argument is an agent-formulated auxiliary for that paragraph;
the external Ingleton reference remains WANTED. The module does not attribute
the expanded argument to the blueprint's text or claim an external citation
was verified. No statement correction or additional node is necessary.

Validation: `scompile.py NI lem-sfb-admissible-scalar-balls` compiled the single
delivered module successfully both as a sandbox module and under its library
module name (1.6 s and 1.3 s). No errors or unexpected warnings were printed.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
