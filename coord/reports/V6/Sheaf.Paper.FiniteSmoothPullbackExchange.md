## What changed

Filled the three original holes in `Sheaf.Paper.FiniteSmoothPullbackExchange`,
with every existing signature, public import and definition body unchanged.
The only added imports are private proof imports. Added three proved private
helpers for scalar cancellation, isomorphism invariance of intrinsic Tor amplitude,
and agreement of the two ordinary-etale bounded-constructible predicates.

`finiteReductionBaseChangeInput` descends the actual input to its finite-ring
etale representative, pulls that representative back, preserves its Tor interval
by the source-library flat-model theorem, and transports the result through the
explicit comparison square and realization equivalences. No smoothness, flatness,
properness or separatedness of the base morphism is used.

`finiteReductionPurityIsIso` uses the source-library orientation-free tensor
formula and the comparison unit at a bounded-below etale representative. Its
argument is adapted from `FiniteCoefficientSmoothPurity.isIso_smoothPurityMap`,
whose absolute-separatedness hypotheses prevent direct application here.
The defining uniqueness equation identifies the specified map with that composite.

`existsUnique_finiteReductionBaseChangeSource` constructs a value in one primitive-root
chart. A genuine remaining arithmetic step is isolated in the new module
`Sheaf.Paper.FiniteSourceChartScalarTransition`; scalar cancellation and uniqueness
are fully proved in the item. Updated the item's proof plan and dependencies.
The change record is `coord/changes/V6-finite-source-chart-scalar-transition.md`.

Validation: both sandbox modules compile through `lcompile.py`; the item compiles
without warnings. The remaining public theorem has its own source, complete
natural-language proof and DAG node. No source-library file is changed.

## Proved and sorry left

Closed all three original textual holes (namespace
`WeilConjectures.PurityFiniteSetting`):

- `finiteReductionBaseChangeInput`: proved from existing declarations, no new hole.
- `finiteReductionPurityIsIso`: proved from existing declarations, no new hole.
- `existsUnique_finiteReductionBaseChangeSource`: reduced to the strictly simpler
  uniform root-chart scalar transition, with categorical cancellation, primitive-root
  existence, construction and uniqueness proved in Lean.

Added one hole:
`WeilConjectures.PurityFiniteSetting.exists_finiteReductionSourceChartScalar`,
node `lem-pur-finite-source-chart-scalar-transition`, in
`Sheaf.Paper.FiniteSourceChartScalarTransition`.
This is a decomposition of the source-map hole, not a completed proof of that
arithmetic step. Thus three original holes closed, one new hole added, net two;
zero holes remain in the item module. Imported declarations may themselves depend
on existing sorries, as intended in stage 3.

## No longer needed

No existing import or module was removed or withdrawn. No whole module is claimed
pruned. The composition-coherence proposition itself is not applied; its module
and node stay needed for the existing normalized `compositionFixedPullbackComp`
construction. The new proof does not import the following alternative dependencies
listed in the original statement plan:

- `Sheaf.Paper.FiniteCoefficientFlatModel` / `lem-sf-flat-model`: the existing
  ordinary-etale flat-model pullback theorem and comparison of Tor intervals suffice.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback` /
  `lem-weil-pbc-ringed-topos-flat-module-pullback`: use the already proved
  ordinary-etale flat pullback instance through the source-library stability theorem.
- `Sheaf.AlgebraicGeometry.PullbackBoundedConstructible` /
  `lem-weil-pbc-pullback-preserves-bounded-constructible`: the proof uses ordinary-etale
  bounded constructibility and then the finite-ring intrinsic origin criterion,
  rather than that pro-etale theorem. Its node is retained as the statement-plan
  reference for bounded-constructible pullback in the dependency inventory.
- `Sheaf.Paper.ProEtaleConstructibleOrigin` / `lem-sf-proetale-constructible-origin`:
  use the stronger already available finite-ring derived origin theorem directly.
- `Sheaf.Paper.CohomologicalSmoothnessTheorem` /
  `thm-pur-cohomological-smoothness`: the canonical ordinary-etale tensor theorem
  supplies the required invertibility directly, preserving the diagonal orientation.
- `Sheaf.Paper.DerivedPullbackTensorIso` /
  `lem-pur-derived-pullback-tensor-iso`, and
  `Sheaf.Paper.CartesianCoefficientTwists` /
  `det-prop-sfb-cartesian-coefficients-twists`: no separate new comparison is chosen;
  the existing source charts give the specified middle map, with their residual
  arithmetic independence isolated in the new lemma. Existing transitive imports
  and statement dependencies are retained.
- `Sheaf.Paper.IntegralFinitePullbackComposition` /
  `lem-weil-pbc-proetale-derived-pullback-composition`: the exact finite-coefficient
  compositor already in `PurityCompositionCoherence` is reused directly.

These are local proof-route observations, not withdrawals of any of those modules
or claims that other users no longer require them. The unit and chapter route is
unchanged: the diagonal orientation remains the specified one in `smoothPurityMap`.

## Where the brief, the DAG or earlier work was wrong

The original definition node had no proof steps despite three construction/domain
obligations in its module. They are now recorded. The existing separated-scheme
purity theorem has a narrower domain than the item, so applying it directly would
add forbidden hypotheses; its proof works with only relative separatedness and
is adapted here without changing either statement.

The sandbox already contained a partial proof and search records at the start of
this continuation. I retained that work, checked its dependencies, repaired the
remaining compilation errors (local realization instances), and completed the
packet. No `.budget` metadata was changed.

Edge cases: the uniform scalar calculation uses only N-annihilation and the
ordered tensor recursion; d=0 gives scalar 1, equal roots admit scalar 1, and
empty schemes and zero complexes have zero identity. The interval argument uses
`min` bounds, so zero objects with unrelated bounds are included. Arbitrary base
morphisms and schemes with only relative separatedness remain in the statements.

## New nodes

`lem-pur-finite-source-chart-scalar-transition` states only that changing the
primitive root rescales every specified source chart by the same natural-number
scalar, independently of the scheme, map and input complex. Its proof is the
inverse primitive-root scalar raised to the ordered tensor degree, transported
through additive comparison and realization. It has no Cartesian square,
exceptional inverse image, existence of a square map or uniqueness conclusion.
The parent genuinely combines it with additive pullback, scalar cancellation,
a primitive root and an existence/uniqueness argument. This is strictly a part
of the original chart-independence argument, not a renamed original theorem.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
