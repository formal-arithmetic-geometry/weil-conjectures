## What changed

Completed `realization_additive` from the proved additive scalar functor and the additive
inverse section equivalence. Extracted the unchanged concrete models into
`Sheaf.Paper.FiniteFreeDualChainModels`, publicly re-exported by the original module.
The original comparison theorem keeps every binder, universe and conclusion.

The comparison proof now combines two strictly separate statements: the ordinary signed
finite-basis chain calculation and generic localization of a specified ordinary evaluation
for arbitrary native complexes. The combining proof constructs finite-free sheaf models
for the realized terms, proves termwise exact Hom using finite-retract dual exactness,
applies bounded exact-term Hom to every quasi-isomorphism, derives native K-flatness from
`0 → Z` and the ordinary comparison, takes the evaluation-normalized comparison from
its existing theorem, and applies generic evaluation localization. It also proves invertibility of the native evaluation
transpose by cancelling the comparison maps in the localization equation.
All these connecting steps contain complete proofs. The final strengthened combining proof compiled in 26.7 seconds, without errors or
warnings. The final localization statement, with the normalized comparison supplied
as input, compiled in 19.5 seconds in the joint check. To avoid repeated expansion of the concrete native
localization maps, the combining proof treats those definitions as locally irreducible
and applies categorical isomorphism cancellation directly to the localization equation.
A proved private categorical helper reflects and cancels the final composite without
expanding the concrete derived equivalence.

The extraction is documented in `coord/changes/E5-finite-free-dual-chain-models.md`.
No source-library module or target statement is changed. The previous session's pending
verification of additivity was recovered successfully after the launcher resume.

## Proved and sorry left

Original holes: 2.

- Closed by proof: `AlgebraicGeometry.ProEtale.FiniteFreeDualComparison.realization_additive`.
- Reduced by a complete connecting proof:
  `AlgebraicGeometry.ProEtale.FiniteFreeDualComparison.finiteFreeDualChainComparison`
  (node `lem-sfb-finite-free-dual-chain-comparison`).
- Added and still `sorry`:
  `AlgebraicGeometry.ProEtale.FiniteFreeDualComparison.finiteFreeOrdinaryChainComparison`
  (node `lem-sfb-finite-free-ordinary-chain-comparison`). This is only the ordinary
  finite-basis comparison, naturality and explicit inverse; it asserts no derived result,
  K-flatness, or Hom quasi-isomorphism invariance.
- Added and still `sorry`:
  `AlgebraicGeometry.ProEtale.FiniteFreeDualComparison.nativeOrdinaryEvaluationLocalization`
  (node `lem-sfb-native-ordinary-evaluation-localization`). This is generic localization,
  conditional on supplied ordinary evaluation data, K-flatness and full Hom invariance;
  it has no scalar ring, finite-free hypotheses, boundedness or basis formula. It takes
  the evaluation-normalized comparison as input and leaves invertibility of the native evaluation transpose to the parent proof.

Thus 2 original holes have complete bodies, 2 separate holes remain, and the main theorem
is a decomposition rather than an independent closure of its whole mathematical argument.
No `sorry` is inside a definition or private helper. No arbitrary existence witness is
used to define data. The retained ordinary statement includes empty ranks and intervals,
zero rings, arbitrary coefficient maps, odd shifts, and unbounded targets. The localization
statement is conditional on the actual specified evaluation and its naturality, so it
cannot replace the ordinary calculation.

## No longer needed

The main module no longer directly imports `InternalSectionScalarAdjunction`,
`ConstantFiniteFreePresentationExtension`, `RingedSiteBoundedEvaluationAssembly`,
`KFlatResolutionIndependentCoefficients`, `SiteDerivedTensorDescentIndependentCoefficients`,
or `OrdinaryModuleDerivedInternalHom`. The lower statements retain the relevant proof
plans and dependencies. These are direct-import removals, not withdrawal of those nodes
or a claim that their modules are globally pruned.

The scalar-adjunction comparison is unnecessary for identifying this chart: its concrete
definition already uses ordinary scalar extension followed by the inverse section
equivalence, whose counit is `sectionChartIso`. No new arbitrary native tensor is chosen.
`lem-sfb-internal-section-scalar-adjunction` and
`Sheaf.CategoryTheory.InternalSectionScalarAdjunction` are therefore absent from both
the new DAG dependency closure and this item's Lean import closure.
The other original dependencies remain in the lower ordinary or localization argument.
No module is withdrawn. Removed parent `tool_uses` entries for internal-section tensor
comparison, scalar adjunction, scalar dual realization, constant finite-free extension,
bounded evaluation assembly, K-flat resolution, ordinary evaluation localization, tensor
descent when those now occur only below a retained lower
statement or are unnecessary. Existing approvals still needed below are not deleted from
their owning nodes. The bounded exact-term Hom and module-object comparison approvals stay on the parent.

## Where the brief, the DAG or earlier work was wrong

The existing `ScalarPerfectDualRealization` interface fixes equal site-object,
site-morphism and coefficient universes. The pro-etale chart here has site objects
in `u+1`, morphisms in `u` and coefficients in `u+1`, so that interface cannot be
applied literally to this statement. Its finite-basis argument remains valid.
The proved `ScalarPerfectFiniteFree` helpers support independent universes; the
connecting proof reuses its rank-one constant-module isomorphism and finite-product
preservation to establish the exact-term result directly. No signature of the
other group's scalar-dual module is changed.

## New nodes

`def-sfb-finite-free-dual-chain-models` attaches the unchanged concrete chart and
native evaluation definitions, together with proved additivity, to the shared model
module. It prevents an import cycle between the two independent lower statements.

`lem-sfb-finite-free-ordinary-chain-comparison` records parent proof steps 2–4:
the signed scalar-dual chain isomorphism, generator normalization, naturality and
the inverse in every finite basis.

`lem-sfb-native-ordinary-evaluation-localization` records parent proof steps 6–7
for arbitrary complexes with supplied ordinary evaluation and exactness data.
The original module proves the K-flat and Hom invariance hypotheses itself.

Each lower theorem has a full source-based proof in its docstring and matching DAG node.
The models node uses the primary realization signature as its Lean statement and lists
all relocated declarations in its attachment. This repairs the first preflight diagnostic.
The unit route and the original theorem statement are retained.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
