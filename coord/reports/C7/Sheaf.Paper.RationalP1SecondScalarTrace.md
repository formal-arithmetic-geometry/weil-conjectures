## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.RationalP1.second_scalar_trace` by a
unit/Chern generator argument, retaining its exact signature and its existing public imports.
Added proof imports of `RationalP1ScalarChernSplittings`, `RationalP1ScalarChernDegree`,
and `RationalP1ScalarChernBaseChange`, and Mathlib imports for additive biproducts,
invertibility of prime casts, and the derived t-structure. The transport definitions publicly import the completed
Chern lift module because the normalization uses its named `Presentation.systemChern`
map. Keeping that map folded also preserves the recorded derived-category instances.

`RationalP1ScalarChernMaps` constructs the independent q and p2 Chern generators by
explicit realization and scalar-extension composites. Each starts with a completed Chern
adjunct supplied by the existing proved `diagonalTrace_completedChern_lift`; no definition
chooses an arbitrary witness. The normalization records the whole-system equation, not
just finite reductions. The closure path uses the bottom finite subfield and its recorded
`Family.toClosure` comparisons.

The private categorical proof compares the two actual binary splitting maps. On each
injection the two generator equations give a commuting square. Negative Ext vanishing proves the zero trace values directly from the degrees of
the source and target sheaves. Additivity is transported through the existing exact-pullback/levelwise-derived
comparison. The additive functor's binary-biproduct comparison and the diagonal endpoint comparison are invertible, so the
specified exchange is invertible. Cancelling the source splitting reduces the trace
square to its two generator values, zero and one. The final unit comparison is obtained
by unfolding `scalarUnitPullIso` and cancelling inverse `singleUnitIso`.

This is a decomposition into intrinsic Chern splittings and geometric preservation of
specified generators. The Chern maps are constructed independently of the exchange and
of the desired trace equation; there is no existential change of basis.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.RationalP1.second_scalar_trace`
(node `lem-sfb-rational-p1-second-scalar-trace`). Its combining proof and private
`trace_square_of_generators` contain no sorry.

Also proved `AlgebraicGeometry.ProEtale.RationalP1.scalar_chern_degree`
(node `lem-sfb-rational-p1-scalar-chern-degree`), including completed Chern degree and
its actual realization, integral, rational and closure coefficient transport. This
removes the degree-one facts from the residual splitting obligation. Its completed
step is the proved `completed_chern_degree` in `RationalP1CompletedChernDegree`,
separated from scalar transport to keep the files within the compile limit. The
q and p2 scalar transports are also proved separately in `RationalP1ScalarChernQDegree`
and `RationalP1ScalarChernP2Degree`; the combined theorem pairs them.

Added two holes, each the whole proof of a public theorem in its own module:

- `AlgebraicGeometry.ProEtale.RationalP1.scalar_chern_splittings`
  (`lem-sfb-rational-p1-scalar-chern-splittings`): the independent q and p2 unit/Chern
  splitting isomorphisms. Its conclusion contains no exchange or trace equation.
- `AlgebraicGeometry.ProEtale.RationalP1.scalar_chern_base_change`
  (`lem-sfb-rational-p1-scalar-chern-base-change`): the two generator equations for
  the actual exchange. Its conclusion contains no trace, inverse splitting, or
  invertibility assertion.

Thus this is one upper hole closed and two strictly smaller geometric obligations
added, a decomposition, not a claim of a net reduction in holes. The item has zero
remaining direct holes. Its checked compile took about 40 seconds; all eight modules
have compiled successfully within the enforced per-file limit. All definitions are explicit and contain zero sorry.

## No longer needed

No existing public import is removed and no existing module is withdrawn.

The main node no longer directly invokes `def-sfb-diagonal-trace-models`,
`def-sfb-diagonal-trace-presentation`, `def-sfb-diagonal-coefficient-reference`,
`def-sfb-diagonal-coefficient-diagrams`, or `def-sfb-diagonal-coefficient-category`
as proof steps: their uses now occur in the explicitly stated Chern-generator steps
or in their statement dependencies. They remain needed.

`lem-pe-bounded-continuity-coefficient-restriction` and
`lem-pd-module-ringed-topos-derived-comparison` are removed from this node's proof
plan and are not imported for the new proofs. Family already supplies the exact scalar
mates and their invertibility on the shifted lines, including a finite-field to closure
leg. The calculation uses the native module-object functors throughout, so it does
not need a new ringed-topos transport. These nodes may still be needed elsewhere;
this report does not request their withdrawal.

## Where the brief, the DAG or earlier work was wrong

The existing base-change theorem for two full diagonal coefficient families does not
apply directly: this item supplies one Reference and no completed cycle-system data on
a second base. The earlier prose did not make the needed Chern generators, splitting
maps, or their native comparison equations available as Lean declarations. This delivery
makes those specific steps explicit and proves their combination.

The item was initially listed in rework and had a quarantine archive; its original
source reappeared in the shared tree during inspection. The current source and archive
have the same statement, which is preserved. No quarantine file is removed.

## New nodes

`def-sfb-rational-p1-scalar-chern-maps`, in `RationalP1ScalarChernMaps`, defines the
whole-system normalization and the actual realized/scalar Chern arrows, twisted-unit
adjunct and root/unit pullback comparisons. It contains no holes and chooses no data
from an unproved existence theorem.

`lem-sfb-rational-p1-scalar-chern-splittings`, in `RationalP1ScalarChernSplittings`,
is the intrinsic two-splitting calculation. Its
docstring and node specify the complete route through the strict splitting, completed
limit, exact realization, and actual coefficient mates.

`lem-sfb-rational-p1-scalar-chern-base-change`, in `RationalP1ScalarChernBaseChange`,
is naturality on the two actual generators. Its docstring and node specify the
adjunction-unit calculation and the positive section/Kummer pullback calculation before
any trace is applied.

`lem-sfb-rational-p1-completed-chern-degree`, in `RationalP1CompletedChernDegree`,
proves completed degree one from the strict Chern component, whole-system
normalization, and completed-unit faithfulness. It adds no hole.

`lem-sfb-rational-p1-scalar-chern-degree`, in `RationalP1ScalarChernDegree`, proves
trace one on both transported Chern adjuncts. The completed calculation follows the
existing proved private helper in `DiagonalUniformizerTraceChernDegree`; the successive
coefficient steps follow formally from the supplied trace squares. It adds no hole.

`lem-sfb-rational-p1-scalar-chern-q-degree` and
`lem-sfb-rational-p1-scalar-chern-p2-degree` prove each native scalar degree equation
separately, with their actual realization and coefficient transport. They contain no
holes and keep the two transport calculations below the per-file compile limit.

No change record is required: no existing signature, definition, instance, attribute,
or public import changes, and no other existing module is edited.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
