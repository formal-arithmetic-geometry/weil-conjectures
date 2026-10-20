## What changed

Replaced the hole in `WeilConjectures.integralOperations_preserve_constructible` by
an explicit proof, without changing its statement or either canonical comparison.
The finite pullback argument pulls back the actual stratification, uses the proved
constant-module composition and finite local-constancy pullback comparisons, and
transports the same cohomological interval through exact inverse image.

For tensor, the proof obtains a uniform Tor interval from `integral_residue_tor`,
compares actual finite reductions with K-flat change of rings, and uses the existing
categorical `homologyConcentratedIn_tensor_of_torAmplitudeIn_left`. Only the first
input needs the Tor test; the second input's cohomological interval suffices.
`finiteTensor_constructible_cohomology` supplies constructible output cohomology.
The proof combines these finite-level results with the separate Roos-effectivity
statement and transports all conclusions through the canonical reduction comparisons.
A proved private helper in the new module constructs the strict Roos distinguished
triangle with its actual localized projections, using exact products and the mapped
mapping-cocone triangle. The retained hole still requires normalized finite-operation
tower data and application of normalized DVR effectivity to that data.

Added `Sheaf.Paper.IntegralOperationRoosEffectivity`, isolating the unbounded
normalization/effectivity calculation before any constructibility argument. The three
existing definitions `integralOperationRoosProjection`, `integralPullbackFiniteComplex`,
and `integralTensorFiniteComplex` moved there verbatim, retaining their names and
exposure. The original module publicly re-exports the new module. This is necessary to
state the separate effectivity result without an import cycle. The two comparison
definitions and the upper theorem retain their signatures. No source-library file or
target was changed.

Single-file compilation was used throughout. The complete original module compiled
without warnings in 52.9 seconds after the local-instance and reduction-model
interface fixes. A subsequent import-order check reached the time limit, so the
finite-reduction map equation was made explicit to avoid expanding the chosen functor;
the final check uses that version. The final import-order check compiled the effectivity
module in 22.8 seconds and the original module in 45.5 seconds, without warnings.
The new module, including its proved strict-triangle helper, initially compiled in
49.5 seconds. Explicit exact-restriction instances and a narrower transparency setting
then reduced its profiled compile to 9.9 seconds. Profiling options were removed before
the final clean check. The final delivery checks are recorded by deliver3.py.
Temporary truncation and heartbeat diagnostics were removed. The site-smallness
witness is a private alias of essentiallySmallSelf registered as a local instance,
so it adds no public instance to the module interface. Keeping the alias reducible
avoids repeated expansion of the coefficient/sheafification data in the finite
reduction comparison; an opaque theorem witness made that block exceed the limit.

## Proved and sorry left

Original module: one named hole closed,
`WeilConjectures.integralOperations_preserve_constructible`; zero holes remain there.
Its proof from its dependencies is complete. The private `strictRoosTriangle`
helper is also proved, with no additional holes.

One named hole added:
`WeilConjectures.integralOperationRoos_effectivity`, in
`Sheaf.Paper.IntegralOperationRoosEffectivity`, node
`lem-pur-integral-operation-roos-effectivity`. Its proof body is exactly `by sorry`,
and its docstring and node give the complete normalization/effectivity argument.
It is the unbounded derived-completion part of the original proof, with no
constructibility assertions or constructibility hypotheses. This is a decomposition:
one upper hole closed and one lower hole added, net zero among changed declarations.
The pinned sorry ledger determines any change in the targets' import closure.
No private helper or definition contains a hole.

## No longer needed

The upper proof no longer directly imports:

- `Sheaf.Paper.NormalizedDVRTower` and `Sheaf.Paper.NormalizedDVREffectivity`:
  needed only in the separate effectivity calculation, not pruned from the packet.
- `Sheaf.Paper.KFlatRingedToposPullback` and
  `Sheaf.CategoryTheory.ModulePullbackTensorIso`: likewise retained for effectivity.
- `Sheaf.Paper.FiniteCoefficientFlatModel`: replaced by the existing generic source
  tensor/cohomology interval theorem (`lem-sf-source-tensor-cohomology-interval`).
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: neither the upper proof nor its
  effectivity statement uses slice operations.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` and
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: the proved
  `Stratification.pullback` already supplies the required strata.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact` and
  `WeilConjectures.CategoryTheory.Abelian.Flat.Basic`: their needed interfaces are
  already exposed by the precise comparison and source tensor modules.

Redundant public imports of `IntegralDerivedOperations`,
`IntrinsicFiniteTorsionConstructibility`, `DerivedScalarExtensionRestrictionAdjunction`,
`DerivedTensor`, and `ProEtaleInverseImage` were removed from the upper module;
the two remaining public imports expose all these same interfaces transitively.
The direct flat-coproduct dependency `lem-weil-pbc-flat-coproduct` is unnecessary:
K-flatness of the finite total tensor follows from associativity and K-flatness
of its two factors; no flatness assertion about its terms is used downstream.
The original top-level tool approvals for this node and `lem-sf-flat-model` were
removed, preserving the order of all other approvals.

The original node no longer lists these direct proof dependencies:

- `def-coef-normalized-dvr-tower`, `lem-coef-normalized-dvr-effectivity`,
  `lem-weil-pbc-ringed-pullback-preserves-kflat`,
  `lem-weil-pbc-ringed-topoi-module-pullback-tensor`, and
  `prop-weil-pbc-proetale-constant-exact`: retained through the new effectivity node.
- `def-weil-closed-immersion` and `lem-pur-scheme-constructible-preimage`:
  the proved source `Stratification.pullback` supplies the strata directly.
- `def-weil-finite-torsion-constructibility` and `def-weil-proetale-inverse-image`:
  remain statement dependencies and are exposed through the precise finite interfaces.
- `lem-sf-flat-model` and `lem-weil-pbc-flat-coproduct`: bypassed by the categorical
  interval proof and K-flat tensor reassociation, respectively.

No module was withdrawn, no upstream declaration was removed, and no global module
pruning is claimed. The normalization dependencies remain required in the new node.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or changed mathematical definition. No existing declaration
constructs a NormalizedDVRTower for either specified finite-operation tower: the
generic normalized-DVR effectivity theorem still needs their semilinear transitions,
quotient cocycles, and normalization comparisons. The retained separate lemma records
that bridge; the strict-triangle calculation is proved. The planned second Tor
interval and explicit pro-etale bounded flat models are unnecessary: the existing
categorical tensor bound uses the first Tor interval and the second cohomology
interval directly. The original unit route is retained.

The resolution theorem supplies flatness using the monoidal tensor functor, while
`integralOperationsGoodComplex` asks for site tensor flatness. The proof explicitly
transports this using `siteSheafTensorRightIso`. The two ordinary reduction functors
are definitionally the same chosen
change-of-rings functor. An explicit equality of their complex models transports
the existing unrestrictedTowerResolutionIso without asking elaboration to normalize
the whole chosen functor. An explicit equation for its map likewise lets Lean cancel
the coefficient-identification casts without expanding that functor. The effectivity
statement uses the existing unrestricted restriction instances and respects transparency
except during type conversion. These are interface conversions, not statement repairs.

The new effectivity assertion was checked on the empty scheme, zero complexes,
positive exponent one (index zero), identity pullback, and unbounded good complexes.
Its normalization argument is independent of cohomological bounds; exact countable
products and normalized DVR effectivity are precisely the required hypotheses.

## New nodes

`lem-pur-integral-operation-roos-effectivity` records the completion and canonical
finite-reduction assertion for the strict pullback and tensor towers of arbitrary
good complexes. It is sourced to Stacks Tags 099M/099N and Bhatt--Scholze
Lemmas 3.5.4--3.5.7. It retains the normalization, K-flat pullback, tensor compatibility,
and normalized DVR effectivity dependencies. Its statement is strictly the
unbounded completion portion of the argument; all finite constructibility and
uniform-bound deductions are proved in the original module.

Change record: `coord/changes/integral-operation-roos-interface.md`. The original
node's proof route and Lean attachments were updated to match the delivered files.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
