## What changed

Replaced the proof of
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.constant_slice_internal_presentation`
with a complete finite-biproduct and cokernel argument. Its statement, universes,
public imports, and its consumer `DiscreteConstantPresentationLifting` are unchanged.

The private proved helper `free_image` constructs the comparison at each finite
rank from the rank-one comparison, `mapBiproduct`, `biproduct.isoProduct`, and
`ModuleCat.piIsoPi`. The private proved helper `transport_cokernel` constructs the
internal arrow by full faithfulness, proves its conjugacy equation, transports its
cokernel, and reflects the final isomorphism. The supplied presentation is used
only after these constructions. Rank zero uses the same categorical products and
cokernels; no nonempty or nonzero assumption enters.

The remaining encoding comparison is stated in the new module
`Sheaf.AlgebraicGeometry.ConstantSliceModuleEncoding`, with its own node. It has
no ranks, matrix, cokernel, given trivialization, or finite-presentation conclusion.
It asks only for the underlying module-category equivalence, its comparisons on
inverse images, and its value on the regular module. These are the first step and
the localization/regular-module portion of the existing plan. The finite-matrix
argument is now proved rather than included in that obligation.

The proof imports the new encoding module privately and uses private Mathlib
imports for concrete module products and cokernel preservation. Keeping the large
encoding functors locally irreducible affects this file's proof elaboration only.

## Proved and sorry left

- Closed the one original hole in
  `AlgebraicGeometry.ProEtale.IntegralModelsStacks.constant_slice_internal_presentation`
  (node `lem-sfb-constant-slice-internal-presentation`). The original module has
  zero `sorry` left.
- Added one hole in
  `AlgebraicGeometry.ProEtale.IntegralModelsStacks.constant_slice_module_encoding`
  (node `lem-sfb-constant-slice-module-encoding`). Its body is exactly `:= by sorry`.
- The two private helpers are proved and contain no holes. No definitions contain
  `sorry`, and no data definition chooses a witness from the new existence theorem:
  the theorem's witness is eliminated only within the presentation theorem's proof.

This is a decomposition: one hole closed, one added, net zero holes closed. The
remaining step is the presentation-free encoding comparison; this delivery does
not claim an axiom-free proof of the original theorem's dependency closure.

Validation: the final clean `lcompile.py --all` run compiled both modules in import
order without errors or warnings: `ConstantSliceModuleEncoding` in 30.6 s and
`ConstantSliceInternalPresentation` in 31.6 s. Both are within 60 s. A direct textual
comparison also confirms that the original theorem signature is unchanged. The
delivery tool runs its independent compile, probe, and preflight checks.

## No longer needed

No module or DAG branch is pruned. Both existing public imports remain needed by
the unchanged statement. The existing component dependencies
`lem-sfb-internal-module-operations-transport`,
`lem-cbc-constant-ring-module-sheaves`, and
`lem-weil-proetale-weakly-etale-localization` remain dependencies of the new
encoding node. They are no longer direct proof dependencies of the presentation
node. The constant-sheaf dependency stays direct, since constant sheafification
is used to transport the displayed cokernel. An exploratory explicit import of
`Mathlib.CategoryTheory.Adjunction.Limits` was removed.

## Where the brief, the DAG or earlier work was wrong

The plan is mathematically consistent, but its component declarations do not
state the combined encoding comparison for arbitrary c. In particular,
`InternalModuleOperationsTransport.upperComparison` ends in sectionwise modules,
`constant_ring_module_sheaves` compares constant-ring and fixed-scalar sheaves,
and `weaklyEtale_localization` compares the sites and their module categories.
They do not directly identify the composite occurring in hN with the internal
restriction at U. The normalized finite-discrete comparison and
`ScalarNormalizedConstantModels.exists_comparison` require normalization or
coefficient assumptions absent here, so neither was applied to arbitrary c.

Mathlib searches were actually run through msearch: finite-presentation and
cokernel searches found the elementary transport APIs; searches for the encoding
comparison found module restriction, ordinary equivalence/adjunction assembly,
and pushforwardPushforwardEquivalence, but not the combined comparison. Project
rg searches located and the relevant signatures were read in the component
modules listed above. Blueprint searches for the slice encoding found no separate
existing blueprint statement. The new node retains the parent's blueprint
ancestor and unit; no unit or chapter route changes.

The initial functor-level comparison formulation required expensive kernel
conversion through the nested inverse-image and scalar-restriction functors.
Stating only the pointwise comparisons actually used by the proof removed this
conversion. Profiling showed the final categorical proof itself takes about a
second to elaborate; temporary profiling options were removed.

## New nodes

`lem-sfb-constant-slice-module-encoding`, in
`dag/nodes/sec-six-functors-basics/lem-sfb-constant-slice-module-encoding.json`,
states the presentation-free module equivalence and its inverse-image and regular
comparisons. Its module is
`lean/Sheaf/AlgebraicGeometry/ConstantSliceModuleEncoding.lean`. Its docstring and
node record the construction from Stacks Tags 00YV, 03CY and 04IX and the existing
component nodes, including the actual pulled-back c rather than an assumed scalar
normalization. The zero ring and empty topos are allowed: all constructions are
module/site equivalences and their regular objects; finite ranks never occur in
this remaining statement. No change record is needed: no existing public
interface, definition, consumer, or foreign node is changed.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
