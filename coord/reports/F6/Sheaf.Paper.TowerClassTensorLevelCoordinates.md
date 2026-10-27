## What changed

The item now evaluates an explicitly constructed natural isomorphism of ordinary systems.
`TowerClassTensorComparison` constructs it from the existing
`SemilinearSections.geometricOrdinaryTensor_exists`: forget the derived fields of
`g.generic`, use `T.system_natural` for the monoidal tensor, conjugate by the existing natural
sheafification comparisons with the explicit site tensor, and transport along the
specified coefficient, transition and pull-functor equalities.
The bridge abbreviates `SheafOfModules.siteSheafTensorRightIso`, with a proved
component formula identifying its existing monoidal presentation. The source and target
still use exactly the existing `tensorRight` and `tensorPure`; no tensor or inverse-image
notion was replaced. The bridge's `siteTensorIso_pure` is proved from naturality of the
module sheafification unit.

The item privately imports `ProEtaleToposFunctorialityInverseImage` to obtain
`PreservesFiniteLimits` for the actual set-sheaf inverse image before applying the
ordinary tensor existence theorem. This adds no hypothesis to the item.

The horizontal equation follows from naturality of the ordinary transition with respect
to this system map. Naturality in M follows by applying evaluation to the constructed
natural transformation's naturality equation. These proofs do not assert faithfulness of
a derived evaluation functor. The final finite adjunction section formula is isolated in
`TowerClassTensorComparisonNormalization` for this fixed, explicitly constructed map.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.SpTowerClasses.exists_tensorLevelCoordinates`
(`lem-sfb-tower-class-tensor-level-coordinates`). The item module contains zero holes.

Added one hole:
`AlgebraicGeometry.ProEtale.SpTowerClasses.TensorCoordinates.comparison_normalization`
(`lem-sfb-tower-class-tensor-comparison-normalization`). This is a decomposition,
not a net reduction in hole count: one original hole closed, one lower hole added.
The lower statement contains only the pure-section formula for a fixed constructed
comparison. It has no existential comparison, no horizontal compatibility clause and no
naturality clause. The construction of the comparison and the combination of all three
clauses in the item are actual Lean proofs, so the lower statement does not rename or
repackage the original obligation.

All definitions in the new construction module have actual bodies. No arbitrary witness
of an unproved existence theorem is used as definition data: the original theorem obtains
an existing ordinary tensor record in its proof and passes it explicitly to the construction.

## No longer needed

No original imports were removed, and no modules are withdrawn or claimed to be pruned.
The item does not directly reconstruct `geometricTensorComponent` or directly invoke
`geometricTensorComponent_horizontal`: it reuses the already assembled `T.system`.
The horizontal lemma and its module remain dependencies of
`geometricOrdinaryTensor_exists`, so they are still needed by the library.
The original direct dependencies `def-coef-semilinear-geometry-base`,
`def-coef-semilinear-geometry-derived`, and `lem-sp-tower-ordinary-unit-evaluation`
remain below the isolated normalization step. Their mathematics is not pruned.
The unit route in `sk-prop-diagonal-tower` is preserved.

## Where the brief, the DAG or earlier work was wrong

The DAG described finite tensor reconstruction although its declared ordinary tensor
result already supplies a compatible system comparison and its naturality. Reusing that
comparison makes the first two clauses formal consequences of evaluation and transition
naturality. The explicit site tensor is not definitionally the monoidal tensor used by
that result; a natural sheafification bridge, with its actual pure-section formula, is
needed. This delivery constructs that bridge rather than treating the two APIs as equal.

A first specialized copy of the geometry's ordinary record caused a kernel timeout.
The final construction abstracts the record projection over arbitrary sites before
specializing it to the scheme geometry. No shared definition was changed. The
standalone profiled construction compiled in 21.7 seconds; profiling options were
removed before delivery. All three modules compiled in import order.

For new statements, zero modules and empty charts are covered by the same pairing and
unit constructions. No flatness assumption on coefficient quotient maps is introduced.
The three Mathlib searches and the local source search are recorded in both new nodes;
they found general pullback-unit and sheafification tools, but no section-normalized
comparison in these actual tower coordinates.

## New nodes

`def-sfb-tower-class-tensor-comparison` records the explicit natural sheafification
bridge, its proved pure-section formula, and the transported natural system tensor
comparison. Its module is `Sheaf.Paper.TowerClassTensorComparison` and contains no sorry.

`lem-sfb-tower-class-tensor-comparison-normalization` is only the finite adjunction
section formula for that fixed comparison. Its module is
`Sheaf.Paper.TowerClassTensorComparisonNormalization`; its docstring and node give the
argument from `T.evaluation`, `T.level_pure`, the topos unit naturality,
`level_unit_underlying`, `hpush`, and `geometry_unit_evaluation`. The remaining work is
the finite coordinate and section transport, not existence or horizontal assembly.

The proved shared bridge is supplied by
`lem-weil-pbc-independent-sheaf-tensor-colimits` (including its registered explicit
site comparison declarations), used as a tool; its colimit conclusion is not assumed
to imply the bridge.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
