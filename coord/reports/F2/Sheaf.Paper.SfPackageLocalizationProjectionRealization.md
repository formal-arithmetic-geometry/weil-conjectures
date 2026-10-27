## What changed

Reduced `WeilConjectures.sfPackageLocalizationIntegralTower` in
`Sheaf.Paper.SfPackageLocalizationProjectionRealization` to two smaller input statements.
`sfPackageIntegralRecollementSource` supplies the natural source boundary for the datum's
integral counit and unit; it does not mention compact support.
`sfPackageIntegralSupportTowerNormalization` supplies a projection-normalized natural
comparison with the designated exact strict tower; it does not mention recollement.
Both live in new modules, imported privately by the item.

The combining proof installs the exact tower and limit shifts, applies the existing
`sfPackageLocalizationImage`, and lifts the resulting natural ambient boundary through
right whiskering by the fully faithful constructible inclusion. Composing with the inverse
inclusion shift comparison makes the lift correctly typed. Cancellation proves the required
boundary equation. Naturality of the supplied comparison proves the morphism equation;
the composite shift supplies the last equation. All existing signatures, definitions and
docstrings remain unchanged. Three unused public imports are removed and the proof-only
source-recollement import is private, as recorded in
`coord/changes/F2-integral-localization-proof-inputs.md`. The finite-image and final assembly proofs
are retained. The node's integral proof step and dependencies now describe this argument.

Validation: `lcompile.py --all` compiled all three sandbox modules. The final main file
compiled without warnings in 52.4 seconds; the two input modules compiled in 58.0 and
57.9 seconds. A diagnostic profiler run took 41.3 seconds, following a 101.6-second
loaded-server run; no profiling options remain. No full-library build was run by this worker.

## Proved and sorry left

This is a decomposition, not a net proof gain. Of the two original holes, the whole proof
of `WeilConjectures.sfPackageLocalizationIntegralTower` is replaced by complete Lean code.
It depends on two new, strictly smaller theorems. There is no partial-proof sorry.

Original hole remaining:

- `WeilConjectures.sfPackageLocalizationCommonStages`, node
  `lem-sf-package-localization-projection-realization`.

New holes:

- `WeilConjectures.sfPackageIntegralRecollementSource`, node
  `lem-sf-package-integral-recollement-source`.
- `WeilConjectures.sfPackageIntegralSupportTowerNormalization`, node
  `lem-sf-package-integral-support-tower-normalization`.

Counts: one original hole reduced, one original hole untouched, two holes added;
three textual holes remain across the delivery, a net increase of one.
Each new hole is exactly the entire proof of a named public theorem in its own module.
Each has its source, proof in words, blueprint tag and DAG node. Neither changes data
or chooses an object in a definition from an unproved existence theorem.

## No longer needed

Removed the unused imports `Sheaf.Paper.SfRecollementReductionBoundary`,
`Sheaf.Paper.CompactSupportTotalLimitRealization`, and
`Sheaf.Paper.ProjectionWeilTensorDomainBridge`. Made
`Sheaf.Paper.SfOpenClosedTriangleAllStages` a private proof import. The new normalization
module also imports only what its statement needs; its later proof can import total-limit
realization. The datum already publicly supplies the tower construction and projection
types. The integral assembly uses a source
recollement boundary followed by exact transport, so it does not invoke
`lem-sf-recollement-reduction-boundary`; the node no longer lists that as a direct proof
dependency. The Weil bridge is not used by any declaration in the current item after the
prior removal of the supplemental Weil statements. No library declaration or module is
withdrawn, and no claim is made that these modules are unused by the entire project.

The source recollement, strict-tower, total-limit, constructibility and coefficient-transport
dependencies remain needed through the input statements and untouched common-stage proof.
No unit statement or unit proof step is bypassed. No upstream source file is changed.

## Where the brief, the DAG or earlier work was wrong

The recorded integral route leaves two interface steps implicit. The integral/rational
recollement theorem gives a normalized presentation; the package needs the actual datum's
adjunction maps. The support construction records a coherent tower, whereas this refinement
requires its comparison with the designated tower choice and normalized projections.
Neither follows merely from an isomorphism of individual object values or separate
finite evaluations. The new obligations explicitly retain these two steps. In particular,
no faithfulness of derived tower evaluations or uniqueness of arbitrary cones is assumed.
Empty open and closed strata obey the same statements; the proof imposes no nonemptiness.

## New nodes

`lem-sf-package-integral-recollement-source` records the source distinguished triangle,
uniqueness and naturality for the supplied adjunctions. Its source is the recollement
paragraph of package clause (3), via `prop-sf-open-closed-triangle-all-stages`.

`lem-sf-package-integral-support-tower-normalization` records only the exact support
realization comparison and its Roos projections. Its sources are the strict-tower and
total-limit realization steps of package clause (3). Both nodes retain the item's chapter
and unit. LeanSearch, LeanFinder/Loogle and source grep were run before introducing them;
Mathlib supplies generic exact-image transport, but neither specialized input comparison.
The removal/privatization of public import lines is recorded in
`coord/changes/F2-integral-localization-proof-inputs.md`. Downstream analysis reports zero
module consumers, so there are no consumer adaptations.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
