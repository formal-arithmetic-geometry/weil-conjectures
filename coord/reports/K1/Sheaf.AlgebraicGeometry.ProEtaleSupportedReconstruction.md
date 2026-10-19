## What changed

Completed `AlgebraicGeometry.ProEtale.supportedLambda_isIso` and
`AlgebraicGeometry.ProEtale.supported_reconstruction`, preserving their signatures and all
existing definitions. Added proved private adjunction calculations and an abelian
supported-open-counit argument. The latter uses disjointness, full faithfulness of open
extension, and exact inverse images to detect an isomorphism through its kernel and cokernel.
The forgetful functor on module objects reflects isomorphisms and carries the specified
module units and counits to the abelian ones. No alternative adjunction is chosen.

Updated the item's proof plan and dependencies. Attached the disjoint-image result already
proved in the source library to a new node; this adds no Lean declaration. Removed unused
imports, including public imports, as recorded in
`coord/changes/K1-supported-reconstruction-imports.md`. The current source has 447
transitive importers (`tools/downstream.py`), headed by
`Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence`; all retain the same public
interfaces, so no consumer adaptation is required. The unit's realized statement and steps
are not bypassed.

Validation: the retained proof compiled cleanly through `lcompile.py` against the current
compiled source in this session (12.2 seconds, exit 0). The required delivery dry run
also checks declaration axioms and import pruning. Interrupted dry-run calls were checked
before retrying; no push has been attempted. The current dry run is waiting in the shared
worktree-capacity queue; its final result will be reported by the delivery tool.

## Proved and sorry left

Closed both original holes:

- `AlgebraicGeometry.ProEtale.supportedLambda_isIso`
  (`lem-sfb-proetale-supported-reconstruction`).
- `AlgebraicGeometry.ProEtale.supported_reconstruction`
  (`lem-sfb-proetale-supported-reconstruction`).

Two holes closed; zero added; zero remaining in the delivered Lean module. No split-off
obligations. Existing imported support results remain separate project dependencies.

## No longer needed

Removed imports:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleAdjunction`.
- `Sheaf.AlgebraicGeometry.RingedTopoiModuleAdjunctionRepair`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal`
  (already available through the statements' imports).
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
  (already publicly imported by the retained statement dependencies).
- `Sheaf.CategoryTheory.RingedSiteModules`
  (already publicly imported by the retained statement dependencies).

The proof no longer uses nodes `lem-weil-pbc-proetale-ringed-open-closed`,
`def-weil-pbc-exact-sequence`, or `lem-weil-pbc-conjugate-iso-unit-equation` as proof
inputs: direct abelian support and reflection of isomorphisms replace the ringed
localization sequence and comparison of adjunctions. Accordingly the obsolete
`lem-weil-pbc-proetale-ringed-open-closed` tool-use entry is withdrawn.
`def-weil-sheaf-of-modules-category` remains a statement dependency but is not an
additional proof lemma. The ringed-open-closed module remains a public import because
`supportedRingAb` uses its concrete coefficient construction.

## Where the brief, the DAG or earlier work was wrong

The earlier plan's ringed localization theorem uses a different module-category
presentation. It is unnecessary to compare its adjunction to the specified one:
the underlying abelian unit and counit suffice. This is a shorter argument below the unit
level and does not change any statement or definition. The retained sandbox had the full
proof, report and change record. The record's zero-consumer inventory was stale; it is now
replaced by the current downstream inventory, with every unchanged consumer listed.
There are no disputed statements.

## New nodes

`lem-sfb-proetale-open-disjoint-direct-image` records the existing source theorem
`AlgebraicGeometry.ProEtale.isZero_upperStar_lowerStar_of_disjoint` specialized to abelian
sheaves. Its `lean.existing` record points directly to the source module and has no Lean
file in this delivery. Unlike the existing etale node `lemma-openclosed-vanishing-lowerstar`,
it concerns the pro-etale site. The proof needs this orthogonality to show the closed
restriction of open extension vanishes. No new Lean file and no new hole is introduced. Its source is the
empty-fibre calculation used in Stacks Tag 09AH and already formalized in the source
module `FiniteCoefficient.UpperLowerStar.ClosedImmersion`.

Change record: `coord/changes/K1-supported-reconstruction-imports.md`.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
