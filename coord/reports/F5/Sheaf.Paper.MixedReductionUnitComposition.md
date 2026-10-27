## What changed

Proved the canonical sequence-site projection, coefficient inclusion, and identity and
composition identifications for exact restriction in
`Sheaf.Paper.MixedReductionUnitComposition`. All public signatures and definitions are unchanged.
The node's first step now records the four construction proofs and their additional
quotient-transition dependency. Its remaining composition plan is retained.
The projection uses the existing compatible-map construction
`SemilinearSections.quotientRingMap`; the coefficient map uses
`NatTrans.ofOpSequence` and the proved quotient-transition square. Restriction isomorphisms
use identity section maps from Mathlib's `restrictScalarsId'App` and
`restrictScalarsComp'App`, and their uniqueness follows sectionwise.

## Proved and sorry left

Closed four of the seven original holes, with no holes added:

- `WeilConjectures.IntegralCoherentReduction.projection_existsUnique`.
- `WeilConjectures.MixedCoherentReduction.ringMap_existsUnique`.
- `WeilConjectures.MixedCoherentReduction.restrictUnit_existsUnique`.
- `WeilConjectures.MixedCoherentReduction.restrictComp_existsUnique`.

The following original holes remain, all attached to
`lem-weil-mixed-reduction-unit-composition`:

- `WeilConjectures.MixedCoherentReduction.ordinary_existsUnique`.
- `WeilConjectures.MixedCoherentReduction.derived_existsUnique`.
- `WeilConjectures.mixedReductionUnit_composition`.

This is a partial proof delivery, not a decomposition: zero split-off statements.
The final trimmed module compiled cleanly through `lcompile.py` in 16.0 seconds.
Its preceding version with the original private imports also compiled in 29.1 seconds.

## No longer needed

Removed the following unused proof imports from the delivered module:

- `Mathlib.CategoryTheory.Adjunction.Mates`.
- `Sheaf.Paper.SemilinearDerivedSections`.
- `Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`.
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`.
- `Sheaf.Paper.QuotientScalarComparisonDescent`.
- `Sheaf.CategoryTheory.StrictRoosHomotopyFunctor`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.CategoryTheory.StrictRoosComparison`.

These imports are not used by the four completed construction proofs. Their nodes remain
in the main theorem's proof plan because that original hole is unchanged; no mathematical
node or module is declared globally unnecessary. All original public imports are retained.
The sole private proof import added is `Sheaf.Paper.CoefficientExtensionReductionData`.
This proof-dependency change is recorded on the node; its transitive DAG dependencies do
not reach the item, so it introduces no cycle.

The original composition proof remains necessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The coefficient transition square already has a
proved declaration, `WeilConjectures.coefficientExtensionQuotient_naturality`, in
`Sheaf.Paper.CoefficientExtensionReductionData`; it avoids an expensive unfolding of
constant sheafification in the direct proof. The basic construction proofs also need no
flatness of quotient maps. Identity fields, arbitrary section objects, and n = 0 are
included by the formulas and by quotient induction for coefficient composition.

Searches: LeanFinder for compatible maps from a constant diagram returned
`NatTrans.ofOpSequence`; Loogle found `Sheaf.hom_ext`; Mathlib grep found the ordinary
restriction identity/composition isomorphisms. A further LeanFinder search for completed
mixed-unit composition returned ordinary `ModuleCat.extendScalars_assoc` variants, which
do not directly state the whole sequence-site completed comparison. Source inspection
found the proved quotient-transition square used here.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
