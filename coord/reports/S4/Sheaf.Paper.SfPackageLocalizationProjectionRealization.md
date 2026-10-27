## What changed

Only `Sheaf.Paper.SfPackageLocalizationProjectionRealization` changes on the Lean side.
Existing public signatures and definitions are unchanged. The main theorem is moved below
its existing refinement theorems so that its proof can assemble their conclusions.

`sfPackageLocalizationWeilFactorization` uses the existing geometric compactification
identity and faithfulness of the full-subcategory and over-category forgetful functors.
`sfPackageLocalizationWeilMapComp` uses functoriality of geometric base change.
The main conjunction uses the existing finite-image, integral-tower and common-stage
refinements and the four projection-formula laws. Its integral triangle is the ambient
triangle retained by the tower witness; its rational and common-stage triangles are the
ones retained by the single field-system witness. Coefficient compatibility is exactly
`compactSupportProjectionFormula_coefficients`.

A completely proved private lemma establishes that the coefficient prime is a unit:
cardinality determines characteristic D.p in the finite base field, the distinct prime
C.l is a unit there, and this unit maps into D.k. This avoids importing the holed
`sfPackageCoefficientIsUnit` lemma. The node records the actual assembly route.

## Proved and sorry left

Original holes: 10. Closed: 4. Added: 0. Remaining: 6.

Closed declarations:

- `sfPackageLocalizationWeilFactorization`.
- `sfPackageLocalizationWeilMapComp`.
- `sfPackageLocalizationProjectionRealization` (from existing named refinements).
- `sfPackageProjectionCoefficientCompatibility`.

Remaining named theorem holes, all attached to
`lem-sf-package-localization-projection-realization`:

- `sfPackageLocalizationFiniteImage`.
- `sfPackageLocalizationIntegralTower`.
- `sfPackageLocalizationRationalization`.
- `sfPackageLocalizationCommonStages`.
- `sfPackageLocalizationWeil_rational`.
- `sfPackageLocalizationWeil_common`.

No new module, public statement, definition hole, or split-off hole is delivered.
The main theorem still depends on the existing refinement holes above.

## No longer needed

Removed private proof imports:

- `Sheaf.Paper.CompactSupportReductionTower`.
- `Sheaf.Paper.SfIntegralConstructibleTriangulated`.
- `Sheaf.Paper.SfRationalizationKaroubi`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`.
- `Sheaf.Paper.DerivedPullbackTensorHom`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`.
- `Sheaf.Paper.CompactSupportDirectImageTriangulated`.
- `Sheaf.Paper.FiniteTorStability`.
- `Sheaf.Paper.SfIntegralCompactSupportConstructible`.
- `Sheaf.Paper.CompactifiedTowerComparisons`.
- `Sheaf.Paper.PbcRationalTransport`.
- `Sheaf.Paper.ScalarExtensionExactIntrinsic`.
- `Sheaf.Paper.BasicOperationsCoefficientReduction`.
- `Sheaf.Paper.PbcDescentFunctors`.
- `WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius`.

The completed assembly does not use these imports directly. Many are already in the
public dependency closure; others support the unfinished refinement plans. The original
mathematical dependencies of those unfinished refinements remain in the node: removing
an unused proof import here does not withdraw their obligations. No whole module is
withdrawn and no source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No statement or definition is changed. The existing named refinements already imply
all four localization conclusions of the main theorem. The projection coefficient
theorem already has exactly the supplied coefficient-compatibility conclusion.

The finite-image proof was developed using natural recollement-boundary uniqueness,
normalized adjunction comparisons, and triangulated intrinsic compact support. Its
generic categorical helpers compile, but the concrete full proof exceeded the file
limit during elaboration. It is not delivered as a new hole or new statement; the
original finite-image theorem remains unchanged. The attempted proof is retained
only in the sandbox scratchpad.

The integral refinement still requires identifying the normalized support construction
with the designated strict tower, including projections and shifts. `supportConstruction`
supplies a normalized tower witness but does not itself assert equality with the
particular tower required by `SfPackageLocalizationTowerBoundary`. That obligation is
not replaced by an equality inferred merely from separate evaluations.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
