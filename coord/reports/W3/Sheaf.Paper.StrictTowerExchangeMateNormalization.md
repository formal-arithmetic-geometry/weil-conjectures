## What changed

Proved `AlgebraicGeometry.Scheme.exchangeResPush_existsUnique` in the item module.
The proof constructs the comparison as a derived adjunction mate. Its universal
unit equation follows from `derived_mate_factors`; exact scalar restriction
preserves K-injectives because flat scalar extension is its exact left adjoint.
The unit equation proves invertibility on K-injective representatives and then
on all derived objects. `derived_comp_ext` proves uniqueness.

Added four proved private helpers for these arguments: termwise preservation
of K-injectives, its scalar-restriction specialization, abstract derived mate
uniqueness, and the ordinary termwise restriction mate. Existing private helpers
are retained.
Public declaration signatures, public imports, and existing definition bodies
are unchanged. The item compiles without errors or warnings via `lcompile.py`.

## Proved and sorry left

Closed one of the two existing holes:
`AlgebraicGeometry.Scheme.exchangeResPush_existsUnique`.
Added zero holes and split off zero theorems.

The one remaining hole is
`AlgebraicGeometry.Scheme.strictTowerExchangeMateNormalization`, attached to
`lem-weil-pbc-strict-tower-exchange-mate-normalization`. Its original statement,
source, and full natural-language proof are retained. This is a partial delivery:
the finite-evaluation and strict mate-coherence arguments remain unproved.

## No longer needed

Removed these unused direct proof imports (some remain transitively available):

- `Sheaf.CategoryTheory.DiagramSiteRealization`
- `Mathlib.Algebra.Category.Grp.FilteredColimits`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `Mathlib.CategoryTheory.Sites.Limits`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.Paper.ProEtaleCanonicalTensorPullback`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.PerfectProjectionFormula`
- `Sheaf.Paper.FiniteLevelRectangle`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.CategoryTheory.FlatRingedDiagramRestriction`
- `Sheaf.Paper.AdicCoefficientDatum`
- `Sheaf.Paper.CompletedDirectImageLimits`
- `Sheaf.Paper.FourArrows`
- `Sheaf.Paper.FourCorners`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

No mathematical node or module is withdrawn. The unfinished normalization theorem
still needs its declared proof route. The temporary evaluation and transport
splits were removed from this packet; no new DAG nodes or split holes are delivered.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The normalized direct-image comparison can be proved
on strict functor categories using an exact left adjoint and the existing derived
mate unit API, without introducing a separate diagram-site realization in this proof.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
