# etaleTensorPositiveDirectImageVanishing imports

## Reason

The reduction now calls an affine object-cohomology lemma and a proved generic
local-vanishing criterion. Move localization and affine-acyclicity proof imports
to the affine lemma. Remove the old sheafified-presheaf theorem import: the generic
criterion proves this step directly from the existing resolution comparison.
SheafCohomology.Basic is needed only by proof dependencies, so it is no longer
publicly imported here. Import GrothendieckCategory.HasExt privately to supply
the small Ext instance used by the proof; it was previously imported transitively.
Every existing declaration signature and visibility is unchanged.

## Old

```lean
public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB
import Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization
import Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyNatural
import Sheaf.AlgebraicGeometry.EtaleULiftInjectiveResolution
import Sheaf.AlgebraicGeometry.EtaleAffineQcoherent
import Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf
import Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift
import Sheaf.AlgebraicGeometry.EtaleTensorSections
```

## New

```lean
public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Sheaf.AlgebraicGeometry.EtaleTensorPositiveObjectCohomology
import Sheaf.AlgebraicGeometry.PositiveDirectImageOfObjectAcyclic
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleZariskiAbelianPositiveComparison | unclaimed in local snapshot | No statement or definition changes. This sole direct importer already publicly imports SheafCohomology.Basic and all retained instance dependencies itself. Its original compiles against the delivered overlay. |

`tools/downstream.py` reports 138 transitive downstream modules and only this
external user of the theorem. Since the sole direct importer already exports
SheafCohomology.Basic itself, removing that re-export from its private proof
import does not affect the public imports seen farther downstream. No forced
adaptations or target statement reviews are needed: no definition changed.

## Status

landed 20261012T225336-L-1815156 2026-10-12 (merge of deliver/V3/Sheaf.AlgebraicGeometry.EtaleTensorPositiveDirectImageVanishing)
