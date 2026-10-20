# AlgebraicGeometry.SimplicialAugmentationSpectralSequence import repair

## Reason

Restore the quarantined item listed in coord/rework.tsv after the upstream filtration
migration. The original published DoubleComplexTotal dependency loads the obsolete
Sheaf filtration, which collides with CanonicalFiltration.IsExhaustive. This module uses
no declaration introduced by DoubleComplexTotal: its filtration is supplied explicitly
by the spectral-sequence structure, and its totals use the existing natural-indexed
Mathlib construction. Import CanonicalFiltration directly and make the spectral-sequence
API explicit. No mathematical definition or theorem signature changes.

Also prove simplicial_etale_augmentation_component using the existing bounded-below
derived-composition isomorphism and its unit factorization. It uses the original
simplicial_etale_restriction_exact theorem, rather than a new hypothesis or new hole.
Remove proof imports not used by the retained Lean proof or the unchanged statements.

## Old

```lean
public import Sheaf.AlgebraicGeometry.TotalEtaleAugmentationAdjunction
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Functor.Currying
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.KInjectiveComputes
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
import Sheaf.AlgebraicGeometry.TotalSimplicialEtaleSite
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
```

## New

```lean
public import Sheaf.AlgebraicGeometry.TotalEtaleAugmentationAdjunction
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Functor.Currying
```

The only declaration-body change is the complete proof of
AlgebraicGeometry.simplicial_etale_augmentation_component. All other bodies and every
signature are preserved from the quarantine archive.

## Users

`tools/downstream.py --allow-missing` reports zero current downstream modules.
A source search of lean/ and quarantine/ finds one archived direct consumer:

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.NearbyProperHyperdescent | unclaimed archive; not adapted | Uses this item only as a proof import; no removed declaration is mentioned. Its statement is unchanged. |

No target definition changes its meaning. The item's node attachment and all existing
mathematical proof dependencies are retained; this is an import repair, not a withdrawal.


Validation: the repaired item compiled cleanly on the server (5.1 seconds); its proved
comparison also compiled in a two-module consumer check (8.4 seconds). The sole archived
consumer was compiled in that same dependency-ordered check. It failed on a separate
pre-existing collision between Sheaf.Algebra.Homology.DerivedInternalHom and
WeilConjectures.Algebra.Homology.DerivedInternalHom, before elaborating its declaration.
That consumer mentions no removed double-complex declaration. Its archive is untouched;
this packet does not claim that unrelated quarantine repair or a clean consumer build.

## Status

landed 20261020T162549-L-3624939 2026-10-20 (merge of deliver/Q2/Sheaf.TraceFormula.SimplicialDerivedImageSpectralSequence)
