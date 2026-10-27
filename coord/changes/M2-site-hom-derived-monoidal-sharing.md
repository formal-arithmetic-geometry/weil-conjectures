# AlgebraicGeometry.ProEtale.siteHomExactDerivedMonoidal

## Reason

Kernel checking of concrete derived closed-comparison applications repeatedly unfolds the
same transported monoidal structure. Share that exact construction as the irreducible
`CategoryTheory.Functor.exactClosedDerivedMonoidal`, with a generic proved comparison API.
The old and new bodies are definitionally equal; no mathematical object or target meaning
changes. The new public helper is under Sheaf, and no source-library file changes.

## Old

```lean
@[irreducible] def siteHomExactDerivedMonoidal
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type e} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D]
    [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal] :
    F.mapDerivedCategory.Monoidal :=
  let _ : F.leftDerivedFunctor.Monoidal := F.residueDerivedMonoidal
  Functor.Monoidal.transport F.leftDerivedFunctorIsoMapDerivedCategory
```

## New

```lean
@[irreducible] def siteHomExactDerivedMonoidal
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type e} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D]
    [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal] :
    F.mapDerivedCategory.Monoidal :=
  Functor.exactClosedDerivedMonoidal F
```

The two restriction evaluation definitions additionally share their existing canonical
component through the new irreducible `Functor.closedComparison`.

### Evaluation definitions, old

```lean
@[irreducible] def siteHomEtaleRestrictionEvaluation
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    (m : (Etale.upperStar B f).mapDerivedCategory.Monoidal)
    (K M : DerivedCategory (Sheaf (X.smallEtaleTopology) B)) :
    (Etale.upperStar B f).mapDerivedCategory.obj
        (((Etale.derivedHom B X).obj (op K)).obj M) ⟶
      ((Etale.derivedHom B Y).obj
        (op ((Etale.upperStar B f).mapDerivedCategory.obj K))).obj
          ((Etale.upperStar B f).mapDerivedCategory.obj M) :=
  let F := (Etale.upperStar B f).mapDerivedCategory
  let _ : F.Monoidal := m
  (Functor.LaxMonoidal.ihomComparison F K).natTrans.app M

@[irreducible] def siteHomProEtaleRestrictionEvaluation
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    (m : (upperStar B f).mapDerivedCategory.Monoidal)
    (K M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B)) :
    (upperStar B f).mapDerivedCategory.obj
        (((derivedHom B X).obj (op K)).obj M) ⟶
      ((derivedHom B Y).obj
        (op ((upperStar B f).mapDerivedCategory.obj K))).obj
          ((upperStar B f).mapDerivedCategory.obj M) :=
  let F := (upperStar B f).mapDerivedCategory
  let _ : F.Monoidal := m
  (Functor.LaxMonoidal.ihomComparison F K).natTrans.app M
```

### Evaluation definitions, new

```lean
@[irreducible] def siteHomEtaleRestrictionEvaluation
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    (m : (Etale.upperStar B f).mapDerivedCategory.Monoidal)
    (K M : DerivedCategory (Sheaf (X.smallEtaleTopology) B)) :
    (Etale.upperStar B f).mapDerivedCategory.obj
        (((Etale.derivedHom B X).obj (op K)).obj M) ⟶
      ((Etale.derivedHom B Y).obj
        (op ((Etale.upperStar B f).mapDerivedCategory.obj K))).obj
          ((Etale.upperStar B f).mapDerivedCategory.obj M) :=
  let F := (Etale.upperStar B f).mapDerivedCategory
  let _ : F.Monoidal := m
  Functor.closedComparison F K M

@[irreducible] def siteHomProEtaleRestrictionEvaluation
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    (m : (upperStar B f).mapDerivedCategory.Monoidal)
    (K M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B)) :
    (upperStar B f).mapDerivedCategory.obj
        (((derivedHom B X).obj (op K)).obj M) ⟶
      ((derivedHom B Y).obj
        (op ((upperStar B f).mapDerivedCategory.obj K))).obj
          ((upperStar B f).mapDerivedCategory.obj M) :=
  let F := (upperStar B f).mapDerivedCategory
  let _ : F.Monoidal := m
  Functor.closedComparison F K M
```

The helper's body is exactly the old expression. These changes preserve the actual
transpose, not only its isomorphism class. All full signatures, attributes and docstrings
are retained. The proof uses the same global sheaf tensor instances as the native source
library; duplicate local tensor instances are unnecessary.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SiteHomComparisonThick | M2 | Same structure; proofs use its shared generic API. |
| Sheaf.Paper.LisseFlatHomSiteComparison | unclaimed | Only downstream importer; does not name this definition. No adaptation. |

The same consumer searches for `siteHomEtaleRestrictionEvaluation` and
`siteHomProEtaleRestrictionEvaluation` each reported only the item as a direct user and
the same single downstream module. No target statement changes meaning.

The consumer search was `python3 tools/downstream.py
Sheaf.AlgebraicGeometry.SiteHomComparisonThick --uses siteHomExactDerivedMonoidal`.
It reported only the item itself as a direct declaration user and the one downstream module
listed above. All existing signatures, visibility and attributes are retained.

## Status

landed 20261025T002522-L-3122912 2026-10-25 (merge of deliver/M2/Sheaf.AlgebraicGeometry.SiteHomComparisonThick)
