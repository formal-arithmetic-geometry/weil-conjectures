# SheafOfModules.finiteFreeStrictTowerTransport

## Reason

Stage-3 preflight requests a record for the additional proof elaboration commands in
`Sheaf.CategoryTheory.FiniteFreeStrictTowerTransport`. The added transparency options
support comparisons between the cochain and localized functors without expensive unfolding.
The additional `open` commands resolve triangle and monoidal names in the private proofs.
They affect elaboration within this file. They do not install notation, exported instances,
or attributes on existing declarations for importers.

Every existing public declaration signature, non-theorem body, visibility, and public import
is preserved. The original universe declaration is also preserved. All added helper declarations
and proof imports are private. The only public theorem body changed is the assigned proof.
No adopted source-library module is edited, no target meaning changes, and no target statement
review is reopened.

## Old

The original public theorem signature, verbatim:

```lean
theorem finiteFreeStrictTowerTransport
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {O S : Sheaf J CommRingCat.{r}} (a : O ⟶ S)
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J O))]
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J O))]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    (D : DerivedChangeOfRingsCochainModel.{u, v, r, w, w} a)
    (hfree : ∃ d : ℕ, Nonempty
      (free (R := derivedChangeRingIndependentCoefficients J O) (ULift.{r} (Fin d)) ≅
        (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
          (unit (derivedChangeRingIndependentCoefficients J S)))) :
    ∃ (_ : PreservesFiniteLimits D.E) (_ : PreservesFiniteColimits D.E)
      (_ : PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) D.E))
      (_ : PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) D.E))
      (_ : HasCountableProducts (DerivedCategory.{w} (ringedSiteModules.{r}
        (derivedChangeRingIndependentCoefficients J O))))
      (_ : HasCountableProducts (DerivedCategory.{w} (ringedSiteModules.{r}
        (derivedChangeRingIndependentCoefficients J S))))
      (κ : D.T ≅ D.E.mapDerivedCategory),
      (∀ M, D.ε.app M = κ.hom.app (DerivedCategory.Q.obj M) ≫
        D.E.mapDerivedCategoryFactors.hom.app M) ∧
      (∀ M : ℕ → DerivedCategory.{w} (ringedSiteModules.{r}
        (derivedChangeRingIndependentCoefficients J O)), IsIso (piComparison D.T M)) ∧
      Nonempty (FiniteFreeStrictTowerTransport D.E D.E.mapDerivedCategory
        (projectionPost (I := ℕᵒᵖ) D.E).mapDerivedCategory
        D.E.mapDerivedCategoryFactors
        (projectionPost (I := ℕᵒᵖ) D.E).mapDerivedCategoryFactors)
```

Original file elaboration context:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v r w uA vA uB vB
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules
```

There was no `open CategoryTheory.MonoidalCategory` command in the module.

## New

The public theorem signature remains identical, verbatim:

```lean
theorem finiteFreeStrictTowerTransport
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {O S : Sheaf J CommRingCat.{r}} (a : O ⟶ S)
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J O))]
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J O))]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    (D : DerivedChangeOfRingsCochainModel.{u, v, r, w, w} a)
    (hfree : ∃ d : ℕ, Nonempty
      (free (R := derivedChangeRingIndependentCoefficients J O) (ULift.{r} (Fin d)) ≅
        (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
          (unit (derivedChangeRingIndependentCoefficients J S)))) :
    ∃ (_ : PreservesFiniteLimits D.E) (_ : PreservesFiniteColimits D.E)
      (_ : PreservesFiniteLimits (projectionPost (I := ℕᵒᵖ) D.E))
      (_ : PreservesFiniteColimits (projectionPost (I := ℕᵒᵖ) D.E))
      (_ : HasCountableProducts (DerivedCategory.{w} (ringedSiteModules.{r}
        (derivedChangeRingIndependentCoefficients J O))))
      (_ : HasCountableProducts (DerivedCategory.{w} (ringedSiteModules.{r}
        (derivedChangeRingIndependentCoefficients J S))))
      (κ : D.T ≅ D.E.mapDerivedCategory),
      (∀ M, D.ε.app M = κ.hom.app (DerivedCategory.Q.obj M) ≫
        D.E.mapDerivedCategoryFactors.hom.app M) ∧
      (∀ M : ℕ → DerivedCategory.{w} (ringedSiteModules.{r}
        (derivedChangeRingIndependentCoefficients J O)), IsIso (piComparison D.T M)) ∧
      Nonempty (FiniteFreeStrictTowerTransport D.E D.E.mapDerivedCategory
        (projectionPost (I := ℕᵒᵖ) D.E).mapDerivedCategory
        D.E.mapDerivedCategoryFactors
        (projectionPost (I := ℕᵒᵖ) D.E).mapDerivedCategoryFactors)
```

The file elaboration context is now:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v r w uA vA uB vB
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open SheafOfModules
```

Inside `namespace SheafOfModules`, the private tensor and scalar-coordinate development adds
`open CategoryTheory.MonoidalCategory`, with a further theorem-local
`open CategoryTheory.MonoidalCategory in` command. These commands introduce no declarations.
There are no added global instance, simp, notation, or declaration-attribute commands.

The proof constructs sectionwise finite coordinates by tensor cancellation, localizes the
exact scalar adjunction, and compares the actual Roos SES boundaries by mapping cones.
The triangulated five lemma proves that the unit-normalized limit comparison is invertible.
It proves all original augmentation and naturality equations. No public definition is repaired
or replaced, and no consumer needs adaptation.

The full proof compiled without warnings through `lcompile.py`; its axiom check lists only
`propext`, `Classical.choice`, and `Quot.sound`.

## Users

`tools/downstream.py Sheaf.CategoryTheory.FiniteFreeStrictTowerTransport --uses
finiteFreeStrictTowerTransport` lists the two downstream modules below and finds the theorem's
textual use in the completion module and the item itself. The table records current claim
holders. Neither consumer is edited. Their statements and the definitions they use keep the
same meaning because the complete public interface and all public non-theorem bodies are
unchanged. There are no forced adaptations.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.CategoryTheory.FiniteFreeStrictTowerTransport` | M4 | Assigned theorem proved; original public signatures and definitions unchanged. |
| `Sheaf.CategoryTheory.FiniteFreeCompletionTransport` | unclaimed | Direct theorem user; same existential result and normalization fields; no adaptation. |
| `Sheaf.Paper.RationalRealizationScalarCoherence` | G7 | Transitive consumer; no interface, statement, or definition change; no adaptation. |

## Status

landed 20261021T214834-L-1866285 2026-10-21 (merge of deliver/M4/Sheaf.CategoryTheory.FiniteFreeStrictTowerTransport)
