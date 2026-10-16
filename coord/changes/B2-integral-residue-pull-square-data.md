# residueExchangePullHom and its explicit restriction-square data

## Reason

Move the unchanged explicit data to an importable lower module, so that separately stated proof obligations do not import their parent theorem. Add typed wrappers for the existing reduction and exact-pullback derived counits. These wrappers avoid elaboration repeatedly unfolding a large left-derived-functor construction. No existing declaration changes its name, visibility, signature or defining term; the original module publicly re-exports the data module. Target meanings are unchanged.

## Old

In `Sheaf.Paper.IntegralResiduePullSquare`:

```lean
/-- Exact restriction from residue modules to integral modules on the derived category. -/
noncomputable abbrev residueExchangeRestriction (T : Scheme.{u}) :
    residueExchangeDerived
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T ⥤
      residueExchangeDerived (integralCoeff ℓ E) T :=
  (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory

/-- The canonical restriction/pullback square, obtained by applying the levelwise
comparison and the exact-pullback identifications. Its data are constructed explicitly. -/
@[irreducible] noncomputable def residueExchangeRestrictPullIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeRestriction ℓ E Y ⋙ residueExchangeUpperStar (integralCoeff ℓ E) f ≅
      residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f ⋙
        residueExchangeRestriction ℓ E X := by
  unfold residueExchangeUpperStar
  exact Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (integralCoeff ℓ E) f) ≪≫
    (derivedComapUpperStarIso (integralReductionMap ℓ E) f).symm ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).symm _

/-- The scalar-extension/pullback comparison is constructed as the inverse mate of
exact restriction/pullback. Invertibility is a property, not chosen data. -/
@[irreducible] noncomputable def residueExchangePullHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeUpperStar (integralCoeff ℓ E) f ⋙ residueExchangeReduction ℓ E X ⟶
      residueExchangeReduction ℓ E Y ⋙
        residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f :=
  ((mateEquiv (residueExchangeReductionAdjunction ℓ E Y)
      (residueExchangeReductionAdjunction ℓ E X)).symm
    (TwoSquare.mk _ _ _ _ (residueExchangeRestrictPullIso ℓ E f).hom)).natTrans

/-- The defining counit identity of the constructed scalar pull comparison. -/
theorem residueExchangePullHom_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : residueExchangeDerived
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) Y) :
    (residueExchangeReduction ℓ E X).map
        ((residueExchangeRestrictPullIso ℓ E f).hom.app N) ≫
      (residueExchangeReductionAdjunction ℓ E X).counit.app
        ((residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).obj N) =
    (residueExchangePullHom ℓ E f).app ((residueExchangeRestriction ℓ E Y).obj N) ≫
      (residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
          ((residueExchangeReductionAdjunction ℓ E Y).counit.app N) := by
  unfold residueExchangePullHom
  exact mateEquiv_counit_symm (residueExchangeReductionAdjunction ℓ E Y)
    (residueExchangeReductionAdjunction ℓ E X)
    (TwoSquare.mk _ _ _ _ (residueExchangeRestrictPullIso ℓ E f).hom) N
```

## New

In `Sheaf.Paper.IntegralResiduePullSquareData`, publicly imported by the original module:

```lean
/-- Exact restriction from residue modules to integral modules on the derived category. -/
noncomputable abbrev residueExchangeRestriction (T : Scheme.{u}) :
    residueExchangeDerived
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T ⥤
      residueExchangeDerived (integralCoeff ℓ E) T :=
  (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory

/-- The canonical restriction/pullback square, obtained by applying the levelwise
comparison and the exact-pullback identifications. Its data are constructed explicitly. -/
@[irreducible] noncomputable def residueExchangeRestrictPullIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeRestriction ℓ E Y ⋙ residueExchangeUpperStar (integralCoeff ℓ E) f ≅
      residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f ⋙
        residueExchangeRestriction ℓ E X := by
  unfold residueExchangeUpperStar
  exact Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (integralCoeff ℓ E) f) ≪≫
    (derivedComapUpperStarIso (integralReductionMap ℓ E) f).symm ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).symm _

/-- The scalar-extension/pullback comparison is constructed as the inverse mate of
exact restriction/pullback. Invertibility is a property, not chosen data. -/
@[irreducible] noncomputable def residueExchangePullHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeUpperStar (integralCoeff ℓ E) f ⋙ residueExchangeReduction ℓ E X ⟶
      residueExchangeReduction ℓ E Y ⋙
        residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f :=
  ((mateEquiv (residueExchangeReductionAdjunction ℓ E Y)
      (residueExchangeReductionAdjunction ℓ E X)).symm
    (TwoSquare.mk _ _ _ _ (residueExchangeRestrictPullIso ℓ E f).hom)).natTrans

/-- The defining counit identity of the constructed scalar pull comparison. -/
theorem residueExchangePullHom_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : residueExchangeDerived
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) Y) :
    (residueExchangeReduction ℓ E X).map
        ((residueExchangeRestrictPullIso ℓ E f).hom.app N) ≫
      (residueExchangeReductionAdjunction ℓ E X).counit.app
        ((residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).obj N) =
    (residueExchangePullHom ℓ E f).app ((residueExchangeRestriction ℓ E Y).obj N) ≫
      (residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
          ((residueExchangeReductionAdjunction ℓ E Y).counit.app N) := by
  unfold residueExchangePullHom
  exact mateEquiv_counit_symm (residueExchangeReductionAdjunction ℓ E Y)
    (residueExchangeReductionAdjunction ℓ E X)
    (TwoSquare.mk _ _ _ _ (residueExchangeRestrictPullIso ℓ E f).hom) N


/-- The derived reduction counit with its actual reduction functor exposed. -/
@[irreducible] noncomputable def residueExchangeReductionCounit (T : Scheme.{u}) :
    DerivedCategory.Qh ⋙ residueExchangeReduction ℓ E T ⟶
      (Mod.extendScalars
        (coefficientMap (integralReductionMap ℓ E) T)).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh := by
  unfold residueExchangeReduction integralReduction
  exact (Mod.extendScalars (coefficientMap (integralReductionMap ℓ E) T)).leftDerivedFunctorCounit

/-- The exact pullback counit with its typed derived pullback exposed. -/
@[irreducible] noncomputable def residueExchangeUpperStarCounit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.Qh ⋙ residueExchangeUpperStar Λ f ⟶
      ((f)^*⟦Λ⟧).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh := by
  unfold residueExchangeUpperStar
  exact ((f)^*⟦Λ⟧).leftDerivedFunctorCounit
```

## Users

The table is the union of `tools/downstream.py --uses` for the four moved declaration names. The whole import closure has 14 modules; unchanged public re-export preserves their interface.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.IntegralResiduePullSquare` | B2 | Same names, types and definition bodies through public re-export; no adaptation. |
| `Sheaf.Paper.IntegralResidueTensorGeometry` | A4 | Same names, types and definition bodies through public re-export; no adaptation. |
| `Sheaf.Paper.IntegralResidueTensorPresentation` | unclaimed | Same names, types and definition bodies through public re-export; no adaptation. |
| `Sheaf.Paper.IntegralResidueTensorSquare` | unclaimed | Same names, types and definition bodies through public re-export; no adaptation. |
| `Sheaf.Paper.IntegralResidueProjectionNormalization` | unclaimed | Same names, types and definition bodies through public re-export; no adaptation. |
| `Sheaf.Paper.IntegralResidueScalarRouteModel` | A2 | Same names and types through public re-export; no adaptation. |
| `Sheaf.Paper.IntegralResidueTensorModel` | A4 | Same names and types through public re-export; no adaptation. |
| `Sheaf.Paper.IntegralResidueTensorPullPresentation` | A4 | Same names and types through public re-export; no adaptation. |

## Status

landed 20261016T151821-L-177787 2026-10-16 (merge of deliver/B2/Sheaf.Paper.IntegralResiduePullSquare)
