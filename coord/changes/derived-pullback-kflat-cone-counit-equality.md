# AlgebraicGeometry.derivedPullback_kFlat_cone_counit_eq

## Reason

Reviewer X-4de8e E1/E2 requires correction at the actual theorem declaration.
The original theorem quantifies over independent arbitrary e and epsilon.
For identity pullback on Spec Q, P the unit and Q=0, the cone projection is
nonzero. Negating e leaves the left side unchanged and negates the right side.
The unrestricted theorem is false. Add the explicit shift square for all
homotopy objects and prove the conditional cone equality by naturality.

No compatible-data existence theorem is added: the prior proposal lacked a
valid construction. The caller's old proof is invalidated by this correction.
Reopen its existing named normalization theorem, preserving its signature and
visibility, rather than claiming that K-flat invertibility implies compatibility.
This is a correction, not net progress in the sorry ledger. No target statement
or definition changes. The unchanged normalization statement shields all 346
transitive importers from any signature change.

## Old

```lean
theorem derivedPullback_kFlat_cone_counit_eq
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    (ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
          (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            (DerivedCategory.Qh : HomotopyCategory
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
              schemeDerivedCategory Z)) :
    ∀ (P Q : CochainComplex
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) (p : P ⟶ Q),
      CochainComplex.IsKFlat (R := Y.sheaf) P →
      CochainComplex.IsKFlat (R := Y.sheaf) Q →
      let C := CochainComplex.mappingCone.triangleh p
      let T := (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Y).mapTriangle.obj C
      let W := ((Scheme.Modules.tensorPullback f).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).mapTriangle.obj C
      ε.app C.obj₃ ≫ W.mor₃ =
        (derivedPullback f).map T.mor₃ ≫
              ((derivedPullback f).mapIso (schemeCanonicalShiftUnitIso Y T.obj₁).symm ≪≫
                asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                  ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) T.obj₁) ≪≫
                tensorIso e (Iso.refl _) ≪≫
                schemeCanonicalShiftUnitIso Z ((derivedPullback f).obj T.obj₁)).hom ≫
                  (ε.app C.obj₁)⟦(1 : ℤ)⟧'
```

## New

```lean
theorem derivedPullback_kFlat_cone_counit_eq
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    (ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
          (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            (DerivedCategory.Qh : HomotopyCategory
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
              schemeDerivedCategory Z))
    (hε :
      ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        ε.app (X⟦(1 : ℤ)⟧) ≫ (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (ε.app X)⟦(1 : ℤ)⟧') :
    ∀ (P Q : CochainComplex
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) (p : P ⟶ Q),
      CochainComplex.IsKFlat (R := Y.sheaf) P →
      CochainComplex.IsKFlat (R := Y.sheaf) Q →
      let C := CochainComplex.mappingCone.triangleh p
      let T := (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Y).mapTriangle.obj C
      let W := ((Scheme.Modules.tensorPullback f).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).mapTriangle.obj C
      ε.app C.obj₃ ≫ W.mor₃ =
        (derivedPullback f).map T.mor₃ ≫
              ((derivedPullback f).mapIso (schemeCanonicalShiftUnitIso Y T.obj₁).symm ≪≫
                asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                  ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) T.obj₁) ≪≫
                tensorIso e (Iso.refl _) ≪≫
                schemeCanonicalShiftUnitIso Z ((derivedPullback f).obj T.obj₁)).hom ≫
                  (ε.app C.obj₁)⟦(1 : ℤ)⟧'
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatConeCounitEquality | D2 | Add explicit shift hypothesis and complete its categorical proof. |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatConeCounitNormalization | unclaimed | Original proof no longer typechecks. Replace only its three-line proof with the existing named theorem's whole-proof sorry; preserve all imports, signatures, visibility, and docstrings. |

The downstream declaration-use scan lists exactly these two modules. The
normalization node's use is marked holds:false in statement_change. Its
construction for an arbitrary supplied monoidal structure remains unresolved;
its existing proof docstring is the prior plan, not a newly verified construction.
The exact original compiler failure is recorded in report.md. No module held
by another group is otherwise adapted. The unit's realized entries are unchanged.

## Status

landed 20261013T234505-L-2160616 2026-10-13 (merge of deliver/D2/Sheaf.AlgebraicGeometry.DerivedPullbackKFlatConeCounitEquality)
