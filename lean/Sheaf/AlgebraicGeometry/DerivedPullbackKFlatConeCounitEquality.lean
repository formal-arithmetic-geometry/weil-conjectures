module

public import Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitData

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- Cone connecting-map normalization for fixed K-flat counit data.

Source: Stacks Project, Tag 06YJ, Lemma 20.27.1, translated-unit
normalization. For a map of K-flat complexes, termwise pullback commutes with
its mapping cone, and tensorator naturality identifies the resulting
projection with the displayed shifted-unit composite.
(blueprint: lem-sc-derived-pullback-kflat-cone-counit-equality).
-/
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
                  (ε.app C.obj₁)⟦(1 : ℤ)⟧' := by
  sorry

end AlgebraicGeometry
