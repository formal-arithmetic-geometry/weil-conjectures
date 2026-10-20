module

public import Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitData

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- Cone connecting-map normalization for fixed K-flat counit data.

Source: Stacks Project, Tag 06YJ, Lemma 20.27.1, translated-unit
normalization. Assume the explicit shift square for the supplied e and ε.
Apply naturality of ε to the third arrow of the homotopy cone triangle,
then compose with the target shift comparison. Substitute the shift square
at the first object and expand the localization functor on triangles.
Functoriality of composition and associativity give the displayed equality.
The K-flat assumptions are retained for the existing interface, although this
categorical implication does not use them.
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
      CochainComplex.IsKFlatTensor (R := Y.sheaf) P →
      CochainComplex.IsKFlatTensor (R := Y.sheaf) Q →
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
  intro P Q p _ _
  let C := CochainComplex.mappingCone.triangleh p
  let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    (DerivedCategory.Qh : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
      schemeDerivedCategory Z)
  have hn := ε.naturality C.mor₃
  have hs := hε C.obj₁
  let a := ((derivedPullback f).mapIso
      (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj C.obj₁)).symm ≪≫
    asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
      ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj C.obj₁)) ≪≫
    tensorIso e (Iso.refl _) ≪≫
    schemeCanonicalShiftUnitIso Z ((derivedPullback f).obj (DerivedCategory.Qh.obj C.obj₁)))
  change ε.app (C.obj₁⟦(1 : ℤ)⟧) ≫ (G.commShiftIso (1 : ℤ)).hom.app C.obj₁ =
    (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app C.obj₁) ≫
      a.hom ≫ (ε.app C.obj₁)⟦(1 : ℤ)⟧' at hs
  change ε.app C.obj₃ ≫
    (G.map C.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app C.obj₁) =
    (derivedPullback f).map (DerivedCategory.Qh.map C.mor₃ ≫
      (DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app C.obj₁) ≫
      a.hom ≫ (ε.app C.obj₁)⟦(1 : ℤ)⟧'
  rw [← Category.assoc, ← hn, Category.assoc, hs, Functor.map_comp]
  simp only [Functor.comp_map, Category.assoc]

end AlgebraicGeometry
