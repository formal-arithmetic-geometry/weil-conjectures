module
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Abelian
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
/-- Fixed-component form of the affine derived pushforward edge compatibility.
The proof compares a K-injective resolution after applying `F` and after termwise
pushforward; exactness identifies both cycle classes, and the naturality square
for the resolution identifies the comparison with the right-derived unit.
Source: Stacks Project, Tags 0AVW and 08D4.
(blueprint: lem-pc-affine-derived-pushforward-sheaf-edge-compatibility-component). -/
theorem affineDerivedPushforwardSheafEdge_component
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (ε : (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i ⋙
      RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom ⟶
    (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i)
    (F : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
    [F.Additive] [F.PreservesZeroMorphisms] [F.PreservesHomology]
    [(F ⋙ RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesZeroMorphisms]
    [(F ⋙ RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesHomology]
    (_hF : ∀ M, (F.obj M).IsQuasicoherent)
    (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (hC : schemeDerivedQCohProperty (Spec (.of A))
      (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj C))) :
      (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).map
          (((C.sc i).mapHomologyIso F).inv ≫
            ((DerivedCategory.homologyFunctorFactors _ i).app
              ((F.mapHomologicalComplex (.up ℤ)).obj C)).inv) ≫
        ε.app ⟨_, hC⟩ =
      ((C.sc i).mapHomologyIso
        (F ⋙ RingedSpace.moduleDirectImage
          (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)).inv ≫
        ((DerivedCategory.homologyFunctorFactors _ i).app
          (((F ⋙ RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)
              |>.mapHomologicalComplex (.up ℤ)).obj C)).inv ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map
          (((RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).rightDerivedFunctorUnit).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj
              ((F.mapHomologicalComplex (.up ℤ)).obj C))) := by
  sorry
end AlgebraicGeometry
