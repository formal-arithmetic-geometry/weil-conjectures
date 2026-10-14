module
public import Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeCanonical
import Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeComponent
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
/-- Compatibility of the affine sheaf edge with the right-derived unit.
Source: Stacks Project, Tags 0AVW and 08D4.
(blueprint: lem-pc-affine-derived-pushforward-sheaf-edge-compatibility). -/
theorem affineDerivedPushforwardSheafEdge_compatibility
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ) :
    ∀ (F : ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      [F.Additive] [F.PreservesZeroMorphisms] [F.PreservesHomology]
      [(F ⋙ RingedSpace.moduleDirectImage
        (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesZeroMorphisms]
      [(F ⋙ RingedSpace.moduleDirectImage
        (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesHomology]
      (_hF : ∀ M, (F.obj M).IsQuasicoherent)
      (C : CochainComplex (ModuleCat.{u} A) ℤ)
      (hC : schemeDerivedQCohProperty (Spec (.of A))
        (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj C))),
      (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).map
          (((C.sc i).mapHomologyIso F).inv ≫
            ((DerivedCategory.homologyFunctorFactors _ i).app
              ((F.mapHomologicalComplex (.up ℤ)).obj C)).inv) ≫
        (affineDerivedPushforwardSheafEdge_canonical A B φ i).app ⟨_, hC⟩ =
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
  intro F _ _ _ _ _ hF C hC
  exact affineDerivedPushforwardSheafEdge_component A B φ i F hF C hC
end AlgebraicGeometry
