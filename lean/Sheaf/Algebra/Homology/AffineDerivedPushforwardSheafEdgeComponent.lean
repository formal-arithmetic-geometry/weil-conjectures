module
public import Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeCanonical
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafReverseUnit
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
  let P := RingedSpace.moduleDirectImage
    (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom
  let D := (F.mapHomologicalComplex (.up ℤ)).obj C
  let τ := affineDerivedPushforwardSheafReverseIso A B φ i
  let a := (C.sc i).mapHomologyIso F
  let b := (DerivedCategory.homologyFunctorFactors _ i).app D
  let c := (C.sc i).mapHomologyIso (F ⋙ P)
  let d := (DerivedCategory.homologyFunctorFactors _ i).app
    ((P.mapHomologicalComplex (.up ℤ)).obj D)
  let u := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map
    (P.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj D))
  change P.map (a.inv ≫ b.inv) ≫ τ.inv.app ⟨_, hC⟩ = c.inv ≫ d.inv ≫ u
  have hu := affineDerivedPushforwardSheafReverse_unit A B φ i D hC
  change u ≫ τ.hom.app ⟨_, hC⟩ =
    d.hom ≫ (D.sc i).leftExactHomologyComparison P ≫ P.map b.inv at hu
  have hc := (C.sc i).leftExactHomologyComparison_map F P
  change c.inv ≫ (D.sc i).leftExactHomologyComparison P = P.map a.inv at hc
  apply (cancel_mono (τ.hom.app ⟨_, hC⟩)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [hu]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hc, ← P.map_comp]
  exact Category.comp_id _
end AlgebraicGeometry
