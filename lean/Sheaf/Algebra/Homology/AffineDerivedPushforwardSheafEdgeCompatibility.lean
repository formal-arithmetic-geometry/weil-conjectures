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
/-- Compatibility of a cycle-normalized affine sheaf edge with the right-derived unit.
Source: Stacks Project, Tags 0AVW and 08D4.
(blueprint: lem-pc-affine-derived-pushforward-sheaf-edge-compatibility).

Proof: Apply the cycle normalization to the homology data of C mapped by F and
by F followed by direct image. Their cycle objects and inclusions agree, so the
cycle comparison is the identity. Their quotient maps agree after direct image.
The latter quotient map is an epimorphism because the composite exact functor
preserves cokernels. Cancel it to obtain the asserted cohomology equality.
An arbitrary natural transformation need not be normalized; the normalization
hypothesis is essential, and does not assert existence of a normalized edge. -/
theorem affineDerivedPushforwardSheafEdge_compatibility
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ) :
  (ε : (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i ⋙
      RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom ⟶
    (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i) →
    (∀ (K : CochainComplex
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
      (hK : schemeDerivedQCohProperty (Spec (.of A)) (DerivedCategory.Q.obj K))
      (T : (K.sc i).LeftHomologyData)
      (U : ((((RingedSpace.moduleDirectImage
        (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).mapHomologicalComplex
          (.up ℤ)).obj K).sc i).LeftHomologyData)
      (k : (RingedSpace.moduleDirectImage
        (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).obj T.K ⟶ U.K),
      (RingedSpace.moduleDirectImage
        (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).map T.i = k ≫ U.i →
      (RingedSpace.moduleDirectImage
        (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).map
        (T.π ≫ T.homologyIso.inv ≫
          ((DerivedCategory.homologyFunctorFactors _ i).app K).inv) ≫ ε.app ⟨_, hK⟩ =
      k ≫ U.π ≫ U.homologyIso.inv ≫
        ((DerivedCategory.homologyFunctorFactors _ i).app
          (((RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).mapHomologicalComplex
              (.up ℤ)).obj K)).inv ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map
          (((RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).rightDerivedFunctorUnit).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) →
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
  intro ε hε F _ _ _ _ _ hF C hC
  let P := RingedSpace.moduleDirectImage
    (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom
  let K := (F.mapHomologicalComplex (.up ℤ)).obj C
  let T := (C.sc i).homologyData.left.map F
  let U := (C.sc i).homologyData.left.map (F ⋙ P)
  have hn := hε K hC T U (𝟙 _) (by simp [T, U, P])
  simp only [Category.id_comp] at hn
  have hepi : Epi ((F ⋙ P).map (C.sc i).homologyData.left.π) := by
    change Epi U.π
    infer_instance
  simp only [Functor.map_comp, Category.assoc] at hn
  apply (cancel_epi ((F ⋙ P).map (C.sc i).homologyData.left.π)).mp
  simpa only [P, T, U, K, ShortComplex.LeftHomologyData.map_π,
    ShortComplex.mapHomologyIso, Functor.comp_map, Functor.map_comp, Category.assoc,
    Functor.mapHomologicalComplex, Functor.comp_obj] using hn
end AlgebraicGeometry
