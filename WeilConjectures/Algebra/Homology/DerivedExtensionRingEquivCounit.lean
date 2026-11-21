/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.DerivedExtensionRingEquivRawCounit
import WeilConjectures.Algebra.Homology.DerivedRestrictionHomologyFactors

/-! # Transporting universal derived counits along coefficient equivalences

## References

* Stacks Project, Tags 06Y6 and 05RR
-/

@[expose] public section
set_option autoImplicit false
universe u w w'
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

/-- Once ordinary scalar extension has been identified, its universal derived
functor and counit transport through coefficient equivalences. -/
theorem exists_derivedExtension_ringEquiv_counit
    {R₀ B₀ R B : Type u}
    [CommRing R₀] [CommRing B₀] [CommRing R] [CommRing B]
    [Algebra R₀ B₀] [Algebra R B]
    [HasDerivedCategory.{w} (ModuleCat.{u} R₀)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B₀)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} B)]
    (L₀ : DerivedCategory (ModuleCat.{u} R₀) ⥤ DerivedCategory (ModuleCat.{u} B₀))
    (L : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε₀ : DerivedCategory.Qh ⋙ L₀ ⟶
      (extendScalars (algebraMap R₀ B₀)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (h₀ : L₀.IsLeftDerivedFunctor ε₀ (HomotopyCategory.quasiIso _ (.up ℤ)))
    (h : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)))
    (eR : R₀ ≃+* R) (eB : B₀ ≃+* B)
    (hRB : eB.toRingHom.comp (algebraMap R₀ B₀) =
      (algebraMap R B).comp eR.toRingHom) (i : ℤ) :
    let π₀ := HomotopyCategory.quotient (ModuleCat.{u} R₀) (.up ℤ)
    let π := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
    let H₀ := DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) i
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
    let P₀ := π₀ ⋙ DerivedCategory.Qh ⋙ L₀ ⋙ H₀
    let P := π ⋙ DerivedCategory.Qh ⋙ L ⋙ H
    let V := (restrictScalars.{u} eR.toRingHom).mapHomologicalComplex (.up ℤ)
    let U := restrictScalars.{u} eB.toRingHom
    let T₀ := (extendScalars (algebraMap R₀ B₀)).mapHomologicalComplex (.up ℤ)
    let T := (extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)
    let c₀ := fun K : CochainComplex (ModuleCat.{u} R₀) ℤ ↦
      H₀.map (ε₀.app (π₀.obj K)) ≫
        (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B₀) i).hom.app
          ((HomotopyCategory.quotient _ _).obj (T₀.obj K)) ≫
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B₀) (.up ℤ) i).hom.app
          (T₀.obj K)
    let c := fun K : CochainComplex (ModuleCat.{u} R) ℤ ↦
      H.map (ε.app (π.obj K)) ≫
        (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.app
          ((HomotopyCategory.quotient _ _).obj (T.obj K)) ≫
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app
          (T.obj K)
    ∀ (t : V ⋙ T₀ ≅ T ⋙ U.mapHomologicalComplex (.up ℤ))
      (_ht : ∀ (K : CochainComplex (ModuleCat.{u} R) ℤ) (j : ℤ) (b : B₀) (x : K.X j),
        (t.hom.app K).f j (b ⊗ₜ[R₀,algebraMap R₀ B₀] x) =
          eB b ⊗ₜ[R,algebraMap R B] x),
      ∃ d : V ⋙ P₀ ≅ P ⋙ U,
        ∀ K : CochainComplex (ModuleCat.{u} R) ℤ,
          d.hom.app K ≫ U.map (c K) =
            c₀ (V.obj K) ≫ HomologicalComplex.homologyMap (t.hom.app K) i ≫
              ((T.obj K).sc i |>.mapHomologyIso U).hom  := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      dsimp only
      intro t _ht
      obtain ⟨E, q, a, ha⟩ := exists_derivedExtension_ringEquiv_raw_counit
        L₀ L ε₀ ε h₀ h eR eB hRB t
      obtain ⟨z, hz⟩ := exists_derivedRestriction_homology_factors eB.toRingHom E i q
      let H₀ := DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) i
      let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
      let U := restrictScalars.{u} eB.toRingHom
      let J := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh ⋙ L
      let d := Functor.isoWhiskerRight a H₀ ≪≫ Functor.isoWhiskerLeft J z
      refine ⟨d, ?_⟩
      intro K
      let π := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
      let π₀ := HomotopyCategory.quotient (ModuleCat.{u} R₀) (.up ℤ)
      let V := (restrictScalars.{u} eR.toRingHom).mapHomologicalComplex (.up ℤ)
      let T := (extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)
      let T₀ := (extendScalars (algebraMap R₀ B₀)).mapHomologicalComplex (.up ℤ)
      let S₀ := HomotopyCategory.quotient (ModuleCat.{u} B₀) (.up ℤ) ⋙ DerivedCategory.Qh
      let F₀ := Functor.isoWhiskerLeft (HomotopyCategory.quotient _ (.up ℤ))
        (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B₀) i) ≪≫
        HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B₀) (.up ℤ) i
      let F := Functor.isoWhiskerLeft (HomotopyCategory.quotient _ (.up ℤ))
        (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i) ≪≫
        HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i
      change (H₀.map (a.hom.app K) ≫ z.hom.app (J.obj K)) ≫
          U.map (H.map (ε.app (π.obj K)) ≫ F.hom.app (T.obj K)) =
        (H₀.map (ε₀.app (π₀.obj (V.obj K))) ≫ F₀.hom.app (T₀.obj (V.obj K))) ≫
          HomologicalComplex.homologyMap (t.hom.app K) i ≫
            (((T.obj K).sc i).mapHomologyIso U).hom
      rw [Functor.map_comp]
      simp only [Category.assoc]
      have hn := z.hom.naturality (ε.app (π.obj K))
      change H₀.map (E.map (ε.app (π.obj K))) ≫ z.hom.app _ =
        z.hom.app (J.obj K) ≫ U.map (H.map (ε.app (π.obj K))) at hn
      rw [← reassoc_of% hn]
      erw [hz (T.obj K)]
      have hh := congrArg H₀.map (ha K)
      simp only [Functor.map_comp] at hh
      erw [reassoc_of% hh]
      have hf := F₀.hom.naturality (t.hom.app K)
      change H₀.map (S₀.map (t.hom.app K)) ≫ F₀.hom.app _ =
        F₀.hom.app (T₀.obj (V.obj K)) ≫ HomologicalComplex.homologyMap (t.hom.app K) i at hf
      erw [reassoc_of% hf]

end ModuleCat
