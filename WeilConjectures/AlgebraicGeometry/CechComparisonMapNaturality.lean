/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
import WeilConjectures.AlgebraicGeometry.ModuleCechLiftSquares

/-!
# Naturality of the canonical Cech-to-cohomology comparison map

Source: Stacks Project, Cohomology of Sheaves, Lemma Tag 01EQ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Transport a comparison equation along a lift between resolutions. -/
private theorem comparison_transport {X : Scheme.{u}} [EnoughInjectives X.Modules]
    [(RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive]
    {ι : Type u} (U : ι → X.Opens) (p : ℕ) {F G : X.Modules} (φ : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (c : ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
    (hc : c ≫ (I.isoRightDerivedObj
        (RingedSpace.globalSectionsFunctor X.toRingedSpace) p).hom ≫
      HomologicalComplex.homologyMap (moduleCechAlpha U I) p =
        HomologicalComplex.homologyMap (moduleCechBeta U I) p) :
    HomologicalComplex.homologyMap ((CategoryTheory.cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          φ.val)) p ≫ HomologicalComplex.homologyMap (moduleCechBeta U J) p =
      c ≫ (RingedSpace.moduleCohomology X.toRingedSpace p).map φ ≫
        (J.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) p).hom ≫
          HomologicalComplex.homologyMap (moduleCechAlpha U J) p := by
  let ψ := InjectiveResolution.desc φ J I
  have hψ := InjectiveResolution.desc_commutes_zero φ J I
  obtain ⟨hα, hβ⟩ := moduleCechLiftSquares U φ I J ψ hψ
  have ha := congrArg (fun f => HomologicalComplex.homologyMap f p) hα
  have hb := congrArg (fun f => HomologicalComplex.homologyMap f p) hβ
  simp only [HomologicalComplex.homologyMap_comp] at ha hb
  have hd := InjectiveResolution.isoRightDerivedObj_hom_naturality
    φ I J ψ hψ (RingedSpace.globalSectionsFunctor X.toRingedSpace) p
  change (RingedSpace.moduleCohomology X.toRingedSpace p).map φ ≫ _ =
    _ ≫ HomologicalComplex.homologyMap
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ)).map ψ) p at hd
  rw [← hb, ← hc]
  simp only [Category.assoc]
  rw [ha, ← Category.assoc _ _ (HomologicalComplex.homologyMap (moduleCechAlpha U J) p),
    ← hd]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical Cech-to-cohomology comparison exists, is independent of the resolution,
and is natural in the coefficient module (Stacks, Tag 01EQ). -/
theorem cechComparisonMapNaturality (X : Scheme.{u}) {ι : Type u}
    (U : ι → X.Opens) (hcover : iSup U = ⊤) :
    (∀ (F : X.Modules) (I : InjectiveResolution F), QuasiIso (moduleCechAlpha U I)) ∧
    ∀ p : ℕ, (∀ F : X.Modules, ∃ c :
        ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
          (RingedSpace.moduleCohomology X.toRingedSpace p).obj F,
        IsModuleCechComparison U F p c) ∧
      (∀ (F G : X.Modules) (φ : F ⟶ G)
        (cF : ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
          (RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
        (cG : ((CategoryTheory.cechComplexFunctor U).obj G.presheafModuleCat).homology p ⟶
          (RingedSpace.moduleCohomology X.toRingedSpace p).obj G),
        IsModuleCechComparison U F p cF → IsModuleCechComparison U G p cG →
        HomologicalComplex.homologyMap ((CategoryTheory.cechComplexFunctor U).map
            ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
              φ.val)) p ≫ cG =
          cF ≫ (RingedSpace.moduleCohomology X.toRingedSpace p).map φ) := by
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : (RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive :=
    RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  constructor
  · intro F I
    rw [quasiIso_iff]
    intro p
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).2
      (moduleCechAlpha_isIso U hcover I p)
  · intro p
    constructor
    · intro F
      let I := injectiveResolution F
      let e := I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) p
      let a := HomologicalComplex.homologyMap (moduleCechAlpha U I) p
      let b := HomologicalComplex.homologyMap (moduleCechBeta U I) p
      have : IsIso a := moduleCechAlpha_isIso U hcover I p
      let c := b ≫ inv a ≫ e.inv
      have hc : c ≫ e.hom ≫ a = b := by simp [c]
      refine ⟨c, ?_⟩
      intro J
      have ht := comparison_transport U p (𝟙 F) I J c hc
      have hid : (PresheafOfModules.forgetToPresheafModuleCat
          (op ⊤) isTerminalTop.op).map (𝟙 F : F ⟶ F).val = 𝟙 F.presheafModuleCat := by
        change (PresheafOfModules.forgetToPresheafModuleCat
          (op ⊤) isTerminalTop.op).map (𝟙 F.val) = _
        exact CategoryTheory.Functor.map_id _ _
      rw [hid] at ht
      have hi := (CategoryTheory.cechComplexFunctor U).map_id F.presheafModuleCat
      rw [hi] at ht
      erw [HomologicalComplex.homologyMap_id] at ht
      simpa only [CategoryTheory.Functor.map_id,
        Category.id_comp, Category.comp_id] using ht.symm
    · intro F G φ cF cG hcF hcG
      let I := injectiveResolution F
      let J := injectiveResolution G
      let e := J.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) p
      let a := HomologicalComplex.homologyMap (moduleCechAlpha U J) p
      have : IsIso a := moduleCechAlpha_isIso U hcover J p
      apply (cancel_mono (e.hom ≫ a)).1
      have ht := comparison_transport U p φ I J cF (hcF I)
      change _ ≫ cG ≫ e.hom ≫ a = _
      change _ ≫ cG ≫ (J.isoRightDerivedObj
        (RingedSpace.globalSectionsFunctor X.toRingedSpace) p).hom ≫
          HomologicalComplex.homologyMap (moduleCechAlpha U J) p = _
      rw [hcG J]
      exact ht

end AlgebraicGeometry.Scheme.Modules
