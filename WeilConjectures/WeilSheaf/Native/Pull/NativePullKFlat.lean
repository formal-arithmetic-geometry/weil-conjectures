/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.KFlatEquivalence
public import WeilConjectures.AlgebraicGeometry.Native.NativeScalarRestrictionComparison
public import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgettingMonoidal
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting

/-! # Pullback of `ℓ`-adic sheaves preserves K-flat complexes -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalCategory D]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  [(curriedTensor D).Additive] [∀ (X₁ : D), ((curriedTensor D).obj X₁).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (G : C ⥤ D) [G.Additive] [G.Monoidal] [G.IsEquivalence]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]

/-- A strong monoidal equivalence, applied degreewise, reflects K-flat complexes. -/
lemma kFlat_of_kFlat_mapHomologicalComplex_obj {K : CochainComplex C ℤ}
    (hK : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
      ((G.mapHomologicalComplex (.up ℤ)).obj K)) :
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K := by
  let Gc := G.mapHomologicalComplex (.up ℤ)
  let δ := OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G
  have hq {M M' : CochainComplex C ℤ} (g : M ⟶ M') :
      HomologicalComplex.quasiIso D (.up ℤ) (Gc.map g) ↔
        HomologicalComplex.quasiIso C (.up ℤ) g := by
    simp only [HomologicalComplex.mem_quasiIso_iff]
    exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology g G
  refine ⟨fun M M' g hg ↦ ?_, fun M M' g hg ↦ ?_⟩
  · refine (hq ((tensorLeft K).map g)).1 ?_
    have h₁ := hK.1 _ ((hq g).2 hg)
    refine (HomologicalComplex.quasiIso D (.up ℤ)).arrow_mk_iso_iff ?_ |>.2 h₁
    refine Arrow.isoMk (asIso ((δ.app K).app M)) (asIso ((δ.app K).app M')) ?_
    have := (δ.app K).naturality g
    dsimp at this ⊢
    exact this.symm
  · refine (hq ((tensorRight K).map g)).1 ?_
    have h₁ := hK.2 _ ((hq g).2 hg)
    refine (HomologicalComplex.quasiIso D (.up ℤ)).arrow_mk_iso_iff ?_ |>.2 h₁
    refine Arrow.isoMk (asIso ((δ.app M).app K)) (asIso ((δ.app M').app K)) ?_
    have := congr_app (δ.naturality g) K
    dsimp at this ⊢
    exact this.symm

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

set_option maxHeartbeats 1000000 in
-- The K-flat statements of the condensed model carry instances elaborated in another file.
/-- Pullback of `ℓ`-adic sheaves preserves K-flat complexes. -/
theorem kFlat_adicUpperStar_mapHomologicalComplex_obj (l : ℕ) [Fact l.Prime]
    {S T : Scheme.{u}} (h : S ⟶ T) (P : CochainComplex (AdicSheaf l T) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((adicUpperStar l h).mapHomologicalComplex (.up ℤ)).obj P) := by
  let θ := (locallyFiniteCoefficientRing_realization l).choose
  let (X : Scheme.{u}) : IsMonHom (θ X).hom :=
    (locallyFiniteCoefficientRing_realization l).choose_spec.1 X
  obtain ⟨e⟩ := nativeScalarForgetting_pullbackIso l h
  obtain ⟨mS⟩ := nativeScalarForgetting_monoidal l S
  obtain ⟨mT⟩ := nativeScalarForgetting_monoidal l T
  let ES := AdicSheaf.forgetAb l S ⋙ Mod.comap (θ S).hom
  let ET := AdicSheaf.forgetAb l T ⋙ Mod.comap (θ T).hom
  have : (AdicSheaf.forgetAb l S).IsEquivalence := nativeScalarForgetting_isEquivalence l S
  have : (AdicSheaf.forgetAb l T).IsEquivalence := nativeScalarForgetting_isEquivalence l T
  have : (Mod.comap (θ S).hom).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (θ S).hom).isEquivalence_functor
  have : (Mod.comap (θ T).hom).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (θ T).hom).isEquivalence_functor
  let : ES.Monoidal := inferInstanceAs (AdicSheaf.forgetAb l S ⋙ Mod.comap (θ S).hom).Monoidal
  let : ET.Monoidal := inferInstanceAs (AdicSheaf.forgetAb l T ⋙ Mod.comap (θ T).hom).Monoidal
  have : ES.Additive := Functor.additive_of_preserves_binary_products _
  have : ET.Additive := Functor.additive_of_preserves_binary_products _
  have hT := ET.kFlat_mapHomologicalComplex_obj_of_isEquivalence hP
  have hU := CondensedRing.kFlat_upperStar_mapHomologicalComplex_obj
    (Profinite.padicAlgClRingObj l) h hT
  let e' : adicUpperStar l h ⋙ ES ≅ ET ⋙ CondensedRing.upperStar
      (Profinite.padicAlgClRingObj l) h := e
  let i : (ES.mapHomologicalComplex (.up ℤ)).obj
        (((adicUpperStar l h).mapHomologicalComplex (.up ℤ)).obj P) ≅
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) h).mapHomologicalComplex
        (.up ℤ)).obj ((ET.mapHomologicalComplex (.up ℤ)).obj P) :=
    (Functor.mapHomologicalComplexCompIso e' (.up ℤ)).app P ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).app _).symm
  have hS : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      ((ES.mapHomologicalComplex (.up ℤ)).obj
        (((adicUpperStar l h).mapHomologicalComplex (.up ℤ)).obj P)) :=
    ObjectProperty.prop_of_iso _ i.symm hU
  have : ∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) ES := fun _ ↦ inferInstance
  exact ES.kFlat_of_kFlat_mapHomologicalComplex_obj hS

end AlgebraicGeometry.ProEtale
