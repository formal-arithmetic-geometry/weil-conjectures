/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.Paper.ContinuousIntegralLocalization
import Sheaf.Paper.ContinuousIntegralRegularTelescope
import Sheaf.Paper.ContinuousIntegralLocalizationLegs
import all Sheaf.Paper.ContinuousConstructibleIntegralDenominators

/-! # Tensoring the regular localization telescope with a module -/

@[expose] public section

universe u v
open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor


namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

omit [Fact ℓ.Prime] in
/-- An additive functor preserves invertibility of a natural scalar endomorphism.
Source: functorial preservation of isomorphisms and natural multiples of morphisms.
(blueprint: lem-weil-pbc-integral-module-telescope). -/
theorem mappedScalar_isIso
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (F : A ⥤ B) [F.Additive] (M : A) [IsIso (ℓ • 𝟙 M)] :
    IsIso (ℓ • 𝟙 (F.obj M)) := by
  simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id] using F.map_isIso (ℓ • 𝟙 M)

/-- The localization-unit telescope of an integral module is a colimit.
Source: Bhatt--Scholze, Lemma 6.8.2, tensoring the regular localization telescope.
(blueprint: lem-weil-pbc-integral-module-telescope).
Proof. Tensor the regular coefficient colimit with M. Balanced tensor preserves
colimits and identifies its vertex with restricted scalar extension of M. The
zeroth leg is the extension unit by the coequalizer formula. Multiplication by ℓ
is invertible at that vertex, so the zeroth-leg equation determines every leg. -/
noncomputable def integralModuleLocalizationCocone (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)) :
    Cocone (integralLocalizationSequence ℓ M) := by
  have := module_nsmul_isIso ℓ E X
    ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj M)
  exact scalarLocalizationUnitCocone ℓ
    (Mod.extendRestrictAdjunction (coefficientMap (integralScalarMap ℓ E) X)) M

/-- The module localization unit presents scalar extension as its scalar telescope.
Source: Bhatt--Scholze, Lemma 6.8.2.
(blueprint: lem-weil-pbc-integral-module-telescope).
Proof. Tensor the explicit regular coefficient colimit with M and identify its
zeroth leg with the extension unit. Invertibility of ℓ determines the other legs. -/
theorem integralModuleLocalization_isColimit (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)) :
    Nonempty (IsColimit (integralModuleLocalizationCocone ℓ E X M)) := by
  let φ := coefficientMap (integralScalarMap ℓ E) X
  let U := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) φ
  obtain ⟨c, ⟨hc⟩, e, he⟩ := integralRegularTelescope ℓ E X
  let t := Mod.extendComapTensorIso φ M
  let es := (tensorRight M).mapIso e ≪≫ t.symm
  let q := c.ι.app 0 ≫ e.hom
  have hq : q.hom = φ := he
  have hz : (tensorRight M).map (c.ι.app 0) ≫ es.hom =
      (λ_ M).hom ≫ Mod.extendUnit φ M := by
    apply (cancel_mono t.hom).1
    simp only [es, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [Mod.extendUnit_tensor φ M q hq]
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, ← Functor.map_comp]
    rfl
  obtain ⟨d, ⟨hd⟩, v, hv⟩ := transportRegularTelescope ℓ (tensorRight M) c
    (isColimitOfPreserves (tensorRight M) hc) (λ_ M) es (𝟭 _) (Mod.extendUnit φ M) hz
  let target := integralModuleLocalizationCocone ℓ E X M
  have : IsIso (ℓ • 𝟙 target.pt) := by
    have h := module_nsmul_isIso ℓ E X ((Mod.extendScalars φ).obj M)
    change IsIso (ℓ • 𝟙 (U.obj ((Mod.extendScalars φ).obj M)))
    exact mappedScalar_isIso ℓ U _
  have hu : (Mod.extendRestrictAdjunction φ).unit.app M = Mod.extendUnit φ M := by
    change Mod.extendUnit φ M ≫ (Mod.comap φ).map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hzero : d.ι.app 0 ≫ v.hom = target.ι.app 0 := by
    simpa [target, integralModuleLocalizationCocone, scalarLocalizationUnitCocone, ← hu, φ]
      using hv
  exact ⟨hd.ofIsoColimit (Cocone.ext v (integralLocalization_coconeLegs ℓ d target v.hom hzero))⟩

end AlgebraicGeometry.ProEtale.CondensedRing
