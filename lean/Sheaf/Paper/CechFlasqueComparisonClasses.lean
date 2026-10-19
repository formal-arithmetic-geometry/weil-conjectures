module

import Sheaf.AlgebraicGeometry.ModuleCechZeroLemmas
public import Sheaf.Paper.CechCupResolutionComparisonData
import all Sheaf.AlgebraicGeometry.ModuleCechComparison

@[expose] public section
universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Homology identifications and canonical-class compatibilities for the core maps.
Source: Stacks Project, Tags 01EQ and 0FKV, cancellation against the injective
resolution comparison.
(blueprint: lem-sc-cech-flasque-resolution-comparison-classes)

Given the core maps and their quasi-isomorphism, compare the computing resolution
with the chosen injective resolution. The resulting invertible homology map defines
`iso`; cancellation in the alpha square gives `alpha_class`, while the beta square
and the defining injective Cech comparison give `beta_class`. The cover hypothesis
is used to invert the injective alpha homology map, hence the total comparison
homology map that is cancelled in the beta-class equation. -/
theorem cechFlasqueComparisonClasses {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) (hU : iSup U = ⊤) {F : X.Modules} (D : CupAcyclicResolution F)
    (alpha : ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.K ⟶ (cupCechDouble U D.K).total (ComplexShape.up ℕ))
    (beta : (cechComplexFunctor U).obj F.presheafModuleCat ⟶
      (cupCechDouble U D.K).total (ComplexShape.up ℕ)) [QuasiIso alpha]
    (halpha : ∀ n : ℕ, alpha.f n = moduleCechZero U (D.K.X n) ≫
      (cupCechDouble U D.K).ιTotal (ComplexShape.up ℕ) n 0 n (by simp))
    (hbeta : ∀ n : ℕ, beta.f n =
      ((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (D.augmentation.f 0).val)).f n ≫
      (cupCechDouble U D.K).ιTotal (ComplexShape.up ℕ) 0 n n (by simp)) :
    ∃ iso : ∀ n : ℕ, (RingedSpace.moduleCohomology X.toRingedSpace n).obj F ≅
      ((cupCechDouble U D.K).total (ComplexShape.up ℕ)).homology n,
      (∀ (n : ℕ)
        (z : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.K).sc n).moduleCatLeftHomologyData.K),
        (iso n).hom (D.class n z) =
          HomologicalComplex.homologyMap alpha n (cupCycleClass _ n z)) ∧
      (∀ (n : ℕ)
        (c : ((cechComplexFunctor U).obj F.presheafModuleCat).homology n ⟶
          (RingedSpace.moduleCohomology X.toRingedSpace n).obj F),
        IsModuleCechComparison U F n c →
        ∀ z : (((cechComplexFunctor U).obj F.presheafModuleCat).sc n).moduleCatLeftHomologyData.K,
          (iso n).hom (c (cupCycleClass _ n z)) =
            HomologicalComplex.homologyMap beta n (cupCycleClass _ n z)) := by
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let G := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let T := (SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op ⋙
      cechComplexFunctor U).mapHomologicalComplex (ComplexShape.up ℕ)
  let t := HomologicalComplex₂.total.map (T.map D.comparison) (ComplexShape.up ℕ)
  have ha : alpha ≫ t = G.map D.comparison ≫ moduleCechAlpha U D.I := by
    apply HomologicalComplex.hom_ext
    intro n
    simp only [HomologicalComplex.comp_f, halpha, t, Category.assoc,
      HomologicalComplex₂.ιTotal_map]
    change moduleCechZero U (D.K.X n) ≫
        ((cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.comparison.f n).val)).f 0 ≫ _ = _
    rw [← Category.assoc, moduleCechZero_naturality]
    rfl
  have hb : beta ≫ t = moduleCechBeta U D.I := by
    apply HomologicalComplex.hom_ext
    intro n
    simp only [HomologicalComplex.comp_f, hbeta, t, Category.assoc,
      HomologicalComplex₂.ιTotal_map]
    let C := SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op ⋙
        cechComplexFunctor U
    change (C.map (D.augmentation.f 0)).f n ≫
      (C.map (D.comparison.f 0)).f n ≫ _ = _
    rw [← Category.assoc, ← HomologicalComplex.comp_f, ← C.map_comp]
    have hover : D.augmentation.f 0 ≫ D.comparison.f 0 = D.I.ι.f 0 :=
      congrArg (fun f ↦ f.f 0) D.over
    rw [hover]
    rfl
  have hcomp (n : ℕ) : IsIso (HomologicalComplex.homologyMap (G.map D.comparison) n) :=
    D.computes n
  let iso (n : ℕ) :=
    (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n) ≪≫
      (asIso (HomologicalComplex.homologyMap (G.map D.comparison) n)).symm ≪≫
      asIso (HomologicalComplex.homologyMap alpha n)
  refine ⟨iso, ?_, ?_⟩
  · intro n z
    change (HomologicalComplex.homologyMap alpha n)
      ((inv (HomologicalComplex.homologyMap (G.map D.comparison) n))
        ((D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).hom
          ((D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv
            (HomologicalComplex.homologyMap (G.map D.comparison) n
              (cupCycleClass _ n z))))) = _
    rw [Iso.inv_hom_id_apply, IsIso.hom_inv_id_apply]
  · intro n c hc z
    have : IsIso (HomologicalComplex.homologyMap (moduleCechAlpha U D.I) n) :=
      moduleCechAlpha_isIso U hU D.I n
    have hha := congrArg (fun f ↦ HomologicalComplex.homologyMap f n) ha
    simp only [HomologicalComplex.homologyMap_comp] at hha
    have hhb := congrArg (fun f ↦ HomologicalComplex.homologyMap f n) hb
    simp only [HomologicalComplex.homologyMap_comp] at hhb
    have : IsIso (HomologicalComplex.homologyMap t n) := by
      have : IsIso (HomologicalComplex.homologyMap alpha n ≫
          HomologicalComplex.homologyMap t n) := by
        rw [hha]
        infer_instance
      exact IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap alpha n)
        (HomologicalComplex.homologyMap t n)
    apply (ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap t n)).mp
      inferInstance
    have heq : c ≫ (iso n).hom ≫ HomologicalComplex.homologyMap t n =
        HomologicalComplex.homologyMap beta n ≫ HomologicalComplex.homologyMap t n := by
      dsimp only [iso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
      simp only [Category.assoc]
      rw [hha, IsIso.inv_hom_id_assoc]
      rw [hc D.I, hhb]
    exact congrArg (fun f ↦ f (cupCycleClass _ n z)) heq


end
end AlgebraicGeometry.Scheme.Modules
