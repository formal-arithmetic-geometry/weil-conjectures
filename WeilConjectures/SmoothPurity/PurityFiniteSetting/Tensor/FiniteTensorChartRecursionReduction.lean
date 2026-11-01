/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveRootCharts
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveChartRecursion
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveChartFrameExt
import all WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageGlobalEvaluation
import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidalPresheaf
import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleUnit
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicSectionCoordinates

/-! # Coefficient reduction and ordered chart recursion

Source: finite reduction of purity, Step 2; Stacks 03EK and 03PK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

private theorem frame_module_map_id {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat.{u + 1}} (M : PresheafOfModules.{u + 1} R)
    (V : Cᵒᵖ) (x : M.obj V) : M.map (𝟙 V) x = x := by
  rw [M.map_id]
  rfl

-- The inverse-equivalence coefficient square preserves the specified section coordinates.
private theorem fixedLineMap_section
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    (c : P.FiniteTensorLineMaps m hm hmn T) (r : ℤ)
    (V : T.ProEt) (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V)) :
    (P.finiteReductionSetting m hm).finiteTensorSection T r V
        ((P.finiteTensorFixedLineMap m hm hmn T c r).hom.app (Opposite.op V) x) =
      (c r).val.app (Opposite.op V) (P.finiteTensorSection T r V x) := by
  let Q := P.finiteReductionSetting m hm
  let E := sfIntrinsicModuleEquivalence T P.Ring
  let F := sfIntrinsicModuleEquivalence T Q.Ring
  let R := sfFixedRestriction T (P.finiteReductionRingHom m hm hmn)
  let U := proEtaleCoefficientRestrictScalars T (P.finiteReductionRingHom m hm hmn)
  let α := sfRealizationRestriction T (P.finiteReductionRingHom m hm hmn)
  let N := Q.finiteTensorLine T r
  let k := c r ≫ U.map (F.counitIso.inv.app N) ≫ α.hom.app (F.inverse.obj N)
  have hk : P.finiteTensorFixedLineMap m hm hmn T c r =
      E.inverse.map k ≫ E.unitIso.inv.app (R.obj (F.inverse.obj N)) := by
    simp only [finiteTensorFixedLineMap, sfInverseRealizationRestriction, k,
      Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_obj, Functor.comp_map, Functor.map_comp, Iso.symm_hom, Category.assoc]
    rfl
  rw [hk]
  change (F.counitIso.hom.app N).val.app (Opposite.op V)
    (sfIntrinsicRealizationUnit T Q.Ring (F.inverse.obj N) (Opposite.op V)
      ((E.unitIso.inv.app (R.obj (F.inverse.obj N))).hom.app (Opposite.op V)
        ((E.inverse.map k).hom.app (Opposite.op V) x))) = _
  have hu (z : (R.obj (F.inverse.obj N)).obj.obj (Opposite.op V)) :
      sfIntrinsicRealizationUnit T Q.Ring (F.inverse.obj N) (Opposite.op V) z =
        sfIntrinsicRealizationUnit T P.Ring (R.obj (F.inverse.obj N)) (Opposite.op V) z := by
    rfl
  erw [hu, ← sectionRealization_functor P.Ring T, sectionRealization_naturality P.Ring T]
  change (F.counitIso.hom.app N).val.app (Opposite.op V)
    ((α.hom.app (F.inverse.obj N)).val.app (Opposite.op V)
      ((F.counitIso.inv.app N).val.app (Opposite.op V)
        ((c r).val.app (Opposite.op V) (P.finiteTensorSection T r V x)))) = _
  erw [(sfRealizationRestriction_existsUnique T
    (P.finiteReductionRingHom m hm hmn)).exists.choose_spec]
  change (((F.counitIso.inv.app N) ≫ (F.counitIso.hom.app N)).val.app
    (Opposite.op V)) _ = _
  rw [F.counitIso.inv_hom_id_app]
  rfl

-- The lax restriction unit sends the canonical constant section one to one.
private theorem restriction_unit_section (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u}) (V : T.ProEt) :
    (Functor.LaxMonoidal.ε (sfFixedRestriction T
      (P.finiteReductionRingHom m hm hmn))).hom.app (Opposite.op V)
        (P.finiteTensorUnitSection T V) =
      (P.finiteReductionSetting m hm).finiteTensorUnitSection T V := by
  have h := ConcreteCategory.congr_hom
    (congr_app (Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose
      (ProEt.topology T)
      (ModuleCat.restrictScalars.{u + 1}
        (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1}))
        (Opposite.op V)) (1 : P.Coefficient)
  change (Functor.LaxMonoidal.ε (sfFixedRestriction T
      (P.finiteReductionRingHom m hm hmn))).hom.app (Opposite.op V)
        (P.finiteTensorUnitSection T V) =
    (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient))).app (Opposite.op V)
        ((Functor.LaxMonoidal.ε (ModuleCat.restrictScalars.{u + 1}
          (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1}))
            (1 : P.Coefficient)) at h
  simpa only [ModuleCat.restrictScalars_η, map_one, finiteTensorUnitSection] using h

set_option maxHeartbeats 2000000 in
-- Constructing signed frames unfolds the realization and slice module structures.
private theorem chart_frame (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    (e₁ : P.FiniteTensorSheafChartType T 1) (V : T.ProEt) :
    ∃ b : P.FiniteTensorFrame T V,
      P.finiteTensorSection T 1 V (e₁.inv.hom.app (Opposite.op V)
        (P.finiteTensorUnitSection T V)) = b.basis 1 0 := by
  classical
  let : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  let E := sfIntrinsicModuleEquivalence T P.Ring
  let q : P.finiteTensorFirstLine T ≅ proEtaleConstantModule T P.Ring :=
    (E.counitIso.app (P.finiteTensorLine T 1)).symm ≪≫ E.functor.mapIso e₁ ≪≫
      proEtaleConstantModuleUnit T P.Ring
  let x₁ (V : T.ProEtᵒᵖ) : (P.finiteTensorFixedSheaf T 1).obj.obj V :=
    e₁.inv.hom.app V
      ((Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient))).app V (1 : P.Coefficient))
  have hx₁ (V : T.ProEtᵒᵖ) : e₁.hom.hom.app V (x₁ V) =
      (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient))).app V (1 : P.Coefficient) := by
    change ((e₁.inv ≫ e₁.hom).hom.app V) _ = _
    rw [e₁.inv_hom_id]
    rfl
  have hq (V : T.ProEtᵒᵖ) : q.hom.val.app V
      (P.finiteTensorSection T 1 V.unop (x₁ V)) =
        (1 : (proEtaleConstantRing T P.Ring).obj.obj V) := by
    let z := sfIntrinsicRealizationUnit T P.Ring (P.finiteTensorFixedSheaf T 1) V (x₁ V)
    have hc : (E.counitIso.app (P.finiteTensorLine T 1)).inv.val.app V
        ((E.counitIso.app (P.finiteTensorLine T 1)).hom.val.app V z) = z :=
      ConcreteCategory.congr_hom
        (congrArg (fun k ↦ k.val.app V)
          (E.counitIso.app (P.finiteTensorLine T 1)).hom_inv_id) z
    change (proEtaleConstantModuleUnit T P.Ring).hom.val.app V
      ((E.functor.map e₁.hom).val.app V
        ((E.counitIso.app (P.finiteTensorLine T 1)).inv.val.app V
          ((E.counitIso.app (P.finiteTensorLine T 1)).hom.val.app V z))) = _
    erw [hc, ← sfRealizationSectionEquiv_map P.Ring T e₁.hom V (x₁ V)]
    change (proEtaleConstantModuleUnit T P.Ring).hom.val.app V
      (sfIntrinsicRealizationUnit T P.Ring (proEtaleFixedConstantModule T P.Ring) V
        (e₁.hom.hom.app V (x₁ V))) = _
    rw [hx₁]
    have hε : Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
          (ModuleCat.{u + 1} P.Coefficient)) =
        toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
          (ModuleCat.of P.Coefficient P.Coefficient)) := by
      change (sheafificationAdjunction (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient)).homEquiv _ _ (𝟙 _) = _
      rw [Adjunction.homEquiv_unit]
      change toSheafify (ProEt.topology T) _ ≫ 𝟙 _ = _
      exact Category.comp_id _
    rw [hε]
    have hn := (proEtaleConstantModuleUnit_existsUnique T P.Ring).exists.choose_spec
      V (1 : P.Coefficient)
    dsimp only [proEtaleConstantModuleUnit, Coefficient, coefficientCommRing] at hn ⊢
    simp only [map_one] at hn
    convert hn using 1
    rfl
  have frame (V : T.ProEt) : ∃ b : P.FiniteTensorFrame T V,
      P.finiteTensorSection T 1 V (x₁ (Opposite.op V)) = b.basis 1 0 := by
    let e : (P.finiteTensorFirstLine T).val.obj (Opposite.op V) :=
      P.finiteTensorSection T 1 V (x₁ (Opposite.op V))
    have he (W : (Over V)ᵒᵖ) : Function.Bijective
        (fun r : (proEtaleConstantRing T P.Ring).obj.obj (Opposite.op W.unop.left) ↦
          r • (P.finiteTensorFirstLine T).val.map W.unop.hom.op e) := by
      let Q := ((SheafOfModules.evaluation _ (Opposite.op W.unop.left)).mapIso q).toLinearEquiv
      have hgen : Q ((P.finiteTensorFirstLine T).val.map W.unop.hom.op e) =
          (1 : (proEtaleConstantRing T P.Ring).obj.obj (Opposite.op W.unop.left)) := by
        have hn := PresheafOfModules.naturality_apply q.hom.val W.unop.hom.op e
        change q.hom.val.app _ _ =
          (proEtaleConstantRing T P.Ring).obj.map W.unop.hom.op
            (q.hom.val.app (Opposite.op V) e) at hn
        change q.hom.val.app _ _ = _
        rw [hn, hq, map_one]
      have hh (r : (proEtaleConstantRing T P.Ring).obj.obj (Opposite.op W.unop.left)) :
          Q (r • (P.finiteTensorFirstLine T).val.map W.unop.hom.op e) = r := by
        rw [Q.map_smul, hgen, smul_eq_mul, mul_one]
      constructor
      · intro r t hrt
        exact (hh r).symm.trans ((congrArg Q hrt).trans (hh t))
      · intro z
        exact ⟨Q z, Q.injective (hh _)⟩
    obtain ⟨v, ⟨hv, hv1⟩, _⟩ := SheafOfModules.existsUnique_signedLineBasisPowers.{u + 1, u, u + 1}
      (P.finiteTensorFirstLine T) (Opposite.op V) e he
    have hb (m : ℤ) : Function.Bijective
        (fun r : (proEtaleConstantRing T P.Ring).obj.obj (Opposite.op V) ↦ r • v m) := by
      have hh := hv.1 m (Opposite.op (Over.mk (𝟙 V)))
      simp only [Over.mk_hom] at hh
      erw [frame_module_map_id] at hh
      exact hh
    let l (m : ℤ) := LinearEquiv.ofBijective
      ({ toFun := fun r ↦ r • v m
         map_add' := fun r t ↦ add_smul r t _
         map_smul' := fun r t ↦ mul_smul r t _ } :
        (proEtaleConstantRing T P.Ring).obj.obj (Opposite.op V) →ₗ[
          (proEtaleConstantRing T P.Ring).obj.obj (Opposite.op V)]
            (SheafOfModules.signedLinePower.{u + 1, u, u + 1} (P.finiteTensorFirstLine T) m).val.obj
              (Opposite.op V)) (hb m)
    let b (m : ℤ) := (Module.Basis.singleton (Fin 1)
      ((proEtaleConstantRing T P.Ring).obj.obj (Opposite.op V))).map (l m)
    have bval (m : ℤ) : b m 0 = v m := by
      change l m ((Module.Basis.singleton (Fin 1) _ ) 0) = v m
      rw [Module.Basis.singleton_apply]
      change (1 : (proEtaleConstantRing T P.Ring).obj.obj (Opposite.op V)) • v m = _
      exact one_smul _ _
    refine ⟨{ basis := b, zero := ?_, positive := ?_, negative := ?_ }, ?_⟩
    · exact (bval 0).trans hv.2.1
    · intro j
      erw [bval, bval, bval]
      exact hv.2.2.1 j
    · intro j
      erw [bval, bval]
      have hn := hv.2.2.2 j (Opposite.op (Over.mk (𝟙 V)))
      simp only [Over.mk_hom] at hn
      erw [frame_module_map_id] at hn
      exact hn
    · change e = b 1 0
      rw [bval]
      exact hv1.symm
  exact frame V

/-- A coefficient-unit square for first charts propagates to ordered positive powers.
Source: finite reduction of purity, Step 2; parent line-chart proof, Step 2;
Stacks 03EK, 00YV and 03EM.
(blueprint: lem-pur-finite-tensor-chart-recursion-reduction).
Proof: use the inverse of a to take coefficient one to a generator of the first
A-line, and its ordered powers to trivialize each positive line. The hypothesis
h1 sends the first generator to the generator given by the inverse of b. The
positive tensor clause of hc sends each ordered tensor to its target ordered
tensor. Both recursive charts send these tensors to coefficient one. For degree
zero the coefficient-map clause of hc gives the same statement. The normalized
realization unit and counit, and the inverse realization/restriction square,
identify these computations with the actual fixed-scalar maps. The normalized
signed products identify the recursive sheaf tensorators on these basis vectors.
Linearity proves the equality on every section of a trivializing cover and sheaf
separatedness glues it. This proves the formula for arbitrary first charts
satisfying h1, independently of any root choice. It also covers the empty scheme,
identity coefficient maps and ramified quotients without a flatness hypothesis. -/
theorem finiteTensorChartRecursion_reduction
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    (c : P.FiniteTensorLineMaps m hm hmn T)
    (hc : P.FiniteTensorLineMapsNormalized m hm hmn T c)
    (a : P.FiniteTensorSheafChartType T 1)
    (b : (P.finiteReductionSetting m hm).FiniteTensorSheafChartType T 1)
    (h1 : P.finiteTensorFixedLineMap m hm hmn T c 1 ≫
        (sfFixedRestriction.{u, u + 1, u + 1} T (P.finiteReductionRingHom m hm hmn)).map
          b.hom = a.hom ≫ Functor.LaxMonoidal.ε
            (sfFixedRestriction.{u, u + 1, u + 1} T
              (P.finiteReductionRingHom m hm hmn))) (d : ℕ) :
    P.finiteTensorFixedLineMap m hm hmn T c d ≫
        (sfFixedRestriction.{u, u + 1, u + 1} T (P.finiteReductionRingHom m hm hmn)).map
          ((P.finiteReductionSetting m hm).finiteTensorOrdinaryChartRecursion T b d).hom =
      (P.finiteTensorOrdinaryChartRecursion T a d).hom ≫
        Functor.LaxMonoidal.ε
          (sfFixedRestriction.{u, u + 1, u + 1} T
            (P.finiteReductionRingHom m hm hmn)) := by
  let Q := P.finiteReductionSetting m hm
  let R := sfFixedRestriction.{u, u + 1, u + 1} T
    (P.finiteReductionRingHom m hm hmn)
  apply P.finiteTensorPositiveChart_frame_ext T a d _
  intro V fr x₁ x hx₁ hx0 hx
  -- The degree-one square identifies the image with the generator selected by b.
  let y₁ := (P.finiteTensorFixedLineMap m hm hmn T c 1).hom.app (Opposite.op V) x₁
  have hby₁ : b.hom.hom.app (Opposite.op V) y₁ = Q.finiteTensorUnitSection T V := by
    have h := congrArg (fun f ↦ f.hom.app (Opposite.op V) x₁) h1
    change b.hom.hom.app (Opposite.op V) y₁ =
      (Functor.LaxMonoidal.ε R).hom.app (Opposite.op V)
        (a.hom.hom.app (Opposite.op V) x₁) at h
    erw [hx0] at h
    exact h.trans (restriction_unit_section P m hm hmn T V)
  have hy₁ : y₁ = b.inv.hom.app (Opposite.op V) (Q.finiteTensorUnitSection T V) := by
    have h := congrArg (fun z ↦ b.inv.hom.app (Opposite.op V) z) hby₁
    change ((b.hom ≫ b.inv).hom.app (Opposite.op V)) y₁ = _ at h
    rw [b.hom_inv_id] at h
    exact h
  obtain ⟨frB, hfrB⟩ := chart_frame Q T b V
  have hbase : (c 1).val.app (Opposite.op V) (fr.basis 1 0) = frB.basis 1 0 := by
    have hx₁' : P.finiteTensorSection T 1 V x₁ = fr.basis 1 0 := eq_of_heq hx₁
    erw [← hx₁', ← fixedLineMap_section P m hm hmn T c 1 V x₁]
    change Q.finiteTensorSection T 1 V y₁ = _
    rw [hy₁]
    exact hfrB
  have hpow : ∀ n : ℕ,
      (c n).val.app (Opposite.op V) (fr.basis n 0) = frB.basis n 0 := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero =>
      have h := hc.1 (Opposite.op V) (fr.basis 0 0)
      change (c 0).val.app (Opposite.op V) (fr.basis 0 0) = _ at h
      erw [h, fr.zero, map_one, frB.zero]
    | one => exact hbase
    | more n _ ih =>
      have h := hc.2.2.1 n (Opposite.op V)
        (fr.basis (n + 1) 0) (fr.basis 1 0)
        (frB.basis (n + 1) 0) (frB.basis 1 0) (heq_of_eq ih) (heq_of_eq hbase)
      change HEq ((c (n + 2)).val.app (Opposite.op V) _ ) _ at h
      erw [fr.positive n]
      exact (eq_of_heq h).trans (frB.positive n).symm
  -- Both ordered recursions take these corresponding frame vectors to one.
  let y := (P.finiteTensorFixedLineMap m hm hmn T c d).hom.app (Opposite.op V) x
  have hy : Q.finiteTensorSection T d V y = frB.basis d 0 := by
    erw [fixedLineMap_section P m hm hmn T c d V x, eq_of_heq hx]
    exact hpow d
  have hy₁' : Q.finiteTensorSection T 1 V y₁ = frB.basis 1 0 := by
    rw [hy₁]
    exact hfrB
  have hleft := Q.finiteTensorOrdinaryChartRecursion_normalized T b d V frB y₁ y
    (heq_of_eq hy₁') hby₁ (heq_of_eq hy)
  have hright := P.finiteTensorOrdinaryChartRecursion_normalized T a d V fr x₁ x
    hx₁ hx0 hx
  change ((Q.finiteTensorOrdinaryChartRecursion T b d).hom.hom.app
    (Opposite.op V)) y = (Functor.LaxMonoidal.ε R).hom.app (Opposite.op V)
      ((P.finiteTensorOrdinaryChartRecursion T a d).hom.hom.app (Opposite.op V) x)
  rw [hleft, hright]
  exact (restriction_unit_section P m hm hmn T V).symm

end WeilConjectures.PurityFiniteSetting
