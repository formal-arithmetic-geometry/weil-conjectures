/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveRootCharts
import all WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageGlobalEvaluation

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

private theorem fixedLineMap_section_coordinate
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

/-- The fixed-coordinate line map is `c 1` in section coordinates.
Source: finite reduction of purity, Step 2; Stacks 03EK and 03EM.
(blueprint: lem-pur-finite-tensor-first-sheaf-chart-reduction-unit-frame-section)
Proof: expand `finiteTensorFixedLineMap` as the inverse realization of `c 1`
followed by the inverse realization/restriction comparison; naturality of the
intrinsic section equivalence (realization unit and counit) identifies the reduced
section of its value at `x₁` with `c 1` applied to the section of `x₁`. That section
is `b.basis 1 0` by `hx₁`, and `c 1` sends it to `bB.basis 1 0` by `hbB`. -/
theorem finiteTensorFirstSheafChart_reduction_section_coordinate
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    (c : P.FiniteTensorLineMaps m hm hmn T)
    (V : T.ProEt) (b : P.FiniteTensorFrame T V)
    (bB : (P.finiteReductionSetting m hm).FiniteTensorFrame T V)
    (x₁ : (P.finiteTensorFixedSheaf T 1).obj.obj (Opposite.op V))
    (hx₁ : HEq (P.finiteTensorSection T 1 V x₁)
      (P.finiteTensorFrameBasis T V b 1))
    (hbB : P.finiteTensorLineSectionMap m hm hmn T c 1 (Opposite.op V)
        (P.finiteTensorFrameBasis T V b 1) =
      (P.finiteReductionSetting m hm).finiteTensorFrameBasis T V bB 1) :
    (P.finiteReductionSetting m hm).finiteTensorSection T 1 V
        ((P.finiteTensorFixedLineMap m hm hmn T c 1).hom.app (Opposite.op V) x₁) =
      (P.finiteReductionSetting m hm).finiteTensorFrameBasis T V bB 1 := by
  rw [fixedLineMap_section_coordinate P m hm hmn T c 1 V x₁]
  rw [eq_of_heq hx₁]
  exact hbB
end WeilConjectures.PurityFiniteSetting
