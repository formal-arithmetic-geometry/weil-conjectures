/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveRootCharts
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteTensorCompatibleRootTowerLift
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteTensorFirstSheafChartUnitRootTensor
import all WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageGlobalEvaluation

/-! # Root-tensor calculation for coefficient reduction

Source: finite reduction of purity, Step 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

/-- Reduction transports a source chart-unit generator to the reduced chart-unit
section in fixed-scalar coordinates.
Source: finite reduction of purity, Step 2; Stacks 03EK and 03PK.
(blueprint: lem-pur-finite-tensor-first-sheaf-chart-reduction-root-transport)
Use the compatible root tower to identify the level-m root with `η`, then use
the normalized degree-one balancing equation of `hc` and the section-normalized
finite Tate comparison. The source chart-unit section and the reduced chart-unit
section are thereby the same after the fixed-line map. -/
theorem finiteTensorFirstSheafChart_reduction_root_transport
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    (c : P.FiniteTensorLineMaps m hm hmn T)
    (hc : P.FiniteTensorLineMapsNormalized m hm hmn T c)
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (η : P.field.k)
    (hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent)
    (hroot : η = ζ ^ (P.coefficients.l ^ (P.level - m)))
    (V : T.ProEt)
    (x₁ : (P.finiteTensorFixedSheaf T 1).obj.obj (Opposite.op V))
    (he₁ : (P.finiteTensorFirstSheafChart T ζ hζ).hom.hom.app (Opposite.op V) x₁ =
      (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient))).app (Opposite.op V) (1 : P.Coefficient)) :
    (P.finiteReductionSetting m hm).finiteTensorSection T 1 V
        ((P.finiteTensorFixedLineMap m hm hmn T c 1).hom.app
          (Opposite.op V) x₁) =
      (P.finiteReductionSetting m hm).finiteTensorSection T 1 V
        (((P.finiteReductionSetting m hm).finiteTensorFirstSheafChart T η hη).inv.hom.app
          (Opposite.op V)
          ((Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
            (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient))).app
              (Opposite.op V) (1 : (P.finiteReductionSetting m hm).Coefficient))) := by
  let Q := P.finiteReductionSetting m hm
  let y₀ := (Q.finiteTensorFirstSheafChart T η hη).inv.hom.app
    (Opposite.op V) (Q.finiteTensorUnitSection T V)
  have hy₀ : (Q.finiteTensorFirstSheafChart T η hη).hom.hom.app
      (Opposite.op V) y₀ = Q.finiteTensorUnitSection T V := by
    change (((Q.finiteTensorFirstSheafChart T η hη).inv ≫
      (Q.finiteTensorFirstSheafChart T η hη).hom).hom.app (Opposite.op V)) _ = _
    rw [(Q.finiteTensorFirstSheafChart T η hη).inv_hom_id]
    rfl
  obtain ⟨t, htA, htB⟩ := finiteTensor_compatible_root_tower_lift
    P m hm hmn T ζ hζ η hroot V
  have hxA := finiteTensorFirstSheafChart_unit_root_tensor P T ζ hζ V t htA x₁ he₁
  have hxB := finiteTensorFirstSheafChart_unit_root_tensor Q T η hη V t htB y₀ hy₀
  have hbal := hc.2.1 (Opposite.op V) 1
    (purTwistIntegralTensor T P.coefficients.l P.extension (Opposite.op V) 1 t)
    (P.finiteTensorSection T 1 V x₁) hxA
  have hmapone :
      (proEtaleConstantRingMap (T := T) (P.finiteReductionRingHom m hm hmn)).hom.app
        (Opposite.op V) (1 : (proEtaleConstantRing T P.Ring).obj.obj (Opposite.op V)) =
      1 := map_one _
  rw [hmapone] at hbal
  have hs : P.finiteTensorLineSectionMap m hm hmn T c 1 (Opposite.op V)
      (P.finiteTensorSection T 1 V x₁) = Q.finiteTensorSection T 1 V y₀ :=
    eq_of_heq (hbal.trans hxB.symm)
  rw [fixedLineMap_section_coordinate P m hm hmn T c 1 V x₁]
  exact hs

end WeilConjectures.PurityFiniteSetting
