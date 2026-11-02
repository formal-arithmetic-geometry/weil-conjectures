/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveRootCharts
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicSectionCoordinates
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteTensorFirstSheafChartReductionRootTransport

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

/-- Root-tower normalized calculation on a reduced unit-frame generator.
Source: finite reduction of purity, Step 2; Stacks 03EK and 03PK.
(blueprint: lem-pur-finite-tensor-first-sheaf-chart-reduction-unit-frame-root)
The root section is lifted through the compatible tower, the level-m projection is
identified with eta by `hroot`, and the normalized Tate comparison and degree-one
balancing equation identify the image with the coefficient unit. -/
theorem finiteTensorFirstSheafChart_reduction_unit_on_coordinate
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    (c : P.FiniteTensorLineMaps m hm hmn T)
    (hc : P.FiniteTensorLineMapsNormalized m hm hmn T c)
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (η : P.field.k)
    (hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent)
    (hroot : η = ζ ^ (P.coefficients.l ^ (P.level - m)))
    (V : T.ProEt) (b : (P.finiteReductionSetting m hm).FiniteTensorFrame T V)
    (x₁ : (P.finiteTensorFixedSheaf T 1).obj.obj (Opposite.op V))
    (hy : (P.finiteReductionSetting m hm).finiteTensorSection T 1 V
      ((P.finiteTensorFixedLineMap m hm hmn T c 1).hom.app (Opposite.op V) x₁) =
      (P.finiteReductionSetting m hm).finiteTensorFrameBasis T V b 1)
    (he₁ : (P.finiteTensorFirstSheafChart T ζ hζ).hom.hom.app (Opposite.op V) x₁ =
      (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient))).app (Opposite.op V) (1 : P.Coefficient)) :
    ((P.finiteReductionSetting m hm).finiteTensorFirstSheafChart T η hη).hom.hom.app
        (Opposite.op V)
        ((P.finiteTensorFixedLineMap m hm hmn T c 1).hom.app (Opposite.op V) x₁) =
      (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient))).app
          (Opposite.op V)
          (1 : (P.finiteReductionSetting m hm).Coefficient) := by
  have _ := hy
  have hs := finiteTensorFirstSheafChart_reduction_root_transport
    P m hm hmn T c hc ζ hζ η hη hroot V x₁ he₁
  let Q := P.finiteReductionSetting m hm
  let y := (P.finiteTensorFixedLineMap m hm hmn T c 1).hom.app
    (Opposite.op V) x₁
  let y₀ := (Q.finiteTensorFirstSheafChart T η hη).inv.hom.app
    (Opposite.op V)
      ((Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} Q.Coefficient))).app (Opposite.op V) (1 : Q.Coefficient))
  have hs' : Q.finiteTensorSection T 1 V y = Q.finiteTensorSection T 1 V y₀ := by
    exact hs
  have hyeq : y = y₀ := by
    let : Finite Q.Ring := Padic.finite_coefficientExtensionRing
      Q.coefficients.l Q.extension Q.level Q.level_pos
    exact (sfIntrinsicSectionEquiv Q.Ring T (Q.finiteTensorLine T 1)
      (Opposite.op V)).injective hs'
  have hnorm : (Q.finiteTensorFirstSheafChart T η hη).hom.hom.app
      (Opposite.op V) y₀ =
      (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} Q.Coefficient))).app (Opposite.op V) (1 : Q.Coefficient) := by
    have h := congrArg (fun f ↦ f.hom.app (Opposite.op V))
      (Q.finiteTensorFirstSheafChart T η hη).inv_hom_id
    change (Q.finiteTensorFirstSheafChart T η hη).inv.hom.app (Opposite.op V) ≫
        (Q.finiteTensorFirstSheafChart T η hη).hom.hom.app (Opposite.op V) = _ at h
    have hv := ConcreteCategory.congr_hom h
      ((Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} Q.Coefficient))).app (Opposite.op V) (1 : Q.Coefficient))
    convert hv using 1 <;> rfl
  change (Q.finiteTensorFirstSheafChart T η hη).hom.hom.app
      (Opposite.op V) y = _
  rw [hyeq]
  exact hnorm

end WeilConjectures.PurityFiniteSetting
