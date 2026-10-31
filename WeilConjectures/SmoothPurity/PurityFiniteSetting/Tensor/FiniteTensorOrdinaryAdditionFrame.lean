/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSignedTwistProducts
/-! Ordinary finite tensor addition: local frame calculation. -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting
/-- The two transposed ordinary scalar-extension maps agree on one coherent frame
generator.

Source: finite reduction of purity, Step 2, expanded parent Step 5; Stacks Project
Tags 03EK, 04TT and 03EM. (blueprint: lem-pur-finite-tensor-ordinary-addition-frame).
Proof: transpose both maps through the scalar extension adjunction. The
semilinear uniqueness theorem identifies the adjunct family with the normalized
signed-line comparison. Choose a local trivialization and its coherent signed
powers; `signedLineComparison_tensor` gives the intrinsic product equation for
every pair of signed exponents. `finiteScalarTensorRealization_pure` transports it
on the pure tensor of the two frame sections. Naturality of the realization
counit and scalar restriction cancels the comparison maps, leaving identical
outputs of the two maps. This is a sectionwise calculation on one coherent frame,
so it is strictly below the global map equality and includes all sign cases. -/
theorem finiteTensorOrdinaryAddition_frame
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (r t : ℤ)
    (V : T.ProEt) (e : P.FiniteTensorFrame T V)
    (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V))
    (y : (P.finiteTensorFixedSheaf T t).obj.obj (Opposite.op V))
    (hx : P.finiteTensorSection T r V x = e.basis r 0)
    (hy : P.finiteTensorSection T t V y = e.basis t 0) :
    let φ := (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1}
    let E := ProEtale.sheafExtendScalars φ T
    let a := ProEtale.sheafExtendScalarsAdjunction φ T
    let c := P.finiteTensorLineMaps m hm hmn T
    let d := fun k : ℤ ↦ (a.homEquiv _ _).symm
      (P.finiteTensorFixedLineMap m hm hmn T c k)
    let f : P.finiteTensorFixedSheaf T r ⊗ P.finiteTensorFixedSheaf T t ⟶
        (sfFixedRestriction T (P.finiteReductionRingHom m hm hmn)).obj
          ((P.finiteReductionSetting m hm).finiteTensorFixedSheaf T (r + t)) :=
      a.homEquiv _ _ (E.map (P.finiteTensorSheafProducts T r t).hom ≫ d (r + t))
    let g : P.finiteTensorFixedSheaf T r ⊗ P.finiteTensorFixedSheaf T t ⟶
        (sfFixedRestriction T (P.finiteReductionRingHom m hm hmn)).obj
          ((P.finiteReductionSetting m hm).finiteTensorFixedSheaf T (r + t)) :=
      a.homEquiv _ _
        (Functor.OplaxMonoidal.δ E (P.finiteTensorFixedSheaf T r)
          (P.finiteTensorFixedSheaf T t) ≫ (d r ⊗ₘ d t) ≫
          ((P.finiteReductionSetting m hm).finiteTensorSheafProducts T r t).hom)
    f.hom.app (Opposite.op V) (P.finiteTensorSectionTmul T r t V x y) =
      g.hom.app (Opposite.op V) (P.finiteTensorSectionTmul T r t V x y) := by
  sorry
end WeilConjectures.PurityFiniteSetting
