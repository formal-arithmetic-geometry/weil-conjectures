/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.ConstantWeilStructure
public import Sheaf.Paper.CompletedPullbackTensorComparison

/-! # Linear duals of common-stage Weil complexes

Source: blueprint, sec-purity-real-sheaves/sk-r-real-linear, dual representation;
Stacks Tag 0FNY (blueprint: def-real-common-stage-weil-linear-dual).
Internal Hom is specified by its representing universal property. Evaluation is a Weil
morphism for the published tensor comparison and constant coefficient Weil structure.
Thus this specifies the usual linear dual, uniquely up to evaluation-preserving Weil iso.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- D is Hom(F,Omega_Y), with contragredient Weil structure. The first condition says
that evaluation represents internal Hom on the actual constructible derived category.
For a lisse F this is ordinary sheaf Hom in degree zero. The second condition is
b(theta_D d,theta_F v)=g*b(d,v). By the universal property it determines theta_D as
precomposition with theta_F inverse after the canonical pullback-Hom comparison.
Source: Stacks 0FNY, 0GMX; blueprint dual representation sentence
(blueprint: def-real-common-stage-weil-linear-dual). -/
def IsCommonStageWeilLinearDual
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (F Fv : sfCommonStageWeilComplex D l hl Y₀ Ω) : Prop :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  ∃ e : (commonStageDerivedTensor l Ω (D.geometricFiber Y₀).left).obj
      (Fv.carrier, F.carrier) ⟶
        (constantWeilAlgebraicallyClosedComplex l D hl Y₀ Ω).carrier,
    (∀ T : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left,
      Function.Bijective (fun f : T ⟶ Fv.carrier ↦
        (commonStageDerivedTensor l Ω (D.geometricFiber Y₀).left).map
          (Prod.mkHom f (𝟙 F.carrier)) ≫ e)) ∧
    (canonicalCommonStagePullbackTensor l Ω (D.geometricFrobenius Y₀).hom
      Fv.carrier F.carrier).hom ≫
        (commonStageDerivedTensor l Ω (D.geometricFiber Y₀).left).map
          (Prod.mkHom Fv.str.hom F.str.hom) ≫ e =
      (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).map e ≫
        (constantWeilAlgebraicallyClosedComplex l D hl Y₀ Ω).str.hom

end WeilConjectures
