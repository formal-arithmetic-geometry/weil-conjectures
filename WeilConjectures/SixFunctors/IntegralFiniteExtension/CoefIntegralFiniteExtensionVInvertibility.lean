/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionHomMapInvertibility
/-! Auxiliary reduction for evaluation invertibility.
Source: current blueprint, lem-coef-integral-finite-extension.proof.md, paragraphs 4-5
(blueprint: lem-sf-integral-finite-extension-invertibility). -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
  (a : IntegralHom.TensorPresentation.{u, u} X
    (completedIntegralCommRingSheafUnrestricted l E X))
  (b : IntegralHom.TensorPresentation.{u, u} X
    (completedIntegralCommRingSheafUnrestricted l L X))
  (K M : IntegralVerdier.Ambient l E X)
  (hK : IsSfDerivedComplete l E X K) (hM : IsSfDerivedComplete l E X M)
set_option linter.style.haveILetI false in
/-- The evaluation-defined finite-extension comparison is invertible on complete inputs.
Source: finite-free basis computation of the evaluation transpose, followed by
conjugation with the completion comparisons.
(blueprint: lem-sf-integral-finite-extension-v-invertibility)
-/
theorem comparison_invertibility_v :
    IsIso (v l E L ι X a b K M hK hM) := by
  unfold v
  apply IsIso.comp_isIso'
  · infer_instance
  apply IsIso.comp_isIso'
  · exact (homMap_isIso l E L ι X a b K M)
  · let eK := completion l E L ι X K hK
    let eM := completion l E L ι X M hM
    letI : IsIso eK.inv := eK.isIso_inv
    letI : IsIso eM.hom := eM.isIso_hom
    letI : IsIso (Prod.mkHom eK.inv.op eM.hom) :=
      (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
    exact (IntegralHom.hom X
      (completedIntegralCommRingSheafUnrestricted l L X)).map_isIso _
end WeilConjectures.IntegralFiniteExtension
