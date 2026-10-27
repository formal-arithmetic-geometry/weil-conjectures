/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.RamifiedPullbackTowerData

/-! # Scalar base change for a finite coefficient module

Source: Stacks Project, Tags 03EK and 03EL.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.RamifiedPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The coefficient base-change square acts on every finite module on one site.
Source: Stacks Project, Tags 03EK (section-tensor-product) and 03EL
(lemma-tensor-product-pullback), the balanced-tensor calculation in step 2 of
lem-weil-ramified-finite-module-comparison.
(blueprint: lem-weil-ramified-coefficient-module-base-change).

Proof: Write R,S for the two completed coefficient sheaves, B,T for the two
finite ones, and c:R→S, π:R→B, q:S→T, j:B→T for the square. The supplied
coefficientIso and coefficient_formula identify S tensor_R B with T by
s tensor b ↦ j(b)q(s). Give this tensor its commuting B-action on its second
factor, and give T the B-action through j. The coefficient formula proves
B-linearity on pure tensors: multiplying b by b0 multiplies the image by
j(b0). Tensor generation, followed by sheafification, proves B-linearity
on all sections. Its inverse is B-linear because it is inverse to a
B-linear bijection; both directions also retain their S-linearity.
For a B-module N, use the balanced tensor associator
S tensor_R Res(N) ≅ (S tensor_R B) tensor_B N, whose forward map sends
s tensor x to (s tensor 1) tensor x and inverse sends (s tensor b) tensor x
to s tensor bx. Tensor the supplied coefficient isomorphism with N. The
composite is S-linear, has an inverse given by that coefficient isomorphism's
inverse and the displayed associator, and sends s tensor x to q(s) tensor x.
These are maps of presheaves on local tensor representatives. Sheafification
and the tensor universal property descend them to module sheaves and verify
both inverse identities; the formula is preserved by the sheafification unit.
This uses neither a scheme morphism nor a reduction or pullback of N. It also
works when N=0 or the site is empty, and uses no flatness hypothesis. -/
theorem coefficientModuleBaseChange_exists (W : Scheme.{t})
    (e : ℕ)
    (j : ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1))
    (data : Coefficients l E L ι e j W) (n : ℕ) :
    ∃ b : ∀ N : Mod.{t, u} (integralCoefficientCommRingSheaf l E W n),
      (scalar.{t, u} data.completedMap).obj
          ((SheafOfModules.restrictScalars.{max u (t + 1)}
            ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
              (completedIntegralCommRingProjectionUnrestricted l E W n))).obj N) ≅
        (SheafOfModules.restrictScalars.{max u (t + 1)}
          ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
            (completedIntegralCommRingProjectionUnrestricted l L W (index e n)))).obj
          ((scalar.{t, u} (ramifiedMap l E L W e n (j n))).obj N),
      ∀ (N : Mod.{t, u} (integralCoefficientCommRingSheaf l E W n))
        (U : W.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
        (x : N.val.obj U),
        (b N).hom.val.app U
          (tensor.{t, u} data.completedMap
            ((SheafOfModules.restrictScalars.{max u (t + 1)}
              ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
                (completedIntegralCommRingProjectionUnrestricted l E W n))).obj N) U s x) =
          @id (((SheafOfModules.restrictScalars.{max u (t + 1)}
            ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
              (completedIntegralCommRingProjectionUnrestricted l L W (index e n)))).obj
                ((scalar.{t, u} (ramifiedMap l E L W e n (j n))).obj N)).val.obj U)
            (tensor.{t, u} (ramifiedMap l E L W e n (j n)) N U
              ((completedIntegralCommRingProjectionUnrestricted l L W (index e n)).hom.app U s)
              x) := by sorry

end WeilConjectures.RamifiedPullback
