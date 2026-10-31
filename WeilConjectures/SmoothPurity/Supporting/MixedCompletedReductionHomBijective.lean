/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.MixedReductionUnit

/-! # The finite universal property of the completed mixed unit

Source: lem-fix-operation-reduction, compact-support paragraph; Stacks 07A6 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The specified completed mixed unit represents finite derived coefficient extension.
This assertion concerns arbitrary derived inputs and targets and has no geometric operation.
Source: lem-fix-operation-reduction, compact-support paragraph, first normalization step;
Stacks 07A6 (lemma-adjoint), 0941 (lemma-derived-limit-is-ok)
(blueprint: lem-sf-mixed-completed-reduction-hom-bijective).
Proof: use the coherent coefficient-extension reduction comparison, namely its actual
reduction counit followed by inverse scalar association. On a flat-term K-flat
representative the ordinary mixed unit sends s tensor x to iota(s) tensor (1 tensor x).
Association carries this to the finite scalar-adjunction unit. The completion factor
is the diagonal Roos augmentation with zero shifted coordinate. The strict Roos
comparison identifies its composite with every limit projection with that augmentation.
The effectivity counit is the adjunct of the same projection, so the comparison carries
the entire completed mixed unit to the finite scalar-adjunction unit. Representative
comparisons and localization extend this identity to every derived input. Transport
Hom along this comparison and use the derived extension/restriction adjunction.
Both maps are bijections, with no boundedness assumption on the target. -/
theorem sfMixedCompletedReductionHomBijective
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (K : DerivedCategory (scalarReductionSource l E W)) (n : ℕ)
    (Z : proEtaleDerivedCategory W (Padic.coefficientExtensionRing l L (n + 1))) :
    Function.Bijective (fun a :
      (scalarReductionDerivedExtension l L W n).obj
        ((integralScalarExtension l E L ι W).obj K) ⟶ Z ↦
      sfMixedCompletedReductionUnit l E L ι W n K ≫
        (proEtaleCoefficientRestrictScalars W
          (integralScalarQuotientMap l E L ι n)).mapDerivedCategory.map a) := by sorry

end WeilConjectures
