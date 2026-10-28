/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DerivedPullbackTensorConstraints

/-! # The integral scalar square for the normalized tensor associator

Source: Stacks 07A4 and the integral step of the prescribed rational scalar square.
(blueprint: stage3-pur-integral-tensor-associator-scalar-square)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- Completed integral scalar extension preserves the coherent-reduction-normalized
associator with its specified tensor comparison.

Source: literature/stacks-project/sites-cohomology.tex, Tag 07A4,
lemma-pullback-tensor-product; integral Step 1 of
lem-pur-rational-tensor-associator-scalar-square.
(blueprint: stage3-pur-integral-tensor-associator-scalar-square)

Proof: choose normalized Roos models from the ambient comparison system and a
primitive scalar model for the fixed E-calculus. Use the normalized tensor-model
realizations for both fixed calculi. The scalar/tensor limit square, after applying
coherent reduction and using counit naturality, gives the binary reduced comparison
square. Reduction intertwining identifies its scalar comparison with the invertible
same-index scalarReduction. Apply this binary square to each of the two nested
tensors. Substitute the defining reduction equations of the two integral
associators. Naturality moves the scalarReduction maps through the L-system
associator. System scalar associator coherence identifies the remaining nested
derivedSigma composites. Cancel the invertible scalar and tensor reduction maps;
faithfulness of coherent reduction on complete constructible objects gives the
displayed equality. The quotient index is unchanged, so this also covers ramified
extensions. Identity coefficient extensions, zero inputs and empty schemes follow
from the same equations; no finite-Tor or finite-type hypothesis is needed.
-/
theorem integralTensorAssociator_scalar_square
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :
    ∀ (X Y Z : sfIntegralConstructibleCategory l E W),
      (sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map
          (pullbackTensorIntegralAssociator l E W X Y Z).hom ≫
        (integralTensorScalarComparison l E L ι W X
          ((constructibleIntegralTensor l E W).obj (Y, Z))).hom ≫
        (constructibleIntegralTensor l L W).map
          (Prod.mkHom (𝟙 _) (integralTensorScalarComparison l E L ι W Y Z).hom) =
      (integralTensorScalarComparison l E L ι W
          ((constructibleIntegralTensor l E W).obj (X, Y)) Z).hom ≫
        (constructibleIntegralTensor l L W).map
          (Prod.mkHom (integralTensorScalarComparison l E L ι W X Y).hom (𝟙 _)) ≫
        (pullbackTensorIntegralAssociator l L W
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj X)
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj Y)
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj Z)).hom := by sorry

end WeilConjectures
