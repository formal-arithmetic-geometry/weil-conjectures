/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.FiniteFreeDirectImageData

/-! # Units and associators of scalar/pullback balancing

Source: Stacks Project, Tag 0D6D, lemma-derived-pullback-composition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

/-- Balancing respects scalar multiplication units and balanced tensor associators.
Source: Stacks Project, Tag 0D6D, lemma-derived-pullback-composition;
finite-free direct-image proof, Step 3.
(blueprint: lem-sp-finite-free-balancing-coherence).

Proof: ordinary scalar extension is sheafification of balanced tensors. For identity
coefficients its multiplication is x tensor r mapping to rx, with inverse x mapping
to x tensor 1. The normalized ordinary unit therefore identifies the balancing map
with the identity. For a tower R to S to B the associator sends (x tensor s) tensor b
to x tensor image(s)b. The two pullback composites send this generator respectively
to q-inverse(x) tensor cB(q-inverse(image(s)b)) and to q-inverse(x) tensor
image(cS(q-inverse(s)))cB(q-inverse(b)). The coefficient square identifies them.
Tensor balancing, additivity and sheafification extend equality to all sections.
Compute the derived scalar functors on flat-term K-flat representatives. Their
normalized counits and units identify these ordinary balanced maps with the
conjugates defining balancing. The normalized derived associator is induced by the
ordinary associator. Localization uniqueness then gives both displayed equations.
This argument uses no finite-basis choice or direct-image comparison. -/
theorem finiteFreeDirectImageBalancingCoherence {Z W : Scheme.{u}} (q : Z ⟶ W)
    (sW : ScalarModel W) (sZ : ScalarModel Z) :
    (∀ (R : Coefficients q) (K : DerivedCategory (proEtaleRingModules W R.target)),
      (proEtaleRingDerivedPullback q R.target R.source R.identification).map
          ((sW.unit R.target).inv.app K) ≫
        (balancing sW sZ (CoefficientMap.id R)).hom.app K ≫
        (sZ.unit R.source).hom.app
          ((proEtaleRingDerivedPullback q R.target R.source R.identification).obj K) = 𝟙 _) ∧
    (∀ (R S B : Coefficients q) (a : CoefficientMap R S) (b : CoefficientMap S B)
      (K : DerivedCategory (proEtaleRingModules W R.target)),
      (balancing sW sZ (a.comp b)).hom.app K =
        (proEtaleRingDerivedPullback q B.target B.source B.identification).map
          ((sW.normalization.derived a.target b.target).inv.app K) ≫
        (balancing sW sZ b).hom.app ((sW.presentation a.target).derived.obj K) ≫
        (sZ.presentation b.source).derived.map ((balancing sW sZ a).hom.app K) ≫
        (sZ.normalization.derived a.source b.source).hom.app
          ((proEtaleRingDerivedPullback q R.target R.source R.identification).obj K)) := by
  sorry

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
