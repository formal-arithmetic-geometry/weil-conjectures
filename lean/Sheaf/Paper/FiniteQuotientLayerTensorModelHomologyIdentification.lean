/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Paper.FiniteCoefficientLocalHomologyModels
public import Sheaf.Paper.FiniteQuotientLayerTensorComplex
public import Sheaf.Paper.FinitePerfectQuotientModelData

/-! # Ordinary homology of the finite constant tensor model

Source: Stacks Project, sites-cohomology.tex, Tags 094H and 06YU.
(blueprint: lem-weil-pbc-finite-quotient-layer-tensor-model-homology-identification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/--
The homology of the derived constant realization of a tensor complex is the
ordinary constant realization of its algebraic homology.  This is the
termwise homology calculation for the bounded-above projective model, together
with transport along the coefficient isomorphism and restriction to the chart.

Source: Stacks Project, sites-cohomology.tex, Tag 094H (locally constant tensor
products) and Tag 06YU (bounded-above flat-complex calculation).
Proof: evaluate the constant realization termwise, use projectivity to compute
derived tensor by the ordinary tensor complex, and apply the homology functor.
The canonical homology comparison for a mapped homological complex identifies
the result with the ordinary homology of
`finiteQuotientLayerTensorComplex`; exact coefficient transport and chart
over-restriction preserve that isomorphism.
(blueprint: lem-weil-pbc-finite-quotient-layer-tensor-model-homology-identification).
-/
theorem finiteQuotient_layer_tensor_model_homology_identification
    (X : Scheme.{t})
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (n : ℕ) (Z : X.Etale)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (0 + 1))) ℤ) (q : ℤ) :
    Nonempty
      (((SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((completedAdicDerivedChange X (φ (n + 1))).obj
              (DerivedCategory.Q.obj
                (finiteModelConstantComplex X _
                  (finiteQuotientLayerTensorComplex d.ideal n P)))))) ≅
        (SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
          ((finiteCoefficientConstantFunctor X
            (A ⧸ d.ideal ^ (n + 1 + 1)) (φ (n + 1))).obj
            ((finiteQuotientLayerTensorComplex d.ideal n P).homology q))) := by
  sorry

end AlgebraicGeometry.Scheme
