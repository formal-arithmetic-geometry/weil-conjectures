/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.Paper.FiniteQuotientCoefficientLayerData
public import Sheaf.Paper.FiniteQuotientLayerTensorComplex
public import Sheaf.Paper.FiniteCoefficientLocalHomologyModels

public import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Ordinary constant tensor compatibility for the finite coefficient layer

Source: Stacks Project, Tags 03EK, 03EL and 094I.
(blueprint: lem-weil-pbc-finite-quotient-layer-ordinary-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Ordinary tensor with the constant residue layer agrees with constant
realization of the explicit algebraic layer tensor, retaining the successor action.

Source: Stacks Project, Modules on Sites, Tags 03EK and 03EL; Cohomology on Sites,
Tag 094I, the ordinary constant ideal-layer tensor calculation.
(blueprint: lem-weil-pbc-finite-quotient-layer-ordinary-tensor-comparison).

Proof: constant module sheafification preserves tensor products. Lifting modules
by ULift commutes with tensor by the canonical lifted pure-tensor equivalence;
extension along phi_0 also preserves tensor by balanced scalar extension.
These comparisons identify C(P) tensor C(L) with C(P tensor L), naturally in P.
Apply the symmetry to obtain C(L tensor P). Restriction along the successor to
residue coefficient map agrees with constant realization after the algebraic
quotient B -> C: cancel the constant quotient map from A in hc.2 to obtain this
coefficient square. Extension along the isomorphism phi_(n+1) transports the
square to the actual successor coefficient sheaf. These maps commute with all
module morphisms since on local constant generators they send x tensor l to
l tensor x; local tensor generation and sheafification determine the maps.
No flatness, projectivity, boundedness or finiteness assumption on P or L is
used. Zero layers, zero rings and empty sites use the same universal properties. -/
theorem finiteQuotient_layer_ordinary_tensor_comparison
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ k : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (k + 1)) ⟶
      completedAdicFiniteCommRing X d k)
    (hφ : ∀ k : ℕ, IsIso (φ k))
    (hc : FinitePerfectModelsCompatible X d φ) (n : ℕ) :
    letI := SheafOfModules.monoidalCategory (completedAdicFiniteCommRing X d 0)
    Nonempty
      (finiteCoefficientConstantFunctor X (A ⧸ d.ideal ^ (0 + 1)) (φ 0) ⋙
          MonoidalCategory.tensorRight
            ((finiteCoefficientConstantFunctor X (A ⧸ d.ideal ^ (0 + 1)) (φ 0)).obj
              (finiteQuotientLayerModule d.ideal n)) ⋙
          SheafOfModules.restrictScalars.{t + 1}
            ((sheafCompose (ProEt.topology X)
              (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
                (completedAdicQuotientCommMap X d (n + 1) 0 (Nat.zero_le _))) ≅
        finiteQuotientLayerTensor d.ideal n ⋙
          finiteCoefficientConstantFunctor X (A ⧸ d.ideal ^ (n + 1 + 1)) (φ (n + 1))) := by sorry

end AlgebraicGeometry.Scheme
