/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization

/-! # Evaluation of a normalized singleton comparison

Source: Stacks Project, Tag 03P2, singleton Čech term.
(blueprint: new-etale-singleton-tensor-normalization-evaluation) -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Evaluating the sole outer Čech index gives an additive map whose value on
normalized pure tensors is the prescribed section. No affine hypothesis is needed.
Source: Stacks Project, Tag 03P2, affine Čech term identification.
(blueprint: new-etale-singleton-tensor-normalization-evaluation)

Proof: define q by the categorical product projection at the unique index
Fin(n+1) → Fin 1, followed by ULift.down. The projection is an additive homomorphism,
and ULift.down is an additive equivalence. Their composite is therefore additive.
Unfold IsSingletonTensorDegreeComparisonHom: its displayed equation is exactly
the asserted equation for q on pure tensors. The only Lean transport is unfolding
the degree-n Čech term and the lifted Amitsur term to expose their carriers.
This construction uses neither affineness, bijectivity nor tensor-generator
induction and applies to empty schemes and zero modules as well.
-/
theorem singletonTensor_normalization_evaluation
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (n : ℕ)
    (f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n)
    (hf : IsSingletonTensorDegreeComparisonHom X F U W g n f) :
    ∃ q : (singletonTensorCech X F U W g).X n →+
      Γ((Modules.tensorPullback (∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)).left.hom).obj F, ⊤),
      letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
      ∀ m b, q ((AddCommGrpCat.Hom.hom f) (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)]
        PiTensorProduct.tprod Γ(U.left, ⊤) b))) =
        (∏ k : Fin (n + 1),
          (Pi.π (fun _ : Fin (n + 1) ↦ Over.mk g) k).left.left.appTop (b k)) •
            Modules.etaleTensorSectionsRestriction F
              (∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)).hom m := by sorry

end
end AlgebraicGeometry.Scheme
