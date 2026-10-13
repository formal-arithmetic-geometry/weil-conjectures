/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization

/-! # Functions on an affine singleton Čech product

Source: Stacks Project, Tags 01I4 and 01JQ.
(blueprint: new-etale-affine-singleton-product-ring) -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- The iterated product is affine, and its functions are the indexed tensor power,
with the expected formula on indexed pure tensors.
Source: Stacks Project, Tags 01I4 and 01JQ.
(blueprint: new-etale-affine-singleton-product-ring)

Proof: take affine spectrum charts for U and W.  For one factor the product is W
and the single-factor indexed tensor power is B.  Add one factor at a time using
Spec(B) × Spec(C) = Spec(B tensor C) over Spec(A).  Associativity of tensor products
and the universal property of the indexed tensor product identify the resulting
ring with the indexed tensor power.  The binary spectrum formula identifies each
projection with the corresponding tensor-factor inclusion.  Multiplying those
inclusions gives the displayed pure-tensor equation.  The spectrum charts also
prove affineness.  The induction starts with one factor, including n = 0; the zero
ring and the empty affine scheme require no extra hypotheses.
-/
theorem singletonProduct_affine_ring
    (X : Scheme.{u}) (U W : X.Etale) (g : W ⟶ U)
    (hU : IsAffine U.left) (hW : IsAffine W.left) (n : ℕ) :
    letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    let P := ∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)
    letI : Algebra Γ(U.left, ⊤) Γ(P.left.left, ⊤) := P.hom.left.appTop.hom.toAlgebra
    IsAffine P.left.left ∧
      ∃ e : (⨂[Γ(U.left, ⊤)] (_ : Fin (n + 1)), Γ(W.left, ⊤)) ≃ₗ[Γ(U.left, ⊤)]
        Γ(P.left.left, ⊤),
        ∀ b : Fin (n + 1) → Γ(W.left, ⊤),
          e (PiTensorProduct.tprod Γ(U.left, ⊤) b) =
            ∏ k : Fin (n + 1),
              (Pi.π (fun _ : Fin (n + 1) ↦ Over.mk g) k).left.left.appTop (b k) := by
  sorry

end
end AlgebraicGeometry.Scheme
