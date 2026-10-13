/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization

/-! # Zero kernel of the affine singleton tensor comparison

Source: Stacks Project, Tag 03P2, affine tensor calculation; Tags 01I4 and 01I9.
(blueprint: new-etale-affine-singleton-tensor-degree-kernel) -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- A normalized affine singleton comparison has zero kernel.
Source: Stacks Project, Tag 03P2; Tags 01I4, 01JQ, 01I9 and 01IA.
(blueprint: new-etale-affine-singleton-tensor-degree-kernel)

Proof: write A = Γ(U,O), B = Γ(W,O), M = Γ(U*F), and let P be the
product of n+1 copies of W over U. Iterating the binary affine fibre-product
spectrum formula identifies Γ(P,O) with the indexed tensor power of B over A;
the single-factor inclusions are pullback along the projections. Affine
pullback sections identify M tensor Γ(P,O) with Γ(P,U*F pulled back to P).
Compare tensor pullback with ordinary pullback by uniqueness of left adjoints
to transport quasi-coherence. Compose with the unit-normalized tensor-pullback
composition isomorphism to identify the latter sections with Γ(P,P*F).
Tensoring the ring equivalence with M gives an additive equivalence E from
the unlifted source tensor module to Γ(P,P*F). Its value on m tensor tprod(b)
is the product of the pulled-back b_i times the normalized restriction of m.
Evaluation at the unique outer Čech index, followed by ULift.down, is an
additive map q from the target to these sections. The normalization of f
says q(f(ULift.up t)) = E(t) on pure generators. TensorProduct.induction_on,
then PiTensorProduct.induction_on in the second factor, extends this equality
to all tensors: handle sums by additivity, and move a scalar from an indexed
pure tensor to the coefficient using the tensor balancing relation. If
f(x)=0, this equality gives E(x.down)=0=E(0). Injectivity of E gives
x.down=0, and injectivity of ULift.down gives x=0. This proof covers zero
modules and empty affine schemes; n=0 still has one factor.
-/
theorem singletonTensorDegreeComparisonHom_kernel
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (hU : IsAffine U.left) (hW : IsAffine W.left)
    (n : ℕ)
    (f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n)
    (hf : IsSingletonTensorDegreeComparisonHom X F U W g n f) :
    ∀ x, (AddCommGrpCat.Hom.hom f) x = 0 → x = 0 := by sorry

end
end AlgebraicGeometry.Scheme
