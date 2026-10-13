/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization
import Sheaf.AlgebraicGeometry.EtaleTensorSections
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Surjectivity of the affine singleton tensor comparison

Source: Stacks Project, Tag 03P2, affine tensor calculation; Tags 01I4 and 01I9.
(blueprint: new-etale-affine-singleton-tensor-degree-surjective) -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- A normalized affine singleton comparison lifts every target section.
Source: Stacks Project, Tag 03P2; Tags 01I4, 01JQ, 01I9 and 01IA.
(blueprint: new-etale-affine-singleton-tensor-degree-surjective)

Proof: put A = Γ(U,O), B = Γ(W,O), M = Γ(U*F), and P equal to the
product of n+1 copies of W over U. Iterate the affine fibre-product spectrum
formula, including its projection equations, to identify Γ(P,O) with the
indexed tensor power of B over A. The affine pullback sections formula for
P→U, followed by the unit-normalized tensor-pullback composition comparison,
identifies M tensor Γ(P,O) with Γ(P,P*F). Quasi-coherence of the tensor
pullback to U follows by comparison with ordinary pullback via uniqueness
of left adjoints. Composing and tensoring the ring identification gives an
additive equivalence E from the unlifted source to Γ(P,P*F). Its pure-tensor
formula is the product of the pulled-back functions times the normalized
restriction of the coefficient. Let q be evaluation at the unique outer
Čech index followed by ULift.down. Tensor induction, and indexed tensor
induction with the balancing relation in its scalar case, extend the given
normalization to q(f(ULift.up t)) = E(t) for every tensor t. For a target
element y, choose t = E.symm(q(y)). Then q(f(ULift.up t)) = q(y).
Evaluation at the unique index is an isomorphism (productUniqueIso), and
ULift.down is injective, so q is injective. Thus f(ULift.up t)=y, giving the
required preimage. Zero modules and empty affine schemes cause no exception;
the number of factors is n+1, including one when n=0.
-/
theorem singletonTensorDegreeComparisonHom_surjective
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (hU : IsAffine U.left) (hW : IsAffine W.left)
    (n : ℕ)
    (f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n)
    (hf : IsSingletonTensorDegreeComparisonHom X F U W g n f) :
    Function.Surjective (AddCommGrpCat.Hom.hom f) := by sorry

end
end AlgebraicGeometry.Scheme
