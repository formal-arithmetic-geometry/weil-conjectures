/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- A normalized degree comparison homomorphism, without invertibility.
Source: Stacks Project, Tag 03P2, affine calculation; Tags 01I9 and 01IA.
(blueprint: new-etale-affine-singleton-tensor-degree-comparison-hom)

Compare tensor pullback with Mathlib pullback by uniqueness of the left
adjoint to the same pushforward, respecting their units. This transports
quasi-coherence of U*F from the Mathlib pullback theorem.

Proof: put A₀ = Γ(U,O), B = Γ(W,O), M = Γ(U,U*F). The product P of n+1
copies of W over U is affine. Its functions form the indexed tensor product
of the copies of B over A₀, with each projection inducing the corresponding
tensor inclusion. The affine pullback sections formula applied to P → U
and U*F constructs the comparison to sections of the iterated pullback.
The unit-normalized composition isomorphism identifies that pullback with
P*F and identifies the restriction of m with the étale tensor restriction.
Hence m tensor tprod(b) maps to the product of the pulled-back b(k) acting
on that restriction. Lift this additive map through ULift and invert
evaluation of the outer product at its unique index. This gives the
normalized comparison homomorphism below.
-/
theorem exists_singletonTensorDegreeComparison_hom
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (hU : IsAffine U.left) (hW : IsAffine W.left)
    (n : ℕ) :
    ∃ f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n,
      IsSingletonTensorDegreeComparisonHom X F U W g n f := by sorry

end
end AlgebraicGeometry.Scheme
