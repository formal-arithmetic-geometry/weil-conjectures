/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeComparison
import Sheaf.AlgebraicGeometry.EtaleTensorSections
import WeilConjectures.RingTheory.FaithfullyFlat.Amitsur

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- Fixed-degree pure-tensor coface compatibility.
Source: Stacks Project, Tag 03P2, affine-case tensor differential formula.
(blueprint: new-etale-affine-singleton-tensor-pure-coface-fixed)

This is the fixed `(n,j)` component of the pure-tensor coface equation.  It
is obtained by evaluating the singleton product at its unique tuple, using the
normalization formula for `e n` and `e (n+1)`, and the functoriality of section
restriction.  The inserted Amitsur factor is the unit, while all retained
factors are carried by the corresponding product projections.
-/
theorem singletonTensorDegreeComparison_pure_coface_fixed
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U)
    (e : ∀ n : ℕ, (singletonTensorAmitsur X F U W g).X n ≅
      (singletonTensorCech X F U W g).X n)
    (he : ∀ n, IsSingletonTensorDegreeComparison X F U W g n (e n))
    (n : ℕ) (j : Fin (n + 2))
      (m : Γ((Modules.tensorPullback U.hom).obj F, ⊤))
      (b : Fin (n + 1) → Γ(W.left, ⊤)) :
    letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    ((e n).hom ≫ (singletonTensorCechCosimplicial X F U W g).δ j)
        (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b)) =
      ((singletonTensorForget U.left).map
        ((Algebra.TensorProduct.amitsurCosimplicialObject Γ(U.left, ⊤) Γ(W.left, ⊤)
          Γ((Modules.tensorPullback U.hom).obj F, ⊤)).δ j) ≫ (e (n + 1)).hom)
            (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b)) := by
  sorry

end
end AlgebraicGeometry.Scheme
