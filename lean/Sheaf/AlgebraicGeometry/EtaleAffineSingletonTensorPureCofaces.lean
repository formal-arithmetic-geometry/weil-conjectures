/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeComparison
import Sheaf.AlgebraicGeometry.EtaleTensorSections
import WeilConjectures.RingTheory.FaithfullyFlat.Amitsur

/-! # Pure-tensor coface formula for singleton sections
Source: Stacks Project, Tag 03P2, the tensor differential formula.
(blueprint: new-etale-affine-singleton-tensor-pure-cofaces).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- The normalized affine comparison carries a single pure tensor through a coface.
Source: Stacks Project, Tag 03P2, affine-case tensor differential formula;
Tag 03DR, equation (35.8.0.1), for the section restrictions.
(blueprint: new-etale-affine-singleton-tensor-pure-cofaces)

Proof: evaluate the singleton product at its unique tuple. The Amitsur coface
associated to j maps tprod(b) to tprod(j.insertNth 1 b). This follows by expressing
an indexed pure tensor as the product of its single-factor inclusions and using
amitsurMap_comp_singleAlgHom; the retained factors land in j.succAbove(k).
The normalization equation in degree n+1 therefore makes the right side the
product of the retained pulled-back functions times the restriction of m from U.
The Čech coface on the left restricts along the product projection omitting j.
Its section restriction is semilinear. The product projection equations identify
the pullbacks of all retained functions, while the restriction composition law
identifies the coefficient restriction with the direct restriction from U.
Thus the two sides agree. The inserted factor is one, so contributes nothing.
This argument is independent of affineness and tests just one pure tensor;
it asserts neither degreewise bijectivity nor a chain map on arbitrary elements.
The case n=0 gives the two usual pullbacks, and zero section groups give zero. -/
theorem singletonTensorDegreeComparison_pure_coface
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U)
    (e : ∀ n : ℕ, (singletonTensorAmitsur X F U W g).X n ≅
      (singletonTensorCech X F U W g).X n)
    (he : ∀ n, IsSingletonTensorDegreeComparison X F U W g n (e n)) :
    letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    ∀ (n : ℕ) (j : Fin (n + 2))
      (m : Γ((Modules.tensorPullback U.hom).obj F, ⊤))
      (b : Fin (n + 1) → Γ(W.left, ⊤)),
      ((e n).hom ≫ (singletonTensorCechCosimplicial X F U W g).δ j)
        (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b)) =
      ((singletonTensorForget U.left).map
        ((Algebra.TensorProduct.amitsurCosimplicialObject Γ(U.left, ⊤) Γ(W.left, ⊤)
          Γ((Modules.tensorPullback U.hom).obj F, ⊤)).δ j) ≫ (e (n + 1)).hom)
            (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b)) := by sorry

end
end AlgebraicGeometry.Scheme
