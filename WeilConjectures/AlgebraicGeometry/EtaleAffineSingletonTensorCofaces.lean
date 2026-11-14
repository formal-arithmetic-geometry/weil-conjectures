/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeComparison
import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorPureCofaces

/-! # Cofaces of the affine singleton tensor comparison

## References

* Stacks Project, Tag 03P2
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- The pure-tensor normalized degree comparisons commute with each coface.
(Stacks, Tags 03P2 and 03DR) -/
theorem singletonTensorDegreeComparison_coface
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U)
    (e : ∀ n : ℕ, (singletonTensorAmitsur X F U W g).X n ≅
      (singletonTensorCech X F U W g).X n)
    (he : ∀ n, IsSingletonTensorDegreeComparison X F U W g n (e n)) :
    letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    ∀ (n : ℕ) (j : Fin (n + 2)),
      (e n).hom ≫ (singletonTensorCechCosimplicial X F U W g).δ j =
        (singletonTensorForget U.left).map
          ((Algebra.TensorProduct.amitsurCosimplicialObject Γ(U.left, ⊤) Γ(W.left, ⊤)
            Γ((Modules.tensorPullback U.hom).obj F, ⊤)).δ j) ≫ (e (n + 1)).hom := by
  classical
  let : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  intro n j
  apply AddCommGrpCat.ext
  intro x
  obtain ⟨x⟩ := x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    change (_ : _ →+ _) (ULift.up x + ULift.up y) =
      (_ : _ →+ _) (ULift.up x + ULift.up y)
    simp only [map_add]
    exact congrArg₂ (· + ·) hx hy
  | tmul m b =>
    induction b using PiTensorProduct.induction_on generalizing m with
    | add b c hb hc =>
      simp only [TensorProduct.tmul_add]
      change (_ : _ →+ _) (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] b) +
        ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] c)) = (_ : _ →+ _)
          (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] b) + ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] c))
      simp only [map_add]
      exact congrArg₂ (· + ·) (hb m) (hc m)
    | smul_tprod r b =>
      simp only [← TensorProduct.smul_tmul]
      exact singletonTensorDegreeComparison_pure_coface_fixed X F U W g e he n j (r • m) b

end
end AlgebraicGeometry.Scheme
