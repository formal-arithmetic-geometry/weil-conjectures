/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization
import WeilConjectures.AlgebraicGeometry.EtaleSingletonTensorCechCofaceEvaluation
import WeilConjectures.AlgebraicGeometry.EtaleSingletonTensorNormalizedRestriction

/-! # Geometric cofaces of normalized singleton tensor sections

## References

* Stacks Project, Tags 03P2 and 03DR
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- The geometric Čech coface preserves the inserted-unit normalization
(Stacks, Tags 03P2 and 03DR). -/
theorem singletonTensorCech_normalized_coface
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (n : ℕ) (j : Fin (n + 2))
    (f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n)
    (f' : (singletonTensorAmitsur X F U W g).X (n + 1) ⟶
      (singletonTensorCech X F U W g).X (n + 1))
    (hf : IsSingletonTensorDegreeComparisonHom X F U W g n f)
    (hf' : IsSingletonTensorDegreeComparisonHom X F U W g (n + 1) f')
    (m : Γ((Modules.tensorPullback U.hom).obj F, ⊤))
    (b : Fin (n + 1) → Γ(W.left, ⊤)) :
    letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    (singletonTensorCechCosimplicial X F U W g).δ j
      (f (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b))) =
    f' (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)]
      PiTensorProduct.tprod Γ(U.left, ⊤) (j.insertNth 1 b))) := by
  classical
  let : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  let V := fun _ : Fin (n + 2) → Fin 1 ↦
    AddCommGrpCat.of (ULift.{u + 1}
      Γ((Modules.tensorPullback
        (∏ᶜ (fun _ : Fin (n + 2) ↦ Over.mk g)).left.hom).obj F, ⊤))
  have hi : Function.Injective (Pi.π V (fun _ ↦ 0)) := by
    have he : (fun _ : Fin (n + 2) ↦ (0 : Fin 1)) = default := Subsingleton.elim _ _
    rw [he, ← productUniqueIso_hom]
    exact (ConcreteCategory.bijective_of_isIso _).injective
  apply hi
  apply ULift.ext
  exact (singletonTensorCech_coface_evaluation X F U W g n j _).trans
    (singletonTensor_normalized_restriction X F U W g n j f f' hf hf' m b)


end
end AlgebraicGeometry.Scheme
