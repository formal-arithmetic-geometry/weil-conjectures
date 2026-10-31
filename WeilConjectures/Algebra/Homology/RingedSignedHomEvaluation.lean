/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedTensorSignedCancellation
public import WeilConjectures.CategoryTheory.SignedDerivedInternalHomExact
public import WeilConjectures.SixFunctors.EvaluationShiftTransport
import WeilConjectures.Algebra.Homology.NativeRingedSignedHomEvaluation

/-! # Evaluation of the exact signed ringed internal Hom shift

Source: Stacks 0A8X, 08J9 and 08JC. Both the tensor and the Hom comparisons retain
their actual representative normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (RingedHomUniverses.Modules.{c, v, r} J R)]

/-- Signed exact Hom shifts obey evaluation with the signed tensor cancellation.
Source: Stacks 0A8X and 08JC; the representative evaluation argument in
blueprint det-prop-scalar-six-tensor-hom.proof.md, Reduction.
(blueprint: lem-sfb-ringed-signed-hom-evaluation-Y2).

Proof: choose the coherent exact Hom shift supplied by signed derived-Hom exactness.
Retain its exactness and its degree-one and degree-minus-one normalizations.
For each K and n, apply evaluation transport through the canonical closed tensor
comparison. It preserves the evaluation counit and conjugates native signed
cancellation to the stated cancellation in S. -/
theorem ringedSignedHom_evaluation
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (M : DerivedCategory (RingedHomUniverses.Modules.{c, v, r} J R)) :
    ∃ s : (Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R).CommShift ℤ,
      (fun [_sH : (Prod.sectL _ M ⋙
          derivedInternalHomOfUniverses.{c, v, r, w} J R).CommShift ℤ] ↦
        (Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R).IsTriangulated ∧
        (∀ K, ((Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R).commShiftIso
              (1 : ℤ)).hom.app (op K) =
          -(RingedHomUniverses.sourceShift.{c, v, r, w} J R K (-1)).inv.app M) ∧
        (∀ K, ((Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R).commShiftIso
              (-1 : ℤ)).inv.app (op K) =
          (RingedHomUniverses.sourceShift.{c, v, r, w} J R K 1).hom.app M) ∧
        ∀ (K : DerivedCategory (RingedHomUniverses.Modules.{c, v, r} J R)) (n : ℤ),
          S.tensor.map (Prod.mkHom
            (reindexedDualShift (Prod.sectL _ M ⋙
              derivedInternalHomOfUniverses.{c, v, r, w} J R) n K).inv
            (𝟙 (K⟦-n⟧))) ≫ S.evaluation (K⟦-n⟧) M =
          RingedSignedTensor.cancellation.{c, v, r, w} J R S K
            ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, M)) n ≫
              S.evaluation K M) (_sH := s) := by
  obtain ⟨s, ht, h₁, h₂⟩ := signedDerivedInternalHom_exact.{c, v, r, w} J R M
  refine ⟨s, ht, h₁, h₂, ?_⟩
  letI := s
  intro K n
  exact RingedSignedTensor.evaluation_transport.{c, v, r, w} J R S K M n
    (reindexedDualShift (Prod.sectL _ M ⋙
      derivedInternalHomOfUniverses.{c, v, r, w} J R) n K).inv
    (nativeRingedSignedHom_evaluation.{c, v, r, w} J R M h₁ K n)

end CategoryTheory
