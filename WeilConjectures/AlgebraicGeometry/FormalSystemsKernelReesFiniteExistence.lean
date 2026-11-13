/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.FormalKernelGradedPieces
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
import WeilConjectures.AlgebraicGeometry.FormalAssociatedGradedAlgebraExists
import WeilConjectures.AlgebraicGeometry.FormalKernelGradedActionExists
import WeilConjectures.AlgebraicGeometry.FormalKernelGradedActionLocalGenerators
@[expose] public section
universe ut
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- The graded algebra and finite graded module construction, without the independent
quasi-coherence assertion about the coproduct of kernels
(Stacks, Lemma 087Z, via Lemma 087W and Section 0EHN). -/
theorem formalSystems_kernel_rees_finite_exists {X : Scheme.{ut}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) :
    ∃ A : GradedSheafAlgebra (formalAssociatedGradedPiece I),
      A.unit = formalAssociatedGradedπ I 0 ∧
      (∀ (m n : ℕ) (U : X.Opens)
        (a : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
        (b : (Scheme.idealSheafPower I.toModulesι n).1.val.obj (op U)),
        ∃ c : (Scheme.idealSheafPower I.toModulesι (m + n)).1.val.obj (op U),
          (Scheme.idealSheafPower I.toModulesι (m + n)).2.val.app (op U) c =
            (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a)) *
              (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op U) b)) ∧
          A.mul m n U ((formalAssociatedGradedπ I m).val.app (op U) a)
            ((formalAssociatedGradedπ I n).val.app (op U) b) =
              (formalAssociatedGradedπ I (m + n)).val.app (op U) c) ∧
      ∃ M : GradedSheafModule A (formalKernelPiece F),
        M.IsLocallyGeneratedInDegreeZero ∧
        ∀ (m n : ℕ) (U : X.Opens)
          (a : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
          (x : (formalKernelPiece F n).val.obj (op U))
          (t : (F.obj.obj (op (m + n))).val.obj (op U)),
          (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op U) t =
            (formalKernelι F n).val.app (op U) x →
          (formalKernelι F (m + n)).val.app (op U)
            (M.act m n U ((formalAssociatedGradedπ I m).val.app (op U) a) x) =
              (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a)) • t := by
  obtain ⟨A, hunit, hmul⟩ := formalAssociatedGraded_algebra_exists I
  obtain ⟨M, hact⟩ := formalKernel_graded_action_exists I F A hunit hmul
  refine ⟨A, hunit, hmul, M, ?_, hact⟩
  apply formalKernel_graded_action_local_generators I F A M
  intro n U a x t ht
  exact hact n 0 U a x t ht
end AlgebraicGeometry
