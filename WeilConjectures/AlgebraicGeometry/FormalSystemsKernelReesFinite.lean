/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalKernelGradedPieces
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.FormalSystemsKernelReesFiniteExistence

/-! # Finite graded kernel module of a coherent formal system

## References

* [Stacks Project, Tag 087Z](https://stacks.math.columbia.edu/tag/087Z)
* [Stacks Project, Tag 0EHN](https://stacks.math.columbia.edu/tag/0EHN)
-/

@[expose] public section

universe ut

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The sum of successive kernels is quasi-coherent and finite over the associated graded
ideal algebra, with generators in degree zero and the action specified by local lifts
(Stacks, Lemma 087Z and Section 0EHN). -/
theorem formalSystems_kernel_rees_finite {X : Scheme.{ut}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) :
    (∐ (formalKernelPiece F)).IsQuasicoherent ∧
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
  refine ⟨?_, formalSystems_kernel_rees_finite_exists I F⟩
  have hF (n : ℕ) : (F.obj.obj (op n)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
      (F.property.1 n)).1
  let (n : ℕ) : (F.obj.obj (op n)).IsQuasicoherent := hF n
  let (n : ℕ) : (formalKernelPiece F n).IsQuasicoherent := by
    cases n with
    | zero => exact hF 0
    | succ n => exact Scheme.Modules.isQuasicoherent_kernel _
  have hsum := Scheme.Modules.isQuasicoherent_sigma
    (fun n : ULift.{ut} ℕ ↦ formalKernelPiece F n.down)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Sigma.reindex (Equiv.ulift : ULift.{ut} ℕ ≃ ℕ) (formalKernelPiece F)) hsum

end AlgebraicGeometry
