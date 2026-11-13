/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalKernelGradedPieces
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
import WeilConjectures.AlgebraicGeometry.FormalKernelBilinearActionExists
import WeilConjectures.AlgebraicGeometry.FormalKernelBilinearActionAssociative

/-! # The graded action on formal kernels

## References

* Stacks Project, Tag 087Z
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The associated graded ideal algebra acts on the successive formal-system kernels.
(Stacks, Tag 087Z and Section 0EHN.) -/
theorem formalKernel_graded_action_exists {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I)
    (A : GradedSheafAlgebra (formalAssociatedGradedPiece I))
    (hunit : A.unit = formalAssociatedGradedπ I 0)
    (hmul : ∀ (m n : ℕ) (U : X.Opens)
        (a : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
        (b : (Scheme.idealSheafPower I.toModulesι n).1.val.obj (op U)),
        ∃ c : (Scheme.idealSheafPower I.toModulesι (m + n)).1.val.obj (op U),
          (Scheme.idealSheafPower I.toModulesι (m + n)).2.val.app (op U) c =
            (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a)) *
              (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op U) b)) ∧
          A.mul m n U ((formalAssociatedGradedπ I m).val.app (op U) a)
            ((formalAssociatedGradedπ I n).val.app (op U) b) =
              (formalAssociatedGradedπ I (m + n)).val.app (op U) c) :
    ∃ M : GradedSheafModule A (formalKernelPiece F),
        ∀ (m n : ℕ) (U : X.Opens)
          (a : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
          (x : (formalKernelPiece F n).val.obj (op U))
          (t : (F.obj.obj (op (m + n))).val.obj (op U)),
          (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op U) t =
            (formalKernelι F n).val.app (op U) x →
          (formalKernelι F (m + n)).val.app (op U)
            (M.act m n U ((formalAssociatedGradedπ I m).val.app (op U) a) x) =
              (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a)) • t := by
  obtain ⟨act, hnat, hact⟩ := formalKernel_bilinear_action_exists I F
  have hassoc := formalKernel_bilinear_action_associative I F A act hnat hact hmul
  have hone : ∀ (n : ℕ) (U : X.Opens)
      (x : (formalKernelPiece F n).val.obj (op U)),
      HEq (act 0 n U (A.unit.val.app (op U)
        (1 : X.ringCatSheaf.obj.obj (op U))) x) x := by
    intro n U x
    rw [hunit]
    have hunit_formula (k : ℕ) (hk : k = n) (h : n ≤ k)
        (z : (formalKernelPiece F k).val.obj (op U))
        (hz : ∀ t : (F.obj.obj (op k)).val.obj (op U),
          (F.obj.map (homOfLE h).op).val.app (op U) t =
            (formalKernelι F n).val.app (op U) x →
          (formalKernelι F k).val.app (op U) z = t) : HEq z x := by
      subst k
      apply heq_of_eq
      have hinj : Function.Injective ((formalKernelι F n).val.app (op U)) := by
        cases n with
        | zero => exact Function.injective_id
        | succ n => exact Scheme.Modules.injective_map_kernelι U _
      apply hinj
      apply hz ((formalKernelι F n).val.app (op U) x)
      rw [show (homOfLE h).op = 𝟙 (op n) from Subsingleton.elim _ _, F.obj.map_id]
      rfl
    apply hunit_formula (0 + n) (Nat.zero_add n) (Nat.le_add_left n 0)
    intro t ht
    have hz := hact 0 n U (1 : X.ringCatSheaf.obj.obj (op U)) x t ht
    have hcoeff : (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι 0).2.val.app
        (op U) (1 : X.ringCatSheaf.obj.obj (op U)))) = 1 := rfl
    rw [hcoeff, one_smul] at hz
    exact hz
  refine ⟨{ act := act, naturality := hnat, assoc := hassoc, one_act := hone }, ?_⟩
  exact hact

end AlgebraicGeometry
