/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
import all WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.ModuleEqualizerInternalHom

/-! # Comparing the two ordinary relative tensor presentations

## References

* Stacks Project, Tag 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

-- Elaborating the concrete tensor instances requires large definitional comparisons.
/-- The two ordinary coequalizer tensors agree by an isomorphism fixing their quotient maps. -/
theorem ordinary_relative_tensor_identification
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    ∃ b : ∀ P Q : ProEtale.AdicSheaf l Y,
        ((ordinaryTensorBifunctor l Y).obj P).obj Q ≅ Q ⊗ P,
      ∀ P Q, Mod.tensorπ Q P ≫ (b P Q).hom.hom = Mod.tensorObjπ Q P := by
  refine ⟨fun P Q ↦ (Mod.equalizerAdjTensorRightIso P).app Q, ?_⟩
  intro P Q
  have h : colimit.ι ((Mod.tensorLeftDiagram _ P).flip.obj Q) WalkingParallelPair.one ≫
      ((Mod.equalizerAdjTensorRightIso P).app Q).hom =
        Mod.equalizerAdjTensorπ Q P := by
    simp [Mod.equalizerAdjTensorRightIso, Mod.equalizerAdjTensorCofork,
      Mod.equalizerAdjTensorπ, HasColimit.ι_isoOfNatIso_hom_assoc]
  exact congrArg (fun f ↦ f.hom) h

end AlgebraicGeometry.ProEtaleWeilSheaf
