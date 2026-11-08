/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.Algebra.Homology.MixedTotalTensor
public import Submission.WeilConjectures.Algebra.Homology.RingTensorCohomology
public import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Submission.WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Underlying additive homology of mixed total tensors

Source: Stacks Project, Tag 06Y6, the ordinary balanced tensor identifications.
(blueprint: new-lem-pc-mixed-tensor-underlying-homology).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace RingTensorCohomology

open MonoidalCategory
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def coeff (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (M : ModuleCat.{u} A) (N : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars (algebraMap R A)).obj
      (((ModuleCat.mixedTensor (algebraMap R A)).obj M).obj N) ≅
      (ModuleCat.restrictScalars (algebraMap R A)).obj M ⊗ N := by
  let : Algebra R A := (algebraMap R A).toAlgebra
  let : Module R M := Module.compHom M (algebraMap R A)
  let : IsScalarTower R A M := SMul.comp.isScalarTower (algebraMap R A)
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A M N).restrictScalars R
    |>.toModuleIso


end RingTensorCohomology
