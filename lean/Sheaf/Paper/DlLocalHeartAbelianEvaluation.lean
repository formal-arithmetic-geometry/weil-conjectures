/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.Paper.DlLocallyConstructibleAdicHeart
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Abelian local hearts and exact evaluation

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15;
local-heart construction in lem-dl-a1-local-heart-cover-defects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (T : Over (Spec (.of D.k₀)))

/-- Only the algebraic construction of the cartesian heart, before any cover detection.
Source: BS 6.8.14--6.8.15; local-heart proof Steps 1--7
(blueprint: lem-dl-a1-local-heart-abelian-evaluation). -/
structure DlLocalHeartAbelianEvaluation where
  [localAbelian : Abelian (DlLocallyConstructibleAdicHeart D c T)]
  [componentAbelian (U : DlAdicFiniteOpen D T) :
    Abelian (sfCommonStageHeart c.l U.val.toScheme c.Qbar)]
  evaluationAdditive : ∀ U : DlAdicFiniteOpen D T, (dlAdicLocalEvaluation D c T U).Additive
  evaluationLimits : ∀ U : DlAdicFiniteOpen D T,
    PreservesFiniteLimits (dlAdicLocalEvaluation D c T U)
  evaluationColimits : ∀ U : DlAdicFiniteOpen D T,
    PreservesFiniteColimits (dlAdicLocalEvaluation D c T U)

/-- The cartesian heart is abelian and evaluation is additive and exact.
Source: BS Proposition 6.8.14 and Remark 6.8.15, local-heart proof Steps 1--7
(blueprint: lem-dl-a1-local-heart-abelian-evaluation).

Proof: each separated finite-type basis open has its bounded common-stage standard
heart over k0. Transport the standard t-structure and completed restriction from the
normalized coefficient presentation; the heart is abelian and open restriction is
additive and exact. Add compatible arrows componentwise. Construct the zero family
and binary biproducts componentwise; additive restriction preserves their equations.
For a compatible arrow f, take the component kernels, transporting their universal
properties through exact restriction and the given cartesian isomorphisms. Define
kernel restriction maps by their unique commuting squares with the kernel inclusions.
Cancel those monic inclusions to verify the cocycle and all lift compatibilities.
The dual construction uses component cokernels and cancellation of epic projections.
These are global kernels and cokernels by their component universal properties.
A global mono has zero kernel; evaluation of this kernel is zero, so every component
arrow is monic. Componentwise normal-mono factorizations glue by monic cancellation.
Dually global epis are normal by epic cancellation. This proves the abelian axioms.
Evaluation preserves these kernel and cokernel constructions and the biproducts,
hence is additive and preserves finite limits and finite colimits. No covering,
geometric point or global coefficient field is used in this construction. -/
theorem dlLocalHeartAbelianEvaluation [LocallyOfFiniteType T.hom] :
    Nonempty (DlLocalHeartAbelianEvaluation D c T) := by sorry

end WeilConjectures
