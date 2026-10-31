/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.SixFunctors.CondensedIsomorphismCohomologyTransport

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Exact scalar sections of internal coefficient modules

Source: Stacks Project, Tags 03CW and 0946, and the weakly contractible geometric
point argument (blueprint: lem-weil-point-proetale-sections-exact).

## Main statements

* `pairingPointScalarSections_exact`: exactness of the existing scalar sections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Use the published site-size specialization, avoiding an unassigned max universe.
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]

/-- Exactness of the already recorded terminal scalar sections. The scalar action
is restriction along the canonical Lambda(*) to Lambda_s(s) homomorphism.
Source: Stacks 03CW, 0946 (blueprint: lem-weil-point-proetale-sections-exact).
Proof: the section-module equivalence is exact. Evaluation at the final object
of the geometric point is exact by point_proEtale_sections_exact_of_universes:
every epimorphism lifts there because the point is weakly contractible. Finally,
restriction of scalars is exact on underlying abelian groups. Compose these three
exact functors; the result is exactly CohomologyTransport.sections, without any
boundedness or discreteness assumption on the module or the coefficient ring. -/
theorem pairingPointScalarSections_exact :
    PreservesFiniteLimits (CohomologyTransport.sections Λ (Spec (.of k))) ∧
      PreservesFiniteColimits (CohomologyTransport.sections Λ (Spec (.of k))) := by
  let A := Evaluation.ringSheaf (Scheme.ProEt.topology (Spec (.of k)))
    (condensedRingObj Λ (Spec (.of k)))
  have h := (point_proEtale_sections_exact_of_universes.{u, u, u + 2, u + 2} k).2 A
  have : PreservesFiniteLimits (SheafOfModules.evaluation
      ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)
      (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) := h.1
  have : PreservesFiniteColimits (SheafOfModules.evaluation
      ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)
      (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) := h.2.1
  unfold CohomologyTransport.sections Evaluation.sections
  exact ⟨inferInstance, inferInstance⟩

/-- The finite-limit component of exact scalar sections.
Source: Stacks 03CW (blueprint: lem-weil-point-proetale-sections-exact). -/
instance pairingPointScalarSections_finiteLimits :
    PreservesFiniteLimits (CohomologyTransport.sections Λ (Spec (.of k))) :=
  (pairingPointScalarSections_exact Λ k).1

/-- The finite-colimit component of exact scalar sections.
Source: Stacks 03CW (blueprint: lem-weil-point-proetale-sections-exact). -/
instance pairingPointScalarSections_finiteColimits :
    PreservesFiniteColimits (CohomologyTransport.sections Λ (Spec (.of k))) :=
  (pairingPointScalarSections_exact Λ k).2

end AlgebraicGeometry.ProEtale.CondensedRing
