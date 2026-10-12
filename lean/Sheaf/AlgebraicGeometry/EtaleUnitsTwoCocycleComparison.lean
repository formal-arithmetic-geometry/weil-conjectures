/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker N3
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Sheaf.FieldTheory.GaloisUnitsTwoCocycles
import Sheaf.FieldTheory.GaloisUnitsHomogeneousComparison
import Mathlib.SetTheory.Cardinal.SchroederBernstein
import Sheaf.AlgebraicGeometry.EtaleUnitsH2ForwardEmbedding
import Sheaf.AlgebraicGeometry.EtaleUnitsH2ReverseEmbedding

/-!
# Etale unit cohomology computed by continuous inhomogeneous cocycles

Source: Stacks Project, Tags 04JQ, 03QU, 03QV (2), and Section 0DVG.
(blueprint: lem-sc-etale-units-two-cocycle-comparison).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Explicit continuous inhomogeneous two-cocycle classes compute the second etale
cohomology of units over a field.

Source: Stacks Project, Tags 04JQ and 03QU, Example 03QV (2), and Section 0DVG.
(blueprint: lem-sc-etale-units-two-cocycle-comparison). -/
theorem nonempty_equiv_twoCocycleClasses_cohomologicalBrauerGroup
    (K : Type u) [Field K] :
    Nonempty (Field.GaloisUnitsTwoCocycleClasses K ≃
      (Spec (.of K)).CohomologicalBrauerGroup) := by
  obtain ⟨eCochains⟩ := Field.nonempty_equiv_galoisUnitsH2_twoCocycleClasses K
  obtain ⟨forward⟩ := nonempty_embedding_galoisUnitsH2_cohomologicalBrauerGroup K
  obtain ⟨reverse⟩ := nonempty_embedding_cohomologicalBrauerGroup_galoisUnitsH2 K
  obtain ⟨eEtale⟩ := Function.Embedding.antisymm forward reverse
  exact ⟨eCochains.symm.trans eEtale⟩

end AlgebraicGeometry.Scheme
