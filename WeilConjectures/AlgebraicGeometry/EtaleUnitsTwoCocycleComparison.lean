/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleGaloisUnitsComparison
public import WeilConjectures.FieldTheory.GaloisUnitsHomogeneousCocycleDescent

/-!
# Etale unit cohomology computed by continuous inhomogeneous cocycles

## References

* Stacks Project, Tags 04JQ, 03QU, 03QV and 0DVG
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Explicit continuous inhomogeneous two-cocycle classes compute the second etale
cohomology of units over a field: the inverse of the change of variables from homogeneous
to inhomogeneous cocycles (`Field.galoisUnitsH2EquivTwoCocycleClasses`), followed by the
comparison `AlgebraicGeometry.Scheme.cohomologicalBrauerGroupAddEquivGaloisUnitsH2`
(Stacks, Tags 04JQ, 03QU, 03QV, 0DVG). -/
noncomputable def twoCocycleClassesEquivCohomologicalBrauerGroup (K : Type u) [Field K] :
    Field.GaloisUnitsTwoCocycleClasses K ≃ (Spec (.of K)).CohomologicalBrauerGroup :=
  (Field.galoisUnitsH2EquivTwoCocycleClasses K).symm.trans
    (cohomologicalBrauerGroupAddEquivGaloisUnitsH2 K).symm.toEquiv

end AlgebraicGeometry.Scheme
