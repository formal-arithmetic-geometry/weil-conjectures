/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleStalkContinuousCohomology
public import WeilConjectures.AlgebraicGeometry.EtaleUnitsGaloisPointStalk

/-!
# Degree-two comparison for the multiplicative sheaf over a field

The cohomological Brauer group `H²(Spec K_ét, 𝔾ₘ)` of a field `K` is the second continuous
Galois cohomology of the units of a separable closure.

## References

* Stacks Project, Tags 04JQ, 03QU, 03QV and 0DVG
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- The second étale cohomology of the multiplicative group over a field `K` is the second
continuous Galois cohomology of the units of the separable closure `Ks` of `K`
(Stacks, Tags 04JQ, 03QU and 0DVG). -/
noncomputable def cohomologicalBrauerGroupAddEquivGaloisUnitsH2 (K : Type u) [Field K] :
    (Spec (.of K)).CohomologicalBrauerGroup ≃+ Field.GaloisUnitsH2 K :=
  haveI : DiscreteTopology (Field.galoisUnitsTopRep K).V := ⟨rfl⟩
  sheafHAddEquivContinuousCohomology K (SeparableClosure K) (Spec (.of K)).gmSheaf
    (Field.galoisUnitsTopRep K) (gmSheafFiberGaloisPointAddEquiv K)
    (gmSheafFiberGaloisPointAddEquiv_presheafFiberAct K) 2

end AlgebraicGeometry.Scheme
