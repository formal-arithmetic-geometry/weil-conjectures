/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.FiberDegreeBound

/-!
# Fibres of an immersion have degree at most one

## References

* Stacks Project, Morphisms, Lemma Tag 03J9.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- An immersion has finite fibres of degree at most one. Outside its image the fibre is
empty; on its image the canonical projection to the spectrum of the residue field is an
isomorphism. In particular its fibres are universally bounded. (Stacks, Tag 03J9.) -/
theorem immersion_fiber_degree_one {Z X : Scheme.{u}} (j : Z ⟶ X) [IsImmersion j] :
    BoundsFiberDegrees j 1 ∧
      (∀ x : X, (x ∉ Set.range j → IsEmpty (j.fiber x)) ∧
        (x ∈ Set.range j → IsIso (j.fiberToSpecResidueField x))) ∧
      HasUniversallyBoundedFibers j := by
  classical
  have hclosed (x : X) : IsClosedImmersion (j.fiberToSpecResidueField x) :=
    .of_isPreimmersion (CategoryTheory.Limits.pullback.snd _ _) (isClosed_discrete _)
  have hcases (x : X) :
      (x ∉ Set.range j → IsEmpty (j.fiber x)) ∧
      (x ∈ Set.range j → IsIso (j.fiberToSpecResidueField x)) := by
    constructor
    · intro hx
      exact ⟨fun z ↦ hx ⟨(j.fiberHomeo x z).1, (j.fiberHomeo x z).2⟩⟩
    · rintro ⟨z, hz⟩
      let w : j.fiber x := (j.fiberHomeo x).symm ⟨z, hz⟩
      have :=  hclosed x
      have : Surjective (j.fiberToSpecResidueField x) :=
        ⟨fun y ↦ ⟨w, Subsingleton.elim _ _⟩⟩
      exact isIso_of_isClosedImmersion_of_surjective _
  have hbound : BoundsFiberDegrees j 1 := by
    intro x
    have :=  hclosed x
    refine ⟨inferInstance, ?_⟩
    by_cases hx : x ∈ Set.range j
    · have :=  (hcases x).2 hx
      have h := finrankΓ_eq_of_iso (j.fiberToSpecResidueField x) (𝟙 _)
        (asIso (j.fiberToSpecResidueField x)) (Iso.refl _) (by simp)
      rw [h]
      exact (finrankΓ_id (k := X.residueField x)).le
    · have :=  (hcases x).1 hx
      have h : (j.fiberToSpecResidueField x).finrankΓ = 0 :=
        Module.finrank_zero_of_subsingleton
      simp [h]
  exact ⟨hbound, hcases, 1, hbound⟩

end AlgebraicGeometry.Scheme.Hom
