/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.LimitSystem.Cech

/-!
# Covering stage objects by stage families

Let `D : Iᵒᵖ ⥤ Scheme` be a directed inverse system of quasi-compact quasi-separated schemes with
affine transition maps and limit `X`. Every covering sieve of a stage object `V` of `X_ét` (the
base change of a quasi-compact quasi-separated étale scheme over some stage) contains a stage
family generating a covering sieve
(`AlgebraicGeometry.Etale.SystemData.exists_isStageFamily`), and the Čech nerve of a stage family
consists of stage objects (`AlgebraicGeometry.Etale.SystemData.isStageObject_cechNerveObj`).
Together with `AlgebraicGeometry.Etale.SystemData.exactAt_cechComplex_of_isStageFamily` this
shows that the colimit of a system of injective sheaves has no higher cohomology
(`AlgebraicGeometry.Etale.SystemData.subsingleton_H_succ_of_injective`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Presheaf

namespace AlgebraicGeometry

section AffineSieve

variable {X : Scheme.{u}}

/-- The sieve of the morphisms to `V` whose image lies in an affine open of `V`. -/
def Scheme.Etale.affineSieve (V : X.Etale) : Sieve V where
  arrows _ f := ∃ N : V.left.Opens, IsAffineOpen N ∧ Set.range f.left ⊆ N
  downward_closed {_ _ f} := fun ⟨N, hN, hf⟩ g ↦ ⟨N, hN, fun x ⟨y, hy⟩ ↦ hf ⟨g.left y, by
    rw [← hy]
    rfl⟩⟩

/-- The sieve of the morphisms with image in an affine open is a covering sieve. -/
lemma Scheme.Etale.affineSieve_mem (V : X.Etale) :
    Scheme.Etale.affineSieve V ∈ X.smallEtaleTopology V := by
  let Z (N : V.left.affineOpens) : X.Etale :=
    MorphismProperty.Over.mk ⊤ (N.1.ι ≫ V.hom) inferInstance
  let f (N : V.left.affineOpens) : Z N ⟶ V := MorphismProperty.Over.homMk N.1.ι rfl trivial
  refine X.smallEtaleTopology.superset_covering ?_
    ((Scheme.ofArrows_mem_smallEtaleTopology_iff f).2 ?_)
  · rw [Sieve.generate_le_iff]
    rintro _ _ ⟨N⟩
    exact ⟨N.1, N.2, by simp [f]⟩
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    have hx : x ∈ (⊤ : V.left.Opens) := trivial
    rw [← V.left.iSup_affineOpens_eq_top, TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨N, hN⟩ := hx
    exact Set.mem_iUnion.2 ⟨N, by simpa [f] using hN⟩

end AffineSieve

end AlgebraicGeometry
