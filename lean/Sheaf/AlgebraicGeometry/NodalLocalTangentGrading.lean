/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.AlgebraicGeometry.NodalLocalTangentData
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The canonical grading on the tangent ring

Source: Stacks Project, Algebra, Section 00JM; the associated graded construction.
(blueprint: lem-sfb-nodal-tangent-canonical-grading).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.NodalLocal

/-- The homogeneous summand identifies additively with its image in the direct sum.
Source: Stacks Project, Algebra, Section 00JM; associated graded construction.
(blueprint: lem-sfb-nodal-tangent-canonical-grading) -/
def pieceEquiv (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) :
    Ideal.associatedGradedPiece (IsLocalRing.maximalIdeal A) n ≃+
      tangentGrading A n :=
  AddMonoidHom.ofInjective (DirectSum.of_injective _)

/-- The summand-image equivalence has the original homogeneous inclusion as underlying map.
Source: Stacks Project, Algebra, Section 00JM; associated graded construction.
(blueprint: lem-sfb-nodal-tangent-canonical-grading) -/
theorem pieceEquiv_coe (A : Type u) [CommRing A] [IsLocalRing A]
    (n : ℕ) (a : Ideal.associatedGradedPiece (IsLocalRing.maximalIdeal A) n) :
    (pieceEquiv A n a : Ideal.associatedGraded (IsLocalRing.maximalIdeal A)) =
      DirectSum.of _ n a := rfl

/-- The ranges of the direct-sum inclusions form an internal direct sum.
Source: Stacks Project, Algebra, Section 00JM; associated graded construction.
(blueprint: lem-sfb-nodal-tangent-canonical-grading) -/
theorem tangent_internal (A : Type u) [CommRing A] [IsLocalRing A] :
    DirectSum.IsInternal (tangentGrading A) := by
  let e := DFinsupp.mapRange.addEquiv (pieceEquiv A)
  have h : (DirectSum.coeAddMonoidHom (tangentGrading A)).comp e.toAddMonoidHom =
      AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext
    intro n a
    simp only [AddMonoidHom.comp_apply]
    change DirectSum.coeAddMonoidHom (tangentGrading A)
      (DirectSum.map (fun n ↦ (pieceEquiv A n).toAddMonoidHom)
        (DirectSum.of _ n a)) = _
    rw [DirectSum.map_of, DirectSum.coeAddMonoidHom_of]
    rfl
  have he : DirectSum.coeAddMonoidHom (tangentGrading A) = e.symm.toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro a
    have := DFunLike.congr_fun h (e.symm a)
    change DirectSum.coeAddMonoidHom (tangentGrading A) (e (e.symm a)) = e.symm a at this
    rw [e.apply_symm_apply] at this
    exact this
  rw [DirectSum.IsInternal, he]
  exact e.symm.bijective

/-- The recorded homogeneous subgroups give the canonical grading.
Source: Stacks Project, Algebra, Section 00JM.
(blueprint: lem-sfb-nodal-tangent-canonical-grading) -/
@[instance_reducible]
def canonicalGrading (A : Type u) [CommRing A] [IsLocalRing A] :
    GradedRing (tangentGrading A) := by
  let decomp := (tangent_internal A).chooseDecomposition
  refine { decomp with one_mem := ?_, mul_mem := ?_ }
  · exact ⟨_, (Ideal.associatedGraded_one _).symm⟩
  · intro i j a b ha hb
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    refine ⟨Ideal.associatedGradedMul _ i j a b, ?_⟩
    exact (DirectSum.of_mul_of a b).symm


/-- The degree-zero associated-graded map, with codomain its homogeneous subgroup.
Source: Stacks Project, Algebra, Section 00JM; associated graded construction.
(blueprint: lem-sfb-nodal-tangent-canonical-grading) -/
def zeroHom (A : Type u) [CommRing A] [IsLocalRing A]
    [GradedRing (tangentGrading A)] : A →+* tangentGrading A 0 :=
  { toFun := fun a ↦ ⟨Ideal.associatedGradedRingHom _ a,
        ⟨Submodule.Quotient.mk ⟨a, by simp⟩, rfl⟩⟩
    map_one' := Subtype.ext (map_one _)
    map_zero' := Subtype.ext (map_zero _)
    map_add' := fun a b ↦ Subtype.ext (map_add _ a b)
    map_mul' := fun a b ↦ Subtype.ext (map_mul _ a b) }

/-- The degree-zero map factors through the maximal-ideal quotient.
Source: Stacks Project, Algebra, Section 00JM; associated graded construction.
(blueprint: lem-sfb-nodal-tangent-canonical-grading) -/
def residueToZero (A : Type u) [CommRing A] [IsLocalRing A]
    [GradedRing (tangentGrading A)] : IsLocalRing.ResidueField A →+* tangentGrading A 0 :=
  Ideal.Quotient.lift _ (zeroHom A) (fun a ha ↦ Subtype.ext
    (Ideal.associatedGradedRingHom_ker _ a ha))

/-- The degree-zero part of the tangent ring is the residue field, on representatives.
Source: Stacks Project, Algebra, Section 00JM.
(blueprint: lem-sfb-nodal-tangent-canonical-grading) -/
def tangentZeroIso (A : Type u) [CommRing A] [IsLocalRing A]
    [GradedRing (tangentGrading A)] : IsLocalRing.ResidueField A ≃+* tangentGrading A 0 :=
  RingEquiv.ofBijective (residueToZero A) (by
    constructor
    · intro a b hab
      apply Ideal.algebraMap_associatedGraded_injective (IsLocalRing.maximalIdeal A)
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      exact congrArg (fun t : tangentGrading A 0 ↦
        (t : Ideal.associatedGraded (IsLocalRing.maximalIdeal A))) hab
    · rintro ⟨_, a, rfl⟩
      induction a using Submodule.Quotient.induction_on with
      | _ a => exact ⟨IsLocalRing.residue A a.val, Subtype.ext rfl⟩)

/-- Formula for the degree-zero isomorphism on residue classes.
Source: Stacks Project, Algebra, Section 00JM.
(blueprint: lem-sfb-nodal-tangent-canonical-grading) -/
theorem tangentZeroIso_apply (A : Type u) [CommRing A] [IsLocalRing A]
    [GradedRing (tangentGrading A)] (a : A) :
    (tangentZeroIso A (IsLocalRing.residue A a) :
      Ideal.associatedGraded (IsLocalRing.maximalIdeal A)) =
        Ideal.associatedGradedRingHom (IsLocalRing.maximalIdeal A) a := rfl

end AlgebraicGeometry.NodalLocal
