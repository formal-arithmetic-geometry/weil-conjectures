/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism

/-! # Reduction of an affine family before generic flatness

## References

* Stacks Project, Tag 0559
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

/-- Reduction produces an integral affine base and a reduced affine source, before shrinking
(Stacks, Tags 0559, 01IZ and 054M). -/
theorem exists_affine_reduction_preparation
    {X T : Scheme.{u}} [IsAffine X] (f : X ⟶ T) [LocallyOfFiniteType f]
    (V : T.Opens) (hV : IsAffineOpen V) (himage : Set.range f ⊆ V)
    (η : T) (hη : IsGenericPoint η Set.univ) (hηV : η ∈ V) :
    ∃ (S Z : Scheme.{u}) (q : S ⟶ V.toScheme)
      (h : Z ⟶ pullback f (q ≫ V.ι)),
      IsAffine S ∧ IsIntegral S ∧ IsAffine Z ∧ IsReduced Z ∧
      IsUniversalHomeomorphism q ∧ IsUniversalHomeomorphism h ∧
      LocallyOfFiniteType (h ≫ pullback.snd f (q ≫ V.ι)) := by
  let : IsAffine V.toScheme := hV
  let S := V.toScheme.nilradical.subscheme
  let q : S ⟶ V.toScheme := V.toScheme.nilradical.subschemeι
  have hqred :=
    reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism V.toScheme
  let : IsReduced S := hqred.1
  let : IsClosedImmersion q := hqred.2.1
  let : IsAffine S := isAffine_of_isAffineHom q
  let : Surjective q := hqred.2.2.1
  have hq : IsUniversalHomeomorphism q := inferInstance
  obtain ⟨s, hs⟩ := q.surjective ⟨η, hηV⟩
  have hsg : IsGenericPoint s (Set.univ : Set S) := by
    rw [isGenericPoint_iff_specializes]
    intro t
    simp only [Set.mem_univ, iff_true]
    apply q.isEmbedding.isInducing.specializes_iff.mp
    apply V.ι.isOpenEmbedding.isEmbedding.isInducing.specializes_iff.mp
    have he : V.ι (q s) = η := congrArg Subtype.val hs
    rw [he]
    exact hη.specializes (Set.mem_univ _)
  let : IrreducibleSpace S := (irreducibleSpace_def _).mpr hsg.isIrreducible
  let : IsIntegral S := isIntegral_of_irreducibleSpace_of_isReduced S
  have hfac : Set.range f ⊆ Set.range V.ι := by
    simpa only [Scheme.Opens.range_ι] using himage
  have hp := IsOpenImmersion.isPullback_lift_id f V.ι hfac
  let : IsAffine (pullback V.ι f) := IsAffine.of_isIso hp.isoPullback.inv
  let P := pullback f (q ≫ V.ι)
  let e : P ≅ pullback q (pullback.fst V.ι f) :=
    pullbackSymmetry f (q ≫ V.ι) ≪≫ (pullbackRightPullbackFstIso V.ι f q).symm
  let : IsAffine P := IsAffine.of_isIso e.hom
  let Z := P.nilradical.subscheme
  let h : Z ⟶ P := P.nilradical.subschemeι
  have hred :=
    reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism P
  let : IsReduced Z := hred.1
  let : IsClosedImmersion h := hred.2.1
  let : IsAffine Z := isAffine_of_isAffineHom h
  let : Surjective h := hred.2.2.1
  refine ⟨S, Z, q, h, inferInstance, inferInstance, inferInstance, inferInstance,
    hq, inferInstance, ?_⟩
  infer_instance

end AlgebraicGeometry
