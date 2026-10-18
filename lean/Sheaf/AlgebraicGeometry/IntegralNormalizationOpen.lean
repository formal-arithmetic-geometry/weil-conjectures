/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S8
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDenseOpenIso
import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Normalization of an integral open subscheme

Source: Stacks Project, Morphisms, Tags 035K, 035Q and 0BXC.
(blueprint: lem-weil-pbc-integral-normalization-open)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem normalization_normal (C : Scheme.{u}) [IsIntegral C] :
    ∀ x : C.normalization, IsDomain (C.normalization.presheaf.stalk x) ∧
      IsIntegrallyClosed (C.normalization.presheaf.stalk x) := by
  intro x
  have : IsRegular (Spec C.functionField) := IsRegular.spec_field C.functionField
  exact ⟨inferInstance,
    C.fromSpecFunctionField.isIntegrallyClosed_stalk_normalization
      (fun z ↦ IsRegular.isIntegrallyClosed_stalk z) x⟩

private theorem restrict_iso_of_le {A B : Scheme.{u}} (f : A ⟶ B)
    (U V : B.Opens) (hUV : U ≤ V) [IsIso (f ∣_ V)] : IsIso (f ∣_ U) := by
  have hsq : IsPullback (A.homOfLE (f.preimage_mono hUV)) (f ∣_ U)
      (f ∣_ V) (B.homOfLE hUV) := by
    apply IsPullback.of_right (t := (isPullback_morphismRestrict f V).flip)
    · simpa using (isPullback_morphismRestrict f U).flip
    · exact (morphismRestrict_homOfLE f U V hUV).symm
  exact hsq.isIso_snd_of_isIso

/-- The normalization of a nonempty integral open subscheme is the corresponding open in the
normalization of the ambient integral finite type scheme.
Source: Stacks Project, Morphisms, Tags 035K, 035Q and 0BXC.
(blueprint: lem-weil-pbc-integral-normalization-open)

Proof: base change the finite normalization of C along the open immersion a. Its source N is a
nonempty integral open of the normal integral scheme C-normalization, so is normal. Both N and
the normalization of D are finite over D and are isomorphisms above some nonempty open: intersect
the inverse image of an isomorphism open for the normalization of C with an isomorphism open for
that of D. The inverse images of this open in both integral sources are nonempty and hence dense.
The finite-normal comparison theorem extends their common isomorphism to an isomorphism over D.
Compose with the open projection from N to C-normalization. Its image is nonempty open in an
integral scheme, and therefore dense. The pullback equation gives commutativity. -/
theorem exists_integral_normalization_open
    (k : Type u) [Field k] (C D : Scheme.{u}) [IsIntegral C] [IsIntegral D]
    (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (a : D ⟶ C) [IsOpenImmersion a] :
    ∃ j : D.normalization ⟶ C.normalization,
      IsOpenImmersion j ∧ DenseRange j ∧ j ≫ C.fromNormalization = D.fromNormalization ≫ a := by
  have : IsFinite C.fromNormalization := C.isFinite_fromNormalization_of_locallyOfFiniteType f
  have : IsFinite D.fromNormalization :=
    D.isFinite_fromNormalization_of_locallyOfFiniteType (a ≫ f)
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian D := isLocallyNoetherian_of_isOpenImmersion a
  let N := pullback C.fromNormalization a
  let r : N ⟶ C.normalization := pullback.fst C.fromNormalization a
  let p : N ⟶ D := pullback.snd C.fromNormalization a
  have : Nonempty N := (p.surjective (Classical.choice (inferInstance : Nonempty D))).nonempty
  have : IsIntegral N := isIntegral_of_isOpenImmersion r
  have hnormalN : ∀ x : N, IsDomain (N.presheaf.stalk x) ∧
      IsIntegrallyClosed (N.presheaf.stalk x) := by
    intro x
    obtain ⟨_, hclosed⟩ := normalization_normal C (r x)
    have : IsIntegrallyClosed (C.normalization.presheaf.stalk (r x)) := hclosed
    exact ⟨inferInstance,
      IsIntegrallyClosed.of_equiv (asIso (r.stalkMap x)).commRingCatIsoToRingEquiv⟩
  obtain ⟨UC, hUC, hCiso⟩ := C.exists_isIso_fromNormalization_restrict f
  obtain ⟨UD, hUD, hDiso⟩ := D.exists_isIso_fromNormalization_restrict (a ≫ f)
  have : IsIso (C.fromNormalization ∣_ UC) := hCiso
  have : IsIso (D.fromNormalization ∣_ UD) := hDiso
  have hpiso : IsIso (p ∣_ (a ⁻¹ᵁ UC)) := by
    have hsq := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback C.fromNormalization a)
      (US := UC) (UT := a ⁻¹ᵁ UC) (UX := C.fromNormalization ⁻¹ᵁ UC)
      le_rfl le_rfl (UY := p ⁻¹ᵁ (a ⁻¹ᵁ UC)) (by
        simp only [p, ← Scheme.Hom.comp_preimage, ← pullback.condition, inf_idem])
    have hres : IsIso (C.fromNormalization.resLE UC
        (C.fromNormalization ⁻¹ᵁ UC) le_rfl) := by
      simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using hCiso
    simpa only [p, Scheme.Hom.resLE_eq_morphismRestrict] using
      hsq.isIso_snd_of_isIso hres
  let U := UD ⊓ a ⁻¹ᵁ UC
  have : IsIso (p ∣_ U) := restrict_iso_of_le p U _ inf_le_right
  have : IsIso (D.fromNormalization ∣_ U) :=
    restrict_iso_of_le D.fromNormalization U UD inf_le_left
  have hda : DenseRange a := a.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty a)
  have hU : (U : Set D).Nonempty := by
    have hpre : (a ⁻¹ᵁ UC : Set D).Nonempty := by
      obtain ⟨x, hx⟩ := hda.exists_mem_open UC.isOpen hUC
      exact ⟨x, hx⟩
    simpa only [U, TopologicalSpace.Opens.coe_inf, Set.inter_comm] using
      (UD.isOpen.dense hUD).inter_open_nonempty _ (a ⁻¹ᵁ UC).isOpen hpre
  have hdense (A : Scheme.{u}) [IsIntegral A] (g : A ⟶ D) [Surjective g] :
      Dense (g ⁻¹ᵁ U : Set A) := by
    apply (g ⁻¹ᵁ U).isOpen.dense
    obtain ⟨x, hx⟩ := hU
    obtain ⟨y, rfl⟩ := g.surjective x
    exact ⟨y, hx⟩
  let e := asIso (D.fromNormalization ∣_ U) ≪≫ (asIso (p ∣_ U)).symm
  obtain ⟨e', he'⟩ := Scheme.finite_normal_iso_of_dense_open D.fromNormalization p
    (normalization_normal D) hnormalN U (hdense _ _) (hdense _ _) e (by simp [e])
  let j := e'.hom ≫ r
  have : IsOpenImmersion j := inferInstance
  refine ⟨j, inferInstance, ?_, ?_⟩
  · exact j.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty j)
  · simp only [j, Category.assoc, r, pullback.condition]
    exact congrArg (fun t ↦ t ≫ a) he'

end AlgebraicGeometry
