/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Restricting morphisms near the image of an open immersion

- `AlgebraicGeometry.isIso_morphismRestrict_of_le_opensRange`: an open immersion restricted
  to an open contained in its image is an isomorphism.
- `AlgebraicGeometry.morphismRestrict_comp_comp_image_iff`: for open immersions `ψ` and `e`, a
  property respecting isomorphisms holds for the restriction of `ψ ≫ q ≫ e` over `e(V)` if
  and only if it holds for `q ∣_ V`, provided `q⁻¹(V)` lies in the image of `ψ`.
- `AlgebraicGeometry.etale_morphismRestrict_of_le`: `f ∣_ V` is étale if `f` is étale on an
  open containing `f⁻¹(V)`.
- `AlgebraicGeometry.etale_basicOpen_ι_comp_SpecMap`: étaleness of `Spec.map f` on a basic open
  `D(s)` follows from étaleness of the localized ring map.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An open immersion restricted to an open contained in its image is an isomorphism. -/
lemma isIso_morphismRestrict_of_le_opensRange {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {V : Y.Opens} (hV : V ≤ f.opensRange) : IsIso (f ∣_ V) := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun y ↦ ?_⟩⟩
  obtain ⟨x, hx⟩ := hV y.2
  refine ⟨⟨x, ?_⟩, Subtype.ext ?_⟩
  · rw [Scheme.Hom.mem_preimage, hx]
    exact y.2
  · rw [morphismRestrict_base_coe]
    exact hx

/-- Let `ψ` and `e` be open immersions and let `V` be an open of the target of `q` such that
`q⁻¹(V)` lies in the image of `ψ`. A property of morphisms respecting isomorphisms holds for the
restriction of `ψ ≫ q ≫ e` over `e(V)` if and only if it holds for `q ∣_ V`. -/
lemma morphismRestrict_comp_comp_image_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {U Y Z T : Scheme.{u}} (ψ : U ⟶ Y) [IsOpenImmersion ψ] (q : Y ⟶ Z) (e : Z ⟶ T)
    [IsOpenImmersion e] {V : Z.Opens} (hV : q ⁻¹ᵁ V ≤ ψ.opensRange) :
    P ((ψ ≫ q ≫ e) ∣_ (e ''ᵁ V)) ↔ P (q ∣_ V) := by
  have : IsIso (ψ ∣_ ((q ≫ e) ⁻¹ᵁ e ''ᵁ V)) := isIso_morphismRestrict_of_le_opensRange ψ
    (by rwa [Scheme.Hom.comp_preimage, e.preimage_image_eq])
  have : IsIso (e ∣_ e ''ᵁ V) :=
    isIso_morphismRestrict_of_le_opensRange e (e.image_le_opensRange V)
  rw [morphismRestrict_comp, P.cancel_left_of_respectsIso, morphismRestrict_comp,
    P.cancel_right_of_respectsIso]
  exact P.arrow_mk_iso_iff (morphismRestrictEq q (e.preimage_image_eq V))

/-- If `f` is étale on an open `O` containing `f⁻¹(V)`, then `f ∣_ V` is étale. -/
lemma etale_morphismRestrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y) {O : X.Opens}
    [Etale (O.ι ≫ f)] {V : Y.Opens} (hV : f ⁻¹ᵁ V ≤ O) : Etale (f ∣_ V) := by
  have : Etale (f ∣_ V ≫ V.ι) := by
    rw [morphismRestrict_ι, ← X.homOfLE_ι hV, Category.assoc]
    infer_instance
  exact Etale.of_comp _ V.ι

/-- Let `f : R ⟶ S` be a ring map and `s ∈ S`. If `R ⟶ S[1/s]` is étale, then `Spec S ⟶ Spec R`
is étale on the basic open `D(s)`. -/
lemma etale_basicOpen_ι_comp_SpecMap {R S : CommRingCat.{u}} (f : R ⟶ S) (s : S)
    (h : ((algebraMap S (Localization.Away s)).comp f.hom).Etale) :
    Etale (Scheme.Opens.ι (X := Spec S) (PrimeSpectrum.basicOpen s) ≫ Spec.map f) := by
  rw [← basicOpenIsoSpecAway_hom_SpecMap, Category.assoc, ← Spec.map_comp]
  have := (HasRingHomProperty.Spec_iff (P := @Etale)
    (φ := f ≫ CommRingCat.ofHom (algebraMap S (Localization.Away s)))).mpr h
  infer_instance

end AlgebraicGeometry
