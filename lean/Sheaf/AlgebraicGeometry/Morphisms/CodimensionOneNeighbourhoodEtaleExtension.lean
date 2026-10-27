/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Localization.Away.Basic

import WeilConjectures.AlgebraicGeometry.Morphisms.RegularCodimensionTwoEtaleExtension
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Extending a finite cover from codimension-one source neighbourhoods

Source: Travaux de Gabber, IX Proposition 2.1(i), pp.133-134; Stacks Project,
Tags 0BMA and 0EY7 (blueprint: lem-sfb-codimension-one-neighbourhood-etale-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem etale_of_source_neighbourhoods {X Y : Scheme.{u}} (q : X ⟶ Y)
    (h : ∀ x : X, ∃ A : X.Opens, x ∈ A ∧ Etale (A.ι ≫ q)) : Etale q := by
  choose A hx hA using h
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale) A
  · exact top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  · exact hA

/-- The complement of the image of the non-etale remainder gives an open over which
this finite cover is etale, and its restriction extends to a finite etale cover of the base.
The base open `PrimeSpectrum.basicOpen f` is the canonical open `Spec B[1/f]`, by
`Hom.opensRange_localizationAway`. The chosen neighbourhood family is indexed by the
points of the source above height-one boundary primes; proof arguments merely restrict
this indexing and impose no condition on other source points.

Source: Travaux de Gabber, IX Proposition 2.1(i), pp.133-134, regular extension
subargument; Stacks Project, Tags 0BMA and 0EY7.
(blueprint: lem-sfb-codimension-one-neighbourhood-etale-extension)

Proof:
1. The inverse image of D(f) is etale over the base by etale composition with its open
   immersion. Every selected neighbourhood is etale over the base. Their union O is
   therefore etale over the base, by etaleness being local on the source
   (lem-weil-pbc-etale-composition-cancellation, lem-weil-pbc-etale-local-on-source).
2. Finiteness makes the image of the closed complement of O closed. Its complement W
   is open, and x belongs to W exactly when its whole fibre lies in O. This gives
   D(f) contained in W (lem-weil-pbc-finite-closed-map-finite-fibres).
3. A height-one point not containing f lies in D(f); otherwise each point of its fibre
   belongs to its selected neighbourhood. Thus every height-one point belongs to W,
   including points with empty fibre. The zero prime belongs to D(f), since f is nonzero.
4. Any prime outside W is neither zero nor height one. Choose a nonzero prime strictly
   below it. Localization preserves the resulting length-two chain: contraction of an
   extended prime below the localization prime is the original prime. Hence the ambient
   stalk has dimension at least two and is regular, by regularity of B. The affine base
   is Noetherian (lem-weil-pbc-spec-domain-stalks-function-field, the localization-at-prime,
   regular-ring and Krull-dimension definitions).
5. The restriction to W is finite by base change and etale because its source lies in O;
   its source is the same open subscheme as the base change of O to W
   (lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-etale-scheme-base-change).
6. Apply lem-sbc-regular-codimension-two-etale-extension to this finite etale restriction,
   using the ambient stalk condition of step 4. Invert its comparison to obtain the
   stated isomorphism from the restriction of the new model H to that of the original N.
7. Pull this comparison back to D(f), using its inclusion in W. Associativity of fibre
   products gives the final isomorphism over D(f) (def-pc-fibre-product). No normality of
   C or henselianity of B is used, and H is not identified with the original N. -/
theorem exists_finite_etale_model_of_codimension_one_neighbourhoods
    (B C : Type u) [CommRing B] [IsDomain B] [IsRegularRing B]
    [CommRing C] [Algebra B C] [Module.Finite B C]
    (f : B) (hf : f ≠ 0)
    (hU : Etale ((Spec.map (CommRingCat.ofHom (algebraMap B C))) ∣_ PrimeSpectrum.basicOpen f))
    (V : (z : Spec (CommRingCat.of C)) →
      ((Spec.map (CommRingCat.ofHom (algebraMap B C))) z).asIdeal.height = 1 ∧
        f ∈ ((Spec.map (CommRingCat.ofHom (algebraMap B C))) z).asIdeal →
      (Spec (CommRingCat.of C)).Opens)
    (hV : ∀ (z : Spec (CommRingCat.of C))
      (hz : ((Spec.map (CommRingCat.ofHom (algebraMap B C))) z).asIdeal.height = 1 ∧
        f ∈ ((Spec.map (CommRingCat.ofHom (algebraMap B C))) z).asIdeal), z ∈ V z hz)
    (hVet : ∀ (z : Spec (CommRingCat.of C))
      (hz : ((Spec.map (CommRingCat.ofHom (algebraMap B C))) z).asIdeal.height = 1 ∧
        f ∈ ((Spec.map (CommRingCat.ofHom (algebraMap B C))) z).asIdeal),
      Etale ((V z hz).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap B C))))
    (O : (Spec (CommRingCat.of C)).Opens)
    (hO : O = (Spec.map (CommRingCat.ofHom (algebraMap B C))) ⁻¹ᵁ PrimeSpectrum.basicOpen f ⊔
      ⨆ (z : Spec (CommRingCat.of C))
        (hz : ((Spec.map (CommRingCat.ofHom (algebraMap B C))) z).asIdeal.height = 1 ∧
          f ∈ ((Spec.map (CommRingCat.ofHom (algebraMap B C))) z).asIdeal), V z hz) :
    ∃ W : (Spec (CommRingCat.of B)).Opens,
      (W : Set (Spec (CommRingCat.of B))) =
        ((Spec.map (CommRingCat.ofHom (algebraMap B C))) '' (O : Set (Spec (CommRingCat.of C)))ᶜ)ᶜ ∧
      PrimeSpectrum.basicOpen f ≤ W ∧
      (∀ x : Spec (CommRingCat.of B), x.asIdeal.height = 1 → x ∈ W) ∧
      IsFinite ((Spec.map (CommRingCat.ofHom (algebraMap B C))) ∣_ W) ∧
      Etale ((Spec.map (CommRingCat.ofHom (algebraMap B C))) ∣_ W) ∧
      (∃ (H : Scheme.{u}) (p : H ⟶ Spec (CommRingCat.of B)), IsFinite p ∧ Etale p ∧
        (∃ e : pullback p W.ι ≅ pullback (Spec.map (CommRingCat.ofHom (algebraMap B C))) W.ι,
          e.hom ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap B C))) W.ι =
            pullback.snd p W.ι) ∧
        ∃ e : pullback p
            (Scheme.Opens.ι (X := Spec (CommRingCat.of B)) (PrimeSpectrum.basicOpen f)) ≅
            pullback (Spec.map (CommRingCat.ofHom (algebraMap B C)))
              (Scheme.Opens.ι (X := Spec (CommRingCat.of B)) (PrimeSpectrum.basicOpen f)),
          e.hom ≫
              pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap B C)))
                (Scheme.Opens.ι (X := Spec (CommRingCat.of B)) (PrimeSpectrum.basicOpen f)) =
            pullback.snd p
              (Scheme.Opens.ι (X := Spec (CommRingCat.of B)) (PrimeSpectrum.basicOpen f))) ∧
      ∀ x : Spec (CommRingCat.of B), x ∉ W →
        IsRegularLocalRing ((Spec (CommRingCat.of B)).presheaf.stalk x) ∧
        (2 : WithBot ℕ∞) ≤ ringKrullDim ((Spec (CommRingCat.of B)).presheaf.stalk x) := by
  classical
  let q := Spec.map (CommRingCat.ofHom (algebraMap B C))
  let U : (Spec (CommRingCat.of B)).Opens := PrimeSpectrum.basicOpen f
  have hq : IsFinite q := (IsFinite.SpecMap_iff _).mpr (by
    exact RingHom.finite_algebraMap.mpr inferInstance)
  let W : (Spec (CommRingCat.of B)).Opens :=
    ⟨(q '' (O : Set (Spec (CommRingCat.of C)))ᶜ)ᶜ,
      (q.isClosedMap _ O.isOpen.isClosed_compl).isOpen_compl⟩
  have hWU : U ≤ W := by
    intro x hx
    rintro ⟨z, hz, rfl⟩
    apply hz
    rw [hO]
    exact Or.inl hx
  have hWone : ∀ x : Spec (CommRingCat.of B), x.asIdeal.height = 1 → x ∈ W := by
    intro x hx
    by_cases hfx : f ∉ x.asIdeal
    · exact hWU hfx
    · push Not at hfx
      rintro ⟨z, hz, hzx⟩
      apply hz
      have hh : (q z).asIdeal.height = 1 ∧ f ∈ (q z).asIdeal := by
        rw [hzx]
        exact ⟨hx, hfx⟩
      rw [hO]
      exact Or.inr (TopologicalSpace.Opens.mem_iSup.mpr
        ⟨z, TopologicalSpace.Opens.mem_iSup.mpr ⟨hh, hV z hh⟩⟩)
  have hpre : q ⁻¹ᵁ W ≤ O := by
    intro z hz
    by_contra hn
    exact hz ⟨z, hn, rfl⟩
  have hgood : ∀ z : Spec (CommRingCat.of C), z ∈ O →
      ∃ A : (Spec (CommRingCat.of C)).Opens, z ∈ A ∧ Etale (A.ι ≫ q) := by
    intro z hz
    rw [hO] at hz
    rcases hz with hz | hz
    · refine ⟨q ⁻¹ᵁ U, hz, ?_⟩
      have : Etale (q ∣_ U) := hU
      rw [← morphismRestrict_ι]
      infer_instance
    · obtain ⟨w, hz⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
      obtain ⟨hw, hz⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
      exact ⟨V w hw, hz, hVet w hw⟩
  have het : Etale (q ∣_ W) := by
    have hcomp : Etale ((q ⁻¹ᵁ W).ι ≫ q) := by
      apply etale_of_source_neighbourhoods
      intro z
      obtain ⟨A, hz, hA⟩ := hgood z.val (hpre z.property)
      let j := (q ⁻¹ᵁ W).ι
      refine ⟨j ⁻¹ᵁ A, hz, ?_⟩
      have : Etale (A.ι ≫ q) := hA
      rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
      infer_instance
    have : Etale ((q ∣_ W) ≫ W.ι) := by rwa [morphismRestrict_ι]
    exact Etale.of_comp _ W.ι
  have hboundary : ∀ x : Spec (CommRingCat.of B), x ∉ W →
      IsRegularLocalRing ((Spec (CommRingCat.of B)).presheaf.stalk x) ∧
      (2 : WithBot ℕ∞) ≤ ringKrullDim ((Spec (CommRingCat.of B)).presheaf.stalk x) := by
    intro x hx
    refine ⟨?_, ?_⟩
    · exact IsRegularLocalRing.of_ringEquiv
        (Spec.stalkIso (CommRingCat.of B) x).symm.commRingCatIsoToRingEquiv
    · rw [ringKrullDim_stalk_eq_coheight, ← idealHeight_eq_coheight]
      apply WithBot.coe_le_coe.mpr
      have hzero : x.asIdeal.height ≠ 0 := by
        intro h
        apply hx
        apply hWU
        change f ∉ x.asIdeal
        rw [Ideal.height_eq_zero_iff_eq_bot.mp h]
        simpa using hf
      have hone : x.asIdeal.height ≠ 1 := fun h ↦ hx (hWone x h)
      exact (ENat.add_one_le_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mpr
        (lt_of_le_of_ne (Order.one_le_iff_ne_zero.mpr hzero) (Ne.symm hone))
  refine ⟨W, rfl, hWU, hWone, inferInstance, het, ?_, hboundary⟩
  have : Etale (q ∣_ W) := het
  obtain ⟨H, p, hp, hpet, e, he⟩ :=
    exists_finite_etale_extension_of_regular_codimension_two_boundary W hboundary (q ∣_ W)
  let ew : pullback p W.ι ≅ pullback q W.ι :=
    pullbackRestrictIsoRestrict p W ≪≫ e.symm ≪≫ (pullbackRestrictIsoRestrict q W).symm
  have he' : e.inv ≫ q ∣_ W = p ∣_ W := by rw [← he]; simp
  have hew : ew.hom ≫ pullback.snd q W.ι = pullback.snd p W.ι := by
    change (pullbackRestrictIsoRestrict p W).hom ≫ e.inv ≫
      (pullbackRestrictIsoRestrict q W).inv ≫ pullback.snd q W.ι = _
    change (pullbackRestrictIsoRestrict p W).hom ≫ e.inv ≫ q ∣_ W = _
    rw [he', pullbackRestrictIsoRestrict_hom_morphismRestrict]
  refine ⟨H, p, hp, hpet, ⟨ew, hew⟩, ?_⟩
  let i := (Spec (CommRingCat.of B)).homOfLE hWU
  have hi : i ≫ W.ι = U.ι := by simp [i]
  let a : pullback (pullback.snd p W.ι) i ≅ pullback p U.ι :=
    pullbackLeftPullbackSndIso p W.ι i ≪≫ pullback.congrHom rfl hi
  let b : pullback (pullback.snd q W.ι) i ≅ pullback q U.ι :=
    pullbackLeftPullbackSndIso q W.ι i ≪≫ pullback.congrHom rfl hi
  let m := pullback.map (pullback.snd p W.ι) i (pullback.snd q W.ι) i
    ew.hom (𝟙 _) (𝟙 _) (by simpa using hew.symm) (by simp)
  have : IsIso m := inferInstance
  refine ⟨a.symm ≪≫ asIso m ≪≫ b, ?_⟩
  change (a.inv ≫ m ≫ b.hom) ≫ pullback.snd q U.ι = pullback.snd p U.ι
  simp [a, b, m, pullback.map, Category.assoc]

end AlgebraicGeometry.Scheme
