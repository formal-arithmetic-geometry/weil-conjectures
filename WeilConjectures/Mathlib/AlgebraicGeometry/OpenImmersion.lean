/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.Topology.Maps.Basic

/-!
# Open immersions respect open immersions on the right

The `MorphismProperty.RespectsRight` instance for open immersions of schemes.

We also record the range of the base change of an open immersion
(`AlgebraicGeometry.range_snd_of_isPullback`) and the form of
`AlgebraicGeometry.isIso_morphismRestrict_of_range_eq` in which the modification layer
produces its data: a partial section `m` of `ψ` whose composite `m ≫ ψ` is an open
immersion and whose range is the full inverse image of the range of `m ≫ ψ` exhibits
`ψ` as an isomorphism over that range
(`AlgebraicGeometry.isIso_morphismRestrict_opensRange_of_range_eq`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

instance : MorphismProperty.RespectsRight @IsOpenImmersion @IsOpenImmersion :=
  ⟨fun i hi f hf ↦ by
    have : IsOpenImmersion i := hi
    have : IsOpenImmersion f := hf
    infer_instance⟩

section RestrictOfSection

variable {T X : Scheme.{u}} (ψ : T ⟶ X) (V : X.Opens) (v : V.toScheme ⟶ T)

/-- **A morphism with an open section covering the inverse image is an isomorphism over
the open**: if `v` is an open immersion lifting the inclusion of `V` along `ψ` whose
range is the whole inverse image of `V`, then `ψ` restricts to an isomorphism over `V`.
This produces the isomorphism over `V` of the graph extension of a compactification
(Stacks Project Tag 0F3Z; revised blueprint
`lemma:nagata-scheme-image-partial-section`). -/
theorem isIso_morphismRestrict_of_range_eq [IsOpenImmersion v] (hv : v ≫ ψ = V.ι)
    (hrange : ((ψ ⁻¹ᵁ V : T.Opens) : Set T) = Set.range v) : IsIso (ψ ∣_ V) := by
  -- lift `v` to the inverse image of `V`
  have hsub : Set.range v ⊆ Set.range (ψ ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι]
    exact hrange.ge
  obtain ⟨v', hv'⟩ : ∃ v' : V.toScheme ⟶ (ψ ⁻¹ᵁ V).toScheme, v' ≫ (ψ ⁻¹ᵁ V).ι = v :=
    ⟨IsOpenImmersion.lift (ψ ⁻¹ᵁ V).ι v hsub, IsOpenImmersion.lift_fac _ _ _⟩
  have hOI : IsOpenImmersion (v' ≫ (ψ ⁻¹ᵁ V).ι) := by
    rw [hv']
    infer_instance
  have hOIv' : IsOpenImmersion v' := IsOpenImmersion.of_comp v' (ψ ⁻¹ᵁ V).ι
  -- the lift is surjective, since the range of `v` is the whole inverse image
  have hsurj : Function.Surjective v' := by
    intro w
    have hw : (ψ ⁻¹ᵁ V).ι w ∈ Set.range v := by
      rw [← hrange, ← Scheme.Opens.range_ι]
      exact ⟨w, rfl⟩
    obtain ⟨t, ht⟩ := hw
    refine ⟨t, (ψ ⁻¹ᵁ V).ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hv', ht]
  -- a surjective open immersion is an isomorphism, and it inverts `ψ ∣_ V`
  have hepi : Epi v'.base := (TopCat.epi_iff_surjective _).mpr hsurj
  have hIsov' : IsIso v' := IsOpenImmersion.isIso v'
  have hcomp : v' ≫ (ψ ∣_ V) = 𝟙 V.toScheme := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hv', hv,
      Category.id_comp]
  have : IsIso (v' ≫ (ψ ∣_ V)) := by
    rw [hcomp]
    infer_instance
  exact IsIso.of_isIso_comp_left v' (ψ ∣_ V)

end RestrictOfSection

section PullbackRange

/-- **The range of the base change of an open immersion**: in a cartesian square whose
left vertical leg `f` is an open immersion, the parallel leg `snd` has range the inverse
image of the range of `f`. -/
theorem range_snd_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} [IsOpenImmersion f] (h : IsPullback fst snd f g) :
    Set.range snd = g ⁻¹' Set.range f := by
  have hsurj : Function.Surjective ⇑h.isoPullback.hom := by
    have := (Scheme.homeoOfIso h.isoPullback).surjective
    rwa [Scheme.coe_homeoOfIso] at this
  have hcomp : snd = h.isoPullback.hom ≫ Limits.pullback.snd f g :=
    (h.isoPullback_hom_snd).symm
  rw [hcomp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ, IsOpenImmersion.range_pullbackSnd]
  rfl

end PullbackRange

section RestrictOfSectionRange

/-- **A partial section identifies an isomorphism locus**: if `m` is an open immersion
whose composite `j := m ≫ ψ` is again an open immersion and whose range is the full
inverse image of the range of `j`, then `ψ` restricts to an isomorphism over the range
of `j`. This is `AlgebraicGeometry.isIso_morphismRestrict_of_range_eq` in the form in
which the modification layer produces its data. -/
theorem isIso_morphismRestrict_opensRange_of_range_eq {W T X : Scheme.{u}} (ψ : T ⟶ X)
    (m : W ⟶ T) [IsOpenImmersion m] [IsOpenImmersion (m ≫ ψ)]
    (hrange : Set.range m = ψ ⁻¹' Set.range (m ≫ ψ)) :
    IsIso (ψ ∣_ (m ≫ ψ).opensRange) := by
  have hsurj : Function.Surjective ⇑(m ≫ ψ).isoOpensRange.inv := by
    have := (Scheme.homeoOfIso (m ≫ ψ).isoOpensRange.symm).surjective
    rwa [Scheme.coe_homeoOfIso] at this
  refine isIso_morphismRestrict_of_range_eq ψ (m ≫ ψ).opensRange
    ((m ≫ ψ).isoOpensRange.inv ≫ m) ?_ ?_
  · rw [Category.assoc]
    exact (Iso.inv_comp_eq _).mpr (Scheme.Hom.isoOpensRange_hom_ι (m ≫ ψ)).symm
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr hsurj, Set.image_univ, hrange]
    rfl

end RestrictOfSectionRange

/-- An open immersion whose range is an open `B` is an isomorphism onto `B`. -/
lemma exists_isIso_lift_of_mem_iff {Y Z : Scheme.{u}} (m : Z ⟶ Y)
    (hm : IsOpenImmersion m) {B : Y.Opens} (hB : ∀ y, (∃ z, m z = y) ↔ y ∈ B) :
    ∃ m' : Z ⟶ B.toScheme, IsIso m' ∧ m' ≫ B.ι = m := by
  have := hm
  have hsub : Set.range m.base ⊆ Set.range B.ι.base := by
    rintro - ⟨z, rfl⟩
    exact ⟨⟨m z, (hB _).mp ⟨z, rfl⟩⟩, rfl⟩
  refine ⟨IsOpenImmersion.lift B.ι m hsub, ?_, IsOpenImmersion.lift_fac _ _ _⟩
  have hfac : IsOpenImmersion.lift B.ι m hsub ≫ B.ι = m := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (IsOpenImmersion.lift B.ι m hsub) := by
    have h1 : IsOpenImmersion (IsOpenImmersion.lift B.ι m hsub ≫ B.ι) := by
      rw [hfac]; infer_instance
    exact IsOpenImmersion.of_comp _ B.ι
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
  refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun t ↦ ?_)
  obtain ⟨z, hz⟩ := (hB t.1).mpr t.2
  refine ⟨z, B.ι.isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, hfac]
  exact hz

/-- A set in a scheme is closed as soon as its preimage under each member of a jointly
surjective family of open immersions is closed. -/
lemma Scheme.isClosed_of_openCover {Q : Scheme.{u}} {κ : Type*} {Z : κ → Scheme.{u}}
    (q : ∀ k, Z k ⟶ Q) [∀ k, IsOpenImmersion (q k)] (hcov : ∀ x : Q, ∃ k y, q k y = x)
    {s : Set Q} (hs : ∀ k, IsClosed ((q k).base ⁻¹' s)) : IsClosed s :=
  isClosed_of_isOpenEmbedding_cover (fun k ↦ (q k).base)
    (fun k ↦ (q k).isOpenEmbedding) hcov hs

end AlgebraicGeometry
