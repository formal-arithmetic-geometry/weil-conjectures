/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # Common principal charts for an open immersion into a quasi-affine scheme

Source: Stacks Project, `properties.tex`, Tag 0ARY,
`lemma-cartesian-diagram-quasi-affine`, common charts and coverage
(blueprint: lem-a1-quasi-affine-open-principal-comparison-cover).

The charts are indexed by all global sections of the target whose distinguished
opens in its affinization lie inside the image of the source.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An open inside a quasi-affine scheme has a common affine principal cover with
its image in the target affinization. The isomorphisms are induced by the given
maps, as expressed by their compatibility with the open inclusions. No
quasi-compactness assumption is imposed on `U`.

Source: Stacks Project, `properties.tex`, Tag 0ARY,
`lemma-cartesian-diagram-quasi-affine`, common charts and coverage
(blueprint: lem-a1-quasi-affine-open-principal-comparison-cover).

Proof:
1. By lem-trf-quasi-affine-canonical-affine-embedding (Tag 01P9), the
   canonical map of V is an open immersion. Both composites to Spec Γ(V, ⊤)
   induce u.appTop on global sections, so the bijection in
   lem-weil-pbc-morphism-into-affine-scheme makes them equal.
2. Open immersions identify their sources with open images
   (def-weil-open-immersion). Thus H is open. The distinguished-open basis
   (lem-weil-pbc-spec-localization-away-basic-open, clause (i)) covers H by
   exactly the D(g) contained in H.
3. For each such g, the preimage clause of
   lem-weil-pbc-morphism-into-affine-scheme identifies V_g with the preimage
   of D(g). Since D(g) lies in the image of the canonical open immersion,
   restricting that immersion gives V_g ≅ D(g). Its injectivity also gives
   V_g ⊆ u(U). Principal localization
   (lem-weil-pbc-principal-localization-open-immersion) identifies D(g)
   with Spec B_g, so V_g is affine (def-pc-scheme).
4. With f = u.appTop g, lem-weil-pbc-basic-open-pullback gives
   U_f = u⁻¹(V_g). The preimage clause of
   lem-weil-pbc-morphism-into-affine-scheme applied to Spec.map u.appTop
   gives the inverse image D(f) of D(g) (def-weil-affine-spectrum).
5. Restrict the inverse of u onto its image to V_g. By step 4 this inverse
   lands in U_f. Both inverse identities restrict, giving the displayed
   isomorphism induced by u. It also proves U_f affine. For any x in U,
   step 2 supplies g with j_V(u(x)) in D(g); steps 3 and 4 then put x in
   U_f. Hence these affine opens cover U. -/
theorem quasiAffine_open_principal_comparison_cover
    {U V : Scheme.{u}} (u : U ⟶ V) [IsOpenImmersion u] [V.IsQuasiAffine] :
    IsOpenImmersion V.toSpecΓ ∧
    U.toSpecΓ ≫ Spec.map u.appTop = u ≫ V.toSpecΓ ∧
    IsOpen (Set.range (u ≫ V.toSpecΓ)) ∧
    Set.range (u ≫ V.toSpecΓ) =
      ⋃ (g : Γ(V, ⊤))
        (_ : ((PrimeSpectrum.basicOpen g).carrier : Set (Spec Γ(V, ⊤))) ⊆
          Set.range (u ≫ V.toSpecΓ)),
        ((PrimeSpectrum.basicOpen g).carrier : Set (Spec Γ(V, ⊤))) ∧
    (∀ g : Γ(V, ⊤),
      ((PrimeSpectrum.basicOpen g).carrier : Set (Spec Γ(V, ⊤))) ⊆
        Set.range (u ≫ V.toSpecΓ) →
      (V.basicOpen g : Set V) ⊆ Set.range u ∧
      IsAffineOpen (V.basicOpen g) ∧
      (∃ e : (V.basicOpen g).toScheme ≅
          Scheme.Opens.toScheme (X := Spec Γ(V, ⊤)) (PrimeSpectrum.basicOpen g),
        e.hom ≫ Scheme.Opens.ι (X := Spec Γ(V, ⊤)) (PrimeSpectrum.basicOpen g) =
          (V.basicOpen g).ι ≫ V.toSpecΓ) ∧
      U.basicOpen (u.appTop g) = u ⁻¹ᵁ V.basicOpen g ∧
      Spec.map u.appTop ⁻¹ᵁ PrimeSpectrum.basicOpen g =
        PrimeSpectrum.basicOpen (u.appTop g) ∧
      (∃ e : (U.basicOpen (u.appTop g)).toScheme ≅ (V.basicOpen g).toScheme,
        e.hom ≫ (V.basicOpen g).ι = (U.basicOpen (u.appTop g)).ι ≫ u) ∧
      IsAffineOpen (U.basicOpen (u.appTop g))) ∧
    ∀ x : U, ∃ g : Γ(V, ⊤),
      ((PrimeSpectrum.basicOpen g).carrier : Set (Spec Γ(V, ⊤))) ⊆
        Set.range (u ≫ V.toSpecΓ) ∧ x ∈ U.basicOpen (u.appTop g) := by
  have hH := IsOpenImmersion.isOpen_range (u ≫ V.toSpecΓ)
  have hb : ∀ z ∈ Set.range (u ≫ V.toSpecΓ), ∃ g : Γ(V, ⊤),
      z ∈ PrimeSpectrum.basicOpen g ∧
      ((PrimeSpectrum.basicOpen g).carrier : Set (Spec Γ(V, ⊤))) ⊆
        Set.range (u ≫ V.toSpecΓ) := by
    intro z hz
    obtain ⟨_, ⟨g, rfl⟩, hzg, hg⟩ :=
      (PrimeSpectrum.isTopologicalBasis_basic_opens (R := Γ(V, ⊤))).exists_subset_of_mem_open
        hz hH
    exact ⟨g, hzg, hg⟩
  refine ⟨inferInstance, (toSpecΓ_naturality u).symm, hH, ?_, ?_, ?_⟩
  · ext z
    simp only [Set.mem_iUnion]
    exact ⟨fun hz ↦ let ⟨g, hzg, hg⟩ := hb z hz; ⟨g, hg, hzg⟩,
      fun ⟨g, hg, hzg⟩ ↦ hg hzg⟩
  · intro g hg
    have hgr : ((PrimeSpectrum.basicOpen g).carrier : Set (Spec Γ(V, ⊤))) ⊆
        Set.range V.toSpecΓ := by
      intro z hz
      obtain ⟨x, rfl⟩ := hg hz
      exact ⟨u x, rfl⟩
    have hVsub : (V.basicOpen g : Set V) ⊆ Set.range u := by
      intro y hy
      have hy' : V.toSpecΓ y ∈ PrimeSpectrum.basicOpen g := by
        change y ∈ V.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen g
        rwa [toSpecΓ_preimage_basicOpen]
      obtain ⟨x, hx⟩ := hg hy'
      exact ⟨x, V.toSpecΓ.isEmbedding.injective hx⟩
    have hVaff : IsAffineOpen (V.basicOpen g) := by
      rw [← toSpecΓ_preimage_basicOpen]
      exact (IsAffineOpen.Spec_basicOpen g).preimage_of_isOpenImmersion V.toSpecΓ hgr
    have hrV : Set.range ((V.basicOpen g).ι ≫ V.toSpecΓ) =
        Set.range (Scheme.Opens.ι (X := Spec Γ(V, ⊤)) (PrimeSpectrum.basicOpen g)) := by
      simp only [Hom.comp_base, TopCat.coe_comp, Set.range_comp, Opens.range_ι]
      rw [← toSpecΓ_preimage_basicOpen]
      exact Set.image_preimage_eq_of_subset hgr
    have hpre := preimage_basicOpen_top u g
    have hUaff : IsAffineOpen (U.basicOpen (u.appTop g)) := by
      rw [← hpre]
      exact hVaff.preimage_of_isOpenImmersion u hVsub
    have hrU : Set.range ((U.basicOpen (u.appTop g)).ι ≫ u) =
        Set.range (V.basicOpen g).ι := by
      simp only [Hom.comp_base, TopCat.coe_comp, Set.range_comp, Opens.range_ι]
      rw [← hpre]
      exact Set.image_preimage_eq_of_subset hVsub
    exact ⟨hVsub, hVaff,
      ⟨IsOpenImmersion.isoOfRangeEq _ _ hrV, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrV⟩,
      hpre.symm, SpecMap_preimage_basicOpen u.appTop g,
      ⟨IsOpenImmersion.isoOfRangeEq _ _ hrU, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrU⟩,
      hUaff⟩
  · intro x
    obtain ⟨g, hxg, hg⟩ := hb ((u ≫ V.toSpecΓ) x) ⟨x, rfl⟩
    refine ⟨g, hg, ?_⟩
    rw [← preimage_basicOpen_top, ← toSpecΓ_preimage_basicOpen]
    exact hxg

end AlgebraicGeometry.Scheme
