/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale

/-! # Composition of the coefficientwise Rees maps

Source: blueprint latest, sec-smooth-purity, orientation charts Step 3 and
composition coherence Step 1 (blueprint: lem-pur-section-rees-map-composition).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.SectionRestriction

/-- Composition for the actual coefficientwise maps of smooth section Rees spaces.
Source: blueprint latest, sk-thm-dnc Local construction, and orientation charts Step 3
(blueprint: lem-pur-section-rees-map-composition).
Proof: choose affine opens U in V, U' in V', and U'' in V'' with
U' contained in h inverse U and U'' contained in h' inverse U'. These triples
cover V''. On their Rees charts, pairMap is Spec of extendedReesAlgebraMap.
The identity appLE_comp_appLE identifies the two coefficient maps, and
extendedReesAlgebraMap_comp identifies their Rees extensions. Thus the two scheme
maps agree after every chart map. The relative gluing cover is jointly epimorphic,
so the equality holds globally. The proof uses commuting centres, not flatness,
and therefore includes arbitrary base changes and identity maps. -/
theorem rees_pairMap_comp {V V' V'' S S' S'' : Scheme.{u}}
    (s : S ⟶ V) (s' : S' ⟶ V') (s'' : S'' ⟶ V'')
    [IsClosedImmersion s] [IsClosedImmersion s'] [IsClosedImmersion s'']
    (h : V' ⟶ V) (h' : V'' ⟶ V') (b : S' ⟶ S) (b' : S'' ⟶ S')
    (w : s' ≫ h = b ≫ s) (w' : s'' ≫ h' = b' ≫ s') :
    SectionReesBaseChange.pairMap s s'' (h' ≫ h) (b' ≫ b)
      (by rw [← Category.assoc, w', Category.assoc, w, ← Category.assoc]) =
    SectionReesBaseChange.pairMap s' s'' h' b' w' ≫
      SectionReesBaseChange.pairMap s s' h b w  := by
  classical
  open Scheme.AffineZariskiSite in
    let J := {q : V''.AffineZariskiSite × V'.AffineZariskiSite × V.AffineZariskiSite //
      q.2.1.1 ≤ h ⁻¹ᵁ q.2.2.1 ∧ q.1.1 ≤ h' ⁻¹ᵁ q.2.1.1}
    let C : s''.ker.deformationSpace.OpenCover :=
      Scheme.Cover.mkOfCovers J
        (fun q ↦ (relativeGluingData s''.ker.coequifibered_toReesPresheaf).functor.obj q.1.1)
        (fun q ↦ colimit.ι
          (relativeGluingData s''.ker.coequifibered_toReesPresheaf).functor q.1.1)
        (by
          intro z
          let x := s''.ker.deformationSpaceProj z
          obtain ⟨U, hU, hxU, _⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
            V.isBasis_affineOpens (show h (h' x) ∈ (⊤ : V.Opens) from trivial)
          obtain ⟨U', hU', hxU', hle'⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
            V'.isBasis_affineOpens (show h' x ∈ h ⁻¹ᵁ U from hxU)
          obtain ⟨U'', hU'', hxU'', hle''⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
            V''.isBasis_affineOpens (show x ∈ h' ⁻¹ᵁ U' from hxU')
          have hz : z ∈ s''.ker.deformationSpaceProj ⁻¹ᵁ U'' := hxU''
          change z ∈ (relativeGluingData s''.ker.coequifibered_toReesPresheaf).toBase
            ⁻¹ᵁ (⟨U'', hU''⟩ : V''.AffineZariskiSite).1 at hz
          rw [toBase_preimage] at hz
          obtain ⟨y, hy⟩ := hz
          exact ⟨⟨(⟨U'', hU''⟩, ⟨U', hU'⟩, ⟨U, hU⟩), hle', hle''⟩, y, hy⟩)
    apply C.hom_ext
    intro q
    change colimit.ι
      (relativeGluingData s''.ker.coequifibered_toReesPresheaf).functor q.1.1 ≫ _ =
        colimit.ι (relativeGluingData s''.ker.coequifibered_toReesPresheaf).functor q.1.1 ≫
          (SectionReesBaseChange.pairMap s' s'' h' b' w' ≫
            SectionReesBaseChange.pairMap s s' h b w)
    dsimp only [SectionReesBaseChange.pairMap, Scheme.IdealSheafData.deformationSpaceMap]
    have hle : q.1.1.1 ≤ (h' ≫ h) ⁻¹ᵁ q.1.2.2.1 :=
      q.2.2.trans (h'.preimage_mono q.2.1)
    rw [PullbackData.ι_comparison _ _ _ hle,
      PullbackData.ι_comparison_assoc _ _ _ q.2.2,
      PullbackData.ι_comparison _ _ _ q.2.1, ← Spec.map_comp_assoc]
    congr 2
    apply CommRingCat.hom_ext
    simp only [Scheme.IdealSheafData.extendedReesPullbackData_map,
      CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    rw [Ideal.extendedReesAlgebraMap_comp]
    have he := Scheme.Hom.appLE_comp_appLE h' h q.1.2.2.1 q.1.2.1.1 q.1.1.1
      q.2.1 q.2.2
    congr 1
    exact congrArg CommRingCat.Hom.hom he.symm

end WeilConjectures.PurityFiniteSetting.SectionRestriction
