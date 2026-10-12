/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
import Sheaf.AlgebraicGeometry.ProjectiveSpaceReindexChart

/-! # Invertibility of the coordinate reindexing morphism

Source: Stacks Project, Constructions, Definition 01NF and Lemma 01NE.
(blueprint: lem-weil-pbc-projective-space-reindex-is-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

/-- The morphism defined by the coordinate sections in a bijectively renamed order
is an isomorphism. No finiteness or nonemptiness assumption is needed.

Source: Stacks Project, Constructions, Definition 01NF and Lemma 01NE.
(blueprint: lem-weil-pbc-projective-space-reindex-is-iso).

Proof: On the open indexed by i, the free generator is the pullback of T_(b i)
under the identity. The coefficients of the other sections are T_(b j)/T_(b i).
The standardOpenIso identifies these opens with relative affine spaces over S.
After restriction over an affine open Spec R of S, the construction
homOfIsFreeGenerator therefore has the map of polynomial coordinate rings
over R sending T_j/T_i to T_(b j)/T_(b i), and fixing R by
homOfIsFreeGenerator_over. These affine opens cover the relative charts. Bijectivity of b
identifies the variables other than i with the variables other than b i, so this
ring map is an isomorphism, with inverse given by b.symm. These affine maps have
the same coordinate-ratio formulas on intersections. The maps formed by b and
b.symm compose to the identity on every standard chart, since their maps on the
base and on all coordinate ratios are identities. The standard charts cover,
so equality of these composites holds globally. Thus the displayed morphism
has a two-sided inverse. For empty coordinate types the schemes are empty and
the same chartwise equality argument applies to the empty cover. -/
theorem isIso_homOfIsFreeGenerator_reindex (β γ : Type u) (b : γ ≃ β)
    (S : Scheme.{u}) :
    let s := fun j : γ ↦ Scheme.Modules.pullbackSection (𝟙 ℙ(β; S))
      (twistOneSection β S (b j))
    let U := fun j : γ ↦ standardOpen β S (b j)
    let hs := fun j : γ ↦
      isFreeGenerator_pullbackSection_twistOneSection (𝟙 ℙ(β; S)) (b j)
    let hU : ⨆ j, U j = ⊤ := (b.iSup_comp).trans (iSup_standardOpen β S)
    IsIso (homOfIsFreeGenerator s U hs (ℙ(β; S) ↘ S) hU) := by
  dsimp only
  let φ := homOfIsFreeGenerator
    (fun j : γ ↦ Scheme.Modules.pullbackSection (𝟙 ℙ(β; S))
      (twistOneSection β S (b j)))
    (fun j : γ ↦ standardOpen β S (b j))
    (fun j : γ ↦ isFreeGenerator_pullbackSection_twistOneSection (𝟙 ℙ(β; S)) (b j))
    (ℙ(β; S) ↘ S) ((b.iSup_comp).trans (iSup_standardOpen β S))
  let ψ := homOfIsFreeGenerator
    (fun j : β ↦ Scheme.Modules.pullbackSection (𝟙 ℙ(γ; S))
      (twistOneSection γ S (b.symm j)))
    (fun j : β ↦ standardOpen γ S (b.symm j))
    (fun j : β ↦
      isFreeGenerator_pullbackSection_twistOneSection (𝟙 ℙ(γ; S)) (b.symm j))
    (ℙ(γ; S) ↘ S) ((b.symm.iSup_comp).trans (iSup_standardOpen γ S))
  have hφ := ι_homOfIsFreeGenerator_reindex β γ b S
  have hψ := ι_homOfIsFreeGenerator_reindex γ β b.symm S
  dsimp only at hφ hψ
  change IsIso φ
  refine ⟨⟨ψ, ?_, ?_⟩⟩
  · apply Scheme.Opens.hom_ext_of_iSup_eq_top
      (fun i : γ ↦ standardOpen β S (b i))
      ((b.iSup_comp).trans (iSup_standardOpen β S))
    intro i
    rw [← Category.assoc, hφ i (b i) rfl]
    simp only [Category.assoc]
    rw [hψ (b i) i (b.symm_apply_apply i)]
    simp only [Iso.inv_hom_id_assoc]
    have hc :
        AffineSpace.reindex
          (fun j : {j : γ // j ≠ i} ↦
            (⟨b j.1, fun he ↦ j.2 (b.injective (he.trans rfl))⟩ :
              {j : β // j ≠ b i})) S ≫
        AffineSpace.reindex
          (fun j : {j : β // j ≠ b i} ↦
            (⟨b.symm j.1, fun he ↦
              j.2 (b.symm.injective (he.trans (b.symm_apply_apply i).symm))⟩ :
              {j : γ // j ≠ i})) S = 𝟙 _ := by
      apply AffineSpace.hom_ext
      · simp
      · intro j
        simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          AffineSpace.reindex_appTop_coord, Scheme.Hom.id_appTop, CommRingCat.id_apply]
        congr 1
        apply Subtype.ext
        exact b.apply_symm_apply j.1
    rw [reassoc_of% hc]
    simp
  · apply Scheme.Opens.hom_ext_of_iSup_eq_top
      (fun i : β ↦ standardOpen γ S (b.symm i))
      ((b.symm.iSup_comp).trans (iSup_standardOpen γ S))
    intro i
    rw [← Category.assoc, hψ i (b.symm i) rfl]
    simp only [Category.assoc]
    rw [hφ (b.symm i) i (b.apply_symm_apply i)]
    simp only [Iso.inv_hom_id_assoc]
    have hc :
        AffineSpace.reindex
          (fun j : {j : β // j ≠ i} ↦
            (⟨b.symm j.1, fun he ↦ j.2 (b.symm.injective (he.trans rfl))⟩ :
              {j : γ // j ≠ b.symm i})) S ≫
        AffineSpace.reindex
          (fun j : {j : γ // j ≠ b.symm i} ↦
            (⟨b j.1, fun he ↦
              j.2 (b.injective (he.trans (b.apply_symm_apply i).symm))⟩ :
              {j : β // j ≠ i})) S = 𝟙 _ := by
      apply AffineSpace.hom_ext
      · simp
      · intro j
        simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          AffineSpace.reindex_appTop_coord, Scheme.Hom.id_appTop, CommRingCat.id_apply]
        congr 1
        apply Subtype.ext
        exact b.symm_apply_apply j.1
    rw [reassoc_of% hc]
    simp

end AlgebraicGeometry.ProjectiveSpace
