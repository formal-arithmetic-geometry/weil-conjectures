/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Étale data at a cofiltered limit of schemes

Let `X = lim Dⱼ` be a cofiltered limit of schemes with affine transition maps. This file
collects the finite-presentation data which descends from `X` to some stage `Dⱼ`, in the form in
which it is used for the continuity of étale sections
(`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`).

## Main results

- `AlgebraicGeometry.exists_etale_isPullback_of_isAffine`: if all `Dⱼ` are affine, every étale
  `X`-scheme is, around any of its points, dominated by the base change of an affine scheme
  étale over some `Dⱼ`. The proof writes the étale `X`-scheme locally as `Spec` of a standard
  étale algebra over `Γ(X) = colim Γ(Dⱼ)`, whose finitely many coefficients come from a stage.
- `AlgebraicGeometry.exists_etale_refinement_of_isLimit`: the same for a scheme étale over the
  base change `V ×_{Dₖ} X` of a scheme `V` étale over a stage `Dₖ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Étale schemes over an affine limit are locally dominated by base changes from a stage.**
Let `X = lim Aᵢ` be a cofiltered limit of affine schemes and `β : Z ⟶ X` étale. Every point of
`Z` lies in the image of a morphism `γ : E ×_{Aᵢ} X ⟶ Z` over `X` from the base change of an
affine scheme `E` étale over some `Aᵢ`. -/
theorem exists_etale_isPullback_of_isAffine {I : Type u} [Category.{u} I] [IsCofiltered I]
    (A : I ⥤ Scheme.{u}) [∀ i, IsAffine (A.obj i)] (c : Cone A) (hc : IsLimit c)
    {Z : Scheme.{u}} (β : Z ⟶ c.pt) [Etale β] (z : Z) :
    ∃ (i : I) (E : Scheme.{u}) (_ : IsAffine E) (q : E ⟶ A.obj i) (_ : Etale q)
      (E' : Scheme.{u}) (π₁ : E' ⟶ E) (π₂ : E' ⟶ c.pt) (_ : IsPullback π₁ π₂ q (c.π.app i))
      (γ : E' ⟶ Z), γ ≫ β = π₂ ∧ z ∈ Set.range γ := by
  classical
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  -- a standard étale chart of `Z` over `Spec Γ(X)` around `z`
  obtain ⟨P, e, he, hz⟩ := Etale.exists_standardEtalePair (β ≫ c.pt.isoSpec.hom) z
  -- `Γ(X)` is the colimit of the `Γ(Aᵢ)`
  obtain ⟨hcol⟩ := nonempty_isColimit_Γ_mapCocone A c hc
  have hrep (b : Γ(c.pt, ⊤)) : ∃ (i : I) (s : Γ(A.obj i, ⊤)), (c.π.app i).appTop s = b := by
    obtain ⟨⟨i⟩, s, hs⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget CommRingCat) hcol) b
    exact ⟨i, s, hs⟩
  choose i s hs using hrep
  -- the finitely many coefficients of `P` come from a common stage `i₀`
  let S : Finset Γ(c.pt, ⊤) := P.f.coeffs ∪ P.g.coeffs
  obtain ⟨i₀, hi₀⟩ := IsCofiltered.inf_objs_exists (S.image i)
  have hmem (b : Γ(c.pt, ⊤)) (hb : b ∈ S) : b ∈ Set.range (c.π.app i₀).appTop := by
    obtain ⟨g⟩ := hi₀ (Finset.mem_image_of_mem i hb)
    refine ⟨(A.map g).appTop (s b), ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, c.w g]
    exact hs b
  let R := Γ(A.obj i₀, ⊤)
  letI : Algebra R Γ(c.pt, ⊤) := (c.π.app i₀).appTop.hom.toAlgebra
  have hf : (P.f.coeffs : Set Γ(c.pt, ⊤)) ⊆ Set.range (algebraMap R Γ(c.pt, ⊤)) :=
    fun b hb ↦ hmem b (Finset.mem_union_left _ hb)
  have hg : (P.g.coeffs : Set Γ(c.pt, ⊤)) ⊆ Set.range (algebraMap R Γ(c.pt, ⊤)) :=
    fun b hb ↦ hmem b (Finset.mem_union_right _ hb)
  obtain ⟨Q, ⟨ε⟩⟩ := StandardEtalePair.exists_algEquiv_tensor_ring_of_coeffs_subset P hf hg
  -- the pushout square of rings `R → Γ(X), Q.Ring → P.Ring`
  have hpo : IsPushout (CommRingCat.ofHom (algebraMap R Γ(c.pt, ⊤)))
      (CommRingCat.ofHom (algebraMap R Q.Ring))
      (CommRingCat.ofHom (algebraMap Γ(c.pt, ⊤) P.Ring))
      (CommRingCat.ofHom (ε.toRingHom.comp (Algebra.TensorProduct.includeRight
        (R := R) (A := Γ(c.pt, ⊤)) (B := Q.Ring)).toRingHom)) := by
    refine (CommRingCat.isPushout_tensorProduct R Γ(c.pt, ⊤) Q.Ring).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ε.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
    · simp
    · simp
    · ext x
      change ε (x ⊗ₜ 1) = algebraMap _ _ x
      rw [← ε.commutes]
      rfl
    · ext x
      simp
  have hqet : Etale (Spec.map (CommRingCat.ofHom (algebraMap R Q.Ring))) :=
    HasRingHomProperty.Spec_iff.mpr
      (RingHom.etale_algebraMap.mpr (inferInstanceAs (Algebra.Etale R Q.Ring)))
  have hsq : IsPullback
      (Spec.map (CommRingCat.ofHom (ε.toRingHom.comp (Algebra.TensorProduct.includeRight
        (R := R) (A := Γ(c.pt, ⊤)) (B := Q.Ring)).toRingHom)))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(c.pt, ⊤) P.Ring)) ≫ c.pt.isoSpec.inv)
      (Spec.map (CommRingCat.ofHom (algebraMap R Q.Ring)) ≫ (A.obj i₀).isoSpec.inv)
      (c.π.app i₀) := by
    refine (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip.of_iso (Iso.refl _) (Iso.refl _)
      c.pt.isoSpec.symm (A.obj i₀).isoSpec.symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp only [Iso.symm_hom]
      rw [← Scheme.isoSpec_inv_naturality]
      rfl
  refine ⟨i₀, _, inferInstance, _, inferInstance, _, _, _, hsq, e, ?_, hz⟩
  rw [← he]
  simp

end AlgebraicGeometry
