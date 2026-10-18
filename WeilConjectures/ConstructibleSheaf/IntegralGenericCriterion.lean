/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.ConstructibleSheaf.FiniteMorphism
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Constructibility from integral locally closed subschemes

A sheaf `F` of `Λ`-modules on a Noetherian scheme `X` is constructible as soon as every integral
Noetherian scheme `W` immersed in `X` has a nonempty open `U` on which the pullback of `F` is
constructible (`AlgebraicGeometry.Scheme.isConstructibleSheaf_of_forall_isIntegral`). This is
the Noetherian induction on closed subsets used in the blueprint proof of
`thm-fin-projective-curve-constant`: a nonempty reduced closed subscheme `Z ⊆ X` has a nonempty
irreducible, hence integral, open `V`, and the complement of the open of `V` given by the
hypothesis is a smaller closed subset.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- **Constructibility from integral locally closed subschemes.** A sheaf `F` of `Λ`-modules on a
Noetherian scheme `X` is constructible if every integral Noetherian scheme `W` with an immersion
`g : W ⟶ X` has a nonempty open `U` on which the pullback of `F` is constructible. The proof is
Noetherian induction on the closed subsets of `X` carrying a reduced closed subscheme structure, as
in `AlgebraicGeometry.Scheme.constructible_of_closed_generic`. -/
theorem isConstructibleSheaf_of_forall_isIntegral
    {X : Scheme.{u}} [IsNoetherian X] {Λ : Type (u + 1)} [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : ∀ (W : Scheme.{u}) [IsIntegral W] [IsNoetherian W] (g : W ⟶ X) [IsImmersion g],
      ∃ U : W.Opens, (U : Set W).Nonempty ∧
        IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U.ι ≫ g)).obj F)) :
    IsConstructibleSheaf F := by
  classical
  have key : ∀ (C : TopologicalSpace.Closeds X) (Z : Scheme.{u})
      (i : Z ⟶ X) [IsClosedImmersion i] [IsReduced Z], Set.range i ⊆ C →
      IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj F) := by
    intro C
    induction C using WellFoundedLT.induction with
    | ind C ih =>
      intro Z i _ _ hiC
      have hZ : IsNoetherian Z := by
        have := LocallyOfFiniteType.isLocallyNoetherian i
        have := QuasiCompact.compactSpace_of_compactSpace i
        exact {}
      cases isEmpty_or_nonempty Z
      · exact IsConstructibleSheaf.of_isZero (Etale.isZero_sheaf_of_isEmpty _)
      obtain ⟨O, hO, hOirr⟩ :=
        TopologicalSpace.NoetherianSpace.exists_isOpen_isIrreducible_inter
          (α := Z) Set.univ_nonempty
      rw [Set.univ_inter] at hOirr
      let V : Z.Opens := ⟨O, hO⟩
      have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace hOirr
      have : IsIntegral V.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
      have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp
        (TopologicalSpace.NoetherianSpace.isCompact _)
      have : IsNoetherian V.toScheme := {}
      obtain ⟨U, hUne, hU⟩ := h V (V.ι ≫ i)
      let U' : Z.Opens := V.ι ''ᵁ U
      let e := V.ι.isoImage U
      have hfac : e.inv ≫ U.ι ≫ V.ι ≫ i = U'.ι ≫ i := by
        rw [← Scheme.Hom.isoImage_inv_ι_assoc]
      have h3 : IsConstructibleSheaf
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (e.inv ≫ U.ι ≫ V.ι ≫ i)).obj F) :=
        have := IsConstructibleSheaf.upperStar e.inv
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U.ι ≫ V.ι ≫ i)).obj F)
        IsConstructibleSheaf.of_iso (F := (Etale.upperStar (ModuleCat.{u + 1} Λ) e.inv).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U.ι ≫ V.ι ≫ i)).obj F))
          ((Etale.upperStarComp _ e.inv (U.ι ≫ V.ι ≫ i)).app F).symm
      rw [hfac] at h3
      have hopen : IsConstructibleSheaf
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) U'.ι).obj
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj F)) :=
        IsConstructibleSheaf.of_iso ((Etale.upperStarComp _ U'.ι i).app F)
      let D : TopologicalSpace.Closeds Z := ⟨(U' : Set Z)ᶜ, U'.isOpen.isClosed_compl⟩
      let i' := (IdealSheafData.vanishingIdeal D).subschemeι
      have hrange : Set.range i' = (U' : Set Z)ᶜ := by
        simp [i', D, IdealSheafData.range_subschemeι,
          IdealSheafData.coe_support_vanishingIdeal]
      obtain ⟨z, hz⟩ : (U' : Set Z).Nonempty := by
        obtain ⟨x, hx⟩ := hUne
        exact ⟨V.ι (U.ι ⟨x, hx⟩), ⟨x, hx, rfl⟩⟩
      let C' : TopologicalSpace.Closeds X :=
        ⟨i '' (U' : Set Z)ᶜ, i.isClosedEmbedding.isClosedMap _ U'.isOpen.isClosed_compl⟩
      have hlt : C' < C := by
        refine lt_of_le_of_ne (fun y ⟨t, _, ht⟩ ↦ hiC ⟨t, ht⟩) fun heq ↦ ?_
        have : i z ∈ (C' : Set X) := heq ▸ hiC ⟨z, rfl⟩
        obtain ⟨t, ht, hti⟩ := this
        exact ht (i.isClosedEmbedding.injective hti ▸ hz)
      have hC' := ih C' hlt _ (i' ≫ i) (by
        rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange]; exact subset_rfl)
      have hclosed : IsConstructibleSheaf
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) i').obj
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj F)) :=
        IsConstructibleSheaf.of_iso
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) i' i).app F)
      exact (isConstructibleSheaf_iff_upperStar U'.ι i'
        (by rw [Scheme.Opens.range_ι, hrange]) _).mpr ⟨hopen, hclosed⟩
  let i₀ := (IdealSheafData.vanishingIdeal (⊤ : TopologicalSpace.Closeds X)).subschemeι
  have hrange : Set.range i₀ = Set.univ := by
    simp [i₀, IdealSheafData.range_subschemeι]
  have h₀ := key ⊤ _ i₀ (by simp)
  refine (isConstructibleSheaf_iff_upperStar (⊥ : X.Opens).ι i₀
    (by rw [Scheme.Opens.range_ι, hrange]; simp) _).mpr ⟨?_, h₀⟩
  have : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x ↦ x.2⟩
  exact IsConstructibleSheaf.of_isZero (Etale.isZero_sheaf_of_isEmpty _)

end AlgebraicGeometry.Scheme
