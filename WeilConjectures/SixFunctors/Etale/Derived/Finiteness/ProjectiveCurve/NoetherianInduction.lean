/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FiniteMorphism
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphismDescent
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Constructibility by Noetherian induction over integral subschemes

Let `S` be a Noetherian scheme and `F` an étale sheaf of `Λ`-modules on `S`. If for every
integral scheme `W` with an immersion `w : W ⟶ S` the pullback of `F` is constructible on some
nonempty open subscheme of `W`, then `F` is constructible
(`AlgebraicGeometry.Scheme.isConstructibleSheaf_of_forall_isIntegral`). This is the passage from
a dense-open assertion over every integral base to all of `S` in the proof of
`thm-fin-projective-curve-constant`: Noetherian induction on the closed subsets of `S`, the
open-closed gluing of constructibility (`prop-constructible-open-closed`) and its invariance
under universal homeomorphisms, which removes nilpotents.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Constructibility of pullbacks is transported along factorizations: if `h = a ≫ g` and the
pullback of `F` along `g` is constructible, so is its pullback along `h`. -/
lemma IsConstructibleSheaf.upperStar_of_fac {S W T : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {h : T ⟶ S} (a : T ⟶ W) {g : W ⟶ S}
    (e : h = a ≫ g) [IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj F)] :
    IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) h).obj F) :=
  have : IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) g ⋙
      Etale.upperStar (ModuleCat.{u + 1} Λ) a).obj F) :=
    IsConstructibleSheaf.upperStar a ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj F)
  IsConstructibleSheaf.of_iso ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) a g h e).app F).symm

/-- Every sheaf on an empty scheme is constructible: the empty stratification works. -/
lemma IsConstructibleSheaf.of_isEmpty {Z : Scheme.{u}} [IsEmpty Z]
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : IsConstructibleSheaf G :=
  ⟨{ n := 0
     stratum := Fin.elim0
     isLocallyClosed_stratum := fun i ↦ i.elim0
     isConstructible_stratum := fun i ↦ i.elim0
     iUnion_stratum_eq_univ := Set.eq_univ_of_forall isEmptyElim
     pairwise_disjoint_stratum := fun i ↦ i.elim0
     domain := Fin.elim0
     immersion := fun i ↦ i.elim0
     isImmersion := fun i ↦ i.elim0
     range_immersion := fun i ↦ i.elim0 }, fun i ↦ i.elim0⟩

/-- **Constructibility by Noetherian induction over integral subschemes.** Let `S` be a
Noetherian scheme and `F` a sheaf of `Λ`-modules on `S_ét`. Suppose that for every integral
scheme `W` with an immersion `w : W ⟶ S`, the pullback of `F` to some nonempty open subscheme of
`W` is constructible. Then `F` is constructible.

By Noetherian induction on the closed subsets `C` of `S`, the pullback of `F` along every closed
immersion `z : Z ⟶ S` with image `C` is constructible: a nonempty irreducible open `V ⊆ Z` has an
integral reduction `V_red`, the hypothesis applied to `V_red ⟶ S` gives a nonempty open
`U ⊆ V` on which the pullback is constructible (constructibility descends along the universal
homeomorphism `U_red ⟶ U`), its complement in `Z` has image strictly smaller than `C`, and
constructibility glues along the open-closed decomposition of `Z`. -/
theorem isConstructibleSheaf_of_forall_isIntegral {S : Scheme.{u}} [IsNoetherian S]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : ∀ (W : Scheme.{u}) (w : W ⟶ S) [IsImmersion w] [IsIntegral W], ∃ U : W.Opens,
      (U : Set W).Nonempty ∧
        IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U.ι ≫ w)).obj F)) :
    IsConstructibleSheaf F := by
  suffices H : ∀ C : TopologicalSpace.Closeds S, ∀ (Z : Scheme.{u}) (z : Z ⟶ S)
      [IsClosedImmersion z], Set.range z.base = C →
        IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) z).obj F) by
    have := H ⊤ S (𝟙 S) (by simp)
    exact IsConstructibleSheaf.of_iso ((Etale.upperStarId (ModuleCat.{u + 1} Λ) S).app F)
  intro C
  induction C using WellFoundedLT.induction with
  | ind C ih =>
  intro Z z _ hz
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian z
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace z
  have : IsNoetherian Z := {}
  by_cases hZ : IsEmpty Z
  · exact IsConstructibleSheaf.of_isEmpty _
  rw [not_isEmpty_iff] at hZ
  -- a nonempty irreducible open `V ⊆ Z` and its integral reduction `R`
  obtain ⟨O, hO, hirr⟩ := TopologicalSpace.NoetherianSpace.exists_isOpen_isIrreducible_inter
    (Set.univ_nonempty (α := Z))
  rw [Set.univ_inter] at hirr
  let V : Z.Opens := ⟨O, hO⟩
  have : IrreducibleSpace V := isIrreducible_iff_irreducibleSpace.1 hirr
  let I := IdealSheafData.vanishingIdeal (⊤ : TopologicalSpace.Closeds V)
  let r : I.subscheme ⟶ V := I.subschemeι
  have hr : Function.Surjective r.base := by
    rw [← Set.range_eq_univ]
    change Set.range I.subschemeι.base = Set.univ
    rw [IdealSheafData.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : Surjective r := ⟨hr⟩
  let e : I.subscheme ≃ₜ V := IsUniversalHomeomorphism.homeomorph r
  have : IrreducibleSpace I.subscheme := by
    rw [irreducibleSpace_def]
    have := (IrreducibleSpace.isIrreducible_univ V).image e.symm e.symm.continuous.continuousOn
    rwa [Set.image_univ_of_surjective e.symm.surjective] at this
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  obtain ⟨U', hU'ne, hU'⟩ := h I.subscheme (r ≫ V.ι ≫ z)
  -- the open `U ⊆ V` corresponding to `U'`
  let U : V.toScheme.Opens := ⟨r.base '' U', e.isOpenMap _ U'.isOpen⟩
  have hU : r ⁻¹ᵁ U = U' := TopologicalSpace.Opens.ext
    (Set.preimage_image_eq _ r.isClosedEmbedding.injective)
  have hUc : IsConstructibleSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U.ι ≫ V.ι ≫ z)).obj F) := by
    have : IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ)
        ((r ∣_ U) ≫ U.ι ≫ V.ι ≫ z)).obj F) :=
      IsConstructibleSheaf.upperStar_of_fac F (Scheme.isoOfEq _ hU).hom
        (by rw [morphismRestrict_ι_assoc, Scheme.isoOfEq_hom_ι_assoc])
    have : IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (r ∣_ U)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U.ι ≫ V.ι ≫ z)).obj F)) :=
      IsConstructibleSheaf.of_iso
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (r ∣_ U) (U.ι ≫ V.ι ≫ z)).app F)
    exact IsConstructibleSheaf.of_upperStar_of_isUniversalHomeomorphism (r ∣_ U) _
  -- glue along the open `j : U ⟶ Z` and its closed complement
  let j : U.toScheme ⟶ Z := U.ι ≫ V.ι
  let i := j.opensRange.closedComplement
  have hij : Set.range i.base = (Set.range j.base)ᶜ := by
    rw [Scheme.Opens.range_closedComplement]
    rfl
  refine (isConstructibleSheaf_iff_upperStar j i hij _).2 ⟨?_, ?_⟩
  · have : IsConstructibleSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (j ≫ z)).obj F) := by
      simpa [j] using hUc
    exact IsConstructibleSheaf.of_iso
      ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) j z (j ≫ z) rfl).app F)
  · let C' : TopologicalSpace.Closeds S :=
      ⟨Set.range (i ≫ z).base, (i ≫ z).isClosedEmbedding.isClosed_range⟩
    have hlt : C' < C := by
      refine lt_of_le_of_ne ?_ fun hC ↦ ?_
      · rintro _ ⟨x, rfl⟩
        rw [← SetLike.mem_coe, ← hz]
        exact ⟨_, rfl⟩
      · obtain ⟨y, hy⟩ := hU'ne
        let u₀ : U := ⟨r.base y, y, hy, rfl⟩
        have hmem : z.base (j.base u₀) ∈ (C : Set S) := by
          rw [← hz]
          exact ⟨_, rfl⟩
        rw [← hC] at hmem
        obtain ⟨x, hx⟩ := hmem
        have hx' : i.base x = j.base u₀ := z.isClosedEmbedding.injective (by simpa using hx)
        have : i.base x ∈ Set.range i.base := ⟨x, rfl⟩
        rw [hij, hx'] at this
        exact this ⟨_, rfl⟩
    have := ih C' hlt _ (i ≫ z) rfl
    exact IsConstructibleSheaf.of_iso
      ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) i z (i ≫ z) rfl).app F)

end Scheme

end AlgebraicGeometry
