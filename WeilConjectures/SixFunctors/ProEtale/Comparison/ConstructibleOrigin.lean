/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.OpenClosedOrigin
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LocallyConstantOrigin
public import WeilConjectures.ConstructibleSheaf.Devissage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# Gluing sheaves of étale origin along a stratification

Let `X` be a Noetherian scheme with a stratification `S`. A pro-étale sheaf of `Λ`-modules `F` on
`X` whose pullbacks along the morphisms from quasi-compact quasi-separated schemes into the strata
are of étale origin is itself of étale origin
(`AlgebraicGeometry.ProEtale.essImage_comparisonUpperStar_of_stratification`). Along a chain of
opens `∅ = V₀ ⊆ V₁ ⊆ ⋯ ⊆ V_m = X` whose differences lie in single strata
(`Topology.Stratification.exists_chain_opens`), the restriction of `F` to `V_{r+1}` is glued from
its restriction to `V_r` and to the reduced closed complement, which maps into a stratum
(`AlgebraicGeometry.ProEtale.essImage_comparisonUpperStar_of_isCompl`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- A morphism `a` from a reduced scheme whose range lies in the range of an immersion `b`
factors through `b`. -/
lemma exists_comp_eq_of_range_subset {Z Z' X : Scheme.{u}} [IsReduced Z] (a : Z ⟶ X)
    (b : Z' ⟶ X) [IsImmersion b] (h : Set.range a ⊆ Set.range b) :
    ∃ c : Z ⟶ Z', c ≫ b = a := by
  have := surjective_pullback_fst_of_range_subset a b h
  have := IsClosedImmersion.of_isImmersion_of_surjective (pullback.fst a b)
  have := isIso_of_isClosedImmersion_of_surjective (pullback.fst a b)
  exact ⟨inv (pullback.fst a b) ≫ pullback.snd a b, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩

/-- The empty family covers an empty scheme, so every pro-étale sheaf on an empty scheme is of
étale origin. -/
lemma essImage_comparisonUpperStar_of_isEmpty [Etale.HasCohomologyContinuity (ModuleCat.{u + 1} Λ)]
    {X : Scheme.{u}} [IsEmpty X] (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).essImage F :=
  essImage_comparisonUpperStar_of_cover (S := Empty) (V := fun e ↦ e.elim) (fun e ↦ e.elim)
    (ofArrows_mem_proetalePrecoverage_of_finite (S := Empty) (V := fun e ↦ e.elim)
      (fun e ↦ e.elim) (fun x ↦ isEmptyElim x)) F (fun e ↦ e.elim)

/-- Being of étale origin can be checked after pulling back along an isomorphism. -/
lemma essImage_comparisonUpperStar_of_isIso [Etale.HasCohomologyContinuity (ModuleCat.{u + 1} Λ)]
    {X Y : Scheme.{u}} (g : Y ⟶ X) [IsIso g]
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (hF : (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).essImage
      ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).obj F)) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).essImage F :=
  essImage_comparisonUpperStar_of_cover (S := Unit) (V := fun _ ↦ Y) (fun _ ↦ g)
    (ofArrows_mem_proetalePrecoverage_of_finite (S := Unit) (V := fun _ ↦ Y) (fun _ ↦ g)
      (fun x ↦ ⟨(), inv g x, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩)) F
    (fun _ ↦ hF)

/-- **Gluing along a stratification.** On a Noetherian scheme `X` with a stratification `S`, a
pro-étale sheaf of `Λ`-modules is of étale origin as soon as its pullbacks along the morphisms from
quasi-compact quasi-separated schemes into the strata are. -/
theorem essImage_comparisonUpperStar_of_stratification
    [Etale.HasCohomologyContinuity (ModuleCat.{u + 1} Λ)] {X : Scheme.{u}} [IsNoetherian X]
    (S : Scheme.Stratification X) (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hS : ∀ (k : Fin S.n) {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
      (h : Y ⟶ S.domain k), (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).essImage
        ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) (h ≫ S.immersion k)).obj F)) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).essImage F := by
  let A := ModuleCat.{u + 1} Λ
  obtain ⟨m, V, hV0, hVm, hstep⟩ := S.exists_chain_opens (⊥ : X.Opens)
  have key (r : Fin (m + 1)) : (comparisonUpperStar A (V r)).essImage
      ((ProEtale.upperStar A (Scheme.Opens.ι (V r))).obj F) := by
    induction r using Fin.induction with
    | zero =>
      have : IsEmpty (V 0) := by
        rw [hV0]
        exact ⟨fun x ↦ TopologicalSpace.Opens.mem_bot.mp x.2⟩
      exact essImage_comparisonUpperStar_of_isEmpty _
    | succ r ih =>
      obtain ⟨hle, k, hk⟩ := hstep r
      let W : X.Opens := V r.succ
      let j := X.homOfLE hle
      let I := IdealSheafData.vanishingIdeal (⟨(Set.range j.base)ᶜ,
        j.isOpenEmbedding.isOpen_range.isClosed_compl⟩ : TopologicalSpace.Closeds W)
      let i : I.subscheme ⟶ W := I.subschemeι
      have hcompl : Set.range i.base = (Set.range j.base)ᶜ := by
        simp [i, I, IdealSheafData.range_subschemeι]
      have hij : IsCompl (Set.range i.base) (Set.range j.base) := by
        rw [hcompl]
        exact isCompl_compl.symm
      -- the restriction to the open `V r`
      have hj : (comparisonUpperStar A (V r.castSucc)).essImage
          ((ProEtale.upperStar A j).obj ((ProEtale.upperStar A W.ι).obj F)) :=
        essImage_comparisonUpperStar_of_iso
          ((ProEtale.upperStarCongr A (X.homOfLE_ι hle).symm).app F ≪≫
            (ProEtale.upperStarComp A j W.ι).app F) ih
      -- the restriction to the closed complement, which maps into the stratum `k`
      have hrange : Set.range (i ≫ W.ι).base ⊆ Set.range (S.immersion k).base := by
        rw [S.range_immersion]
        rintro _ ⟨z, rfl⟩
        apply hk
        refine ⟨by simp [W], fun hz ↦ ?_⟩
        have hzi : i.base z ∉ Set.range j.base := by
          rw [← Set.mem_compl_iff, ← hcompl]
          exact ⟨z, rfl⟩
        exact hzi ⟨⟨_, hz⟩, Subtype.ext (by simp [j, Scheme.homOfLE_apply])⟩
      obtain ⟨c, hc⟩ := exists_comp_eq_of_range_subset (i ≫ W.ι) (S.immersion k) hrange
      have : TopologicalSpace.NoetherianSpace W :=
        W.ι.isOpenEmbedding.isInducing.noetherianSpace
      have : TopologicalSpace.NoetherianSpace I.subscheme :=
        i.isClosedEmbedding.isInducing.noetherianSpace
      have : CompactSpace I.subscheme := ⟨TopologicalSpace.NoetherianSpace.isCompact _⟩
      have : QuasiSeparatedSpace I.subscheme :=
        ⟨fun _ _ _ _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
      have hi : (comparisonUpperStar A I.subscheme).essImage
          ((ProEtale.upperStar A i).obj ((ProEtale.upperStar A W.ι).obj F)) :=
        essImage_comparisonUpperStar_of_iso
          ((ProEtale.upperStarCongr A hc).app F ≪≫ (ProEtale.upperStarComp A i W.ι).app F)
          (hS k c)
      exact essImage_comparisonUpperStar_of_isCompl i j hij _ hj hi
  have hlast := key (Fin.last m)
  rw [hVm] at hlast
  have : IsIso (Scheme.Opens.ι (⊤ : X.Opens)) := by
    rw [← Scheme.Opens.topIso_hom]
    infer_instance
  exact essImage_comparisonUpperStar_of_isIso _ hlast

end AlgebraicGeometry.ProEtale
