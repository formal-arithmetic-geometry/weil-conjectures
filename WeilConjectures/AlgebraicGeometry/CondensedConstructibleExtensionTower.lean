/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedConstructiblePiece
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleOneStep

/-! # Finite open/closed dévissage of constructible condensed module sheaves -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem pushforward_piece
    {Z T : Scheme.{u}} (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (i : Z ⟶ T) [IsClosedImmersion i]
    [PreservesFiniteColimits
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj E.val) i)]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.val) Z)))
    (hK : condensedConstructiblePiece Z ℓ E K) :
    condensedConstructiblePiece T ℓ E
      ((CondensedRing.lowerStar
        (Profinite.continuousMapRingObj E.val) i).mapDerivedCategory.obj K) := by
  obtain ⟨V, U, k, j, hk, hj, hqc, P, hP, ⟨e⟩⟩ := hK
  let := hk
  let := hj
  refine ⟨V, U, k ≫ i, j, inferInstance, hj, hqc, P, hP, ⟨?_⟩⟩
  exact ((CondensedRing.lowerStar
        (Profinite.continuousMapRingObj E.val) i).mapDerivedCategory.mapIso e) ≪≫
    ((CondensedRing.lowerStar
        (Profinite.continuousMapRingObj E.val) i).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((CondensedRing.lowerStarComp (Profinite.continuousMapRingObj E.val) k i).app _)

private theorem pushforward_tower
    {Z T : Scheme.{u}} (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (i : Z ⟶ T) [IsClosedImmersion i]
    [PreservesFiniteColimits
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj E.val) i)]
    (r : ℕ) :
    ∀ K, (condensedConstructiblePiece Z ℓ E).extensionProductIter r K →
      (condensedConstructiblePiece T ℓ E).extensionProductIter r
        ((CondensedRing.lowerStar
        (Profinite.continuousMapRingObj E.val) i).mapDerivedCategory.obj K) := by
  let F := (CondensedRing.lowerStar
        (Profinite.continuousMapRingObj E.val) i).mapDerivedCategory
  induction r with
  | zero => exact fun K hK ↦ pushforward_piece ℓ E i K hK
  | succ r ih =>
    rw [ObjectProperty.extensionProductIter_succ]
    rintro K ⟨A, B, f, g, k, hdist, hA, hB⟩
    rw [ObjectProperty.extensionProductIter_succ]
    have h := F.map_distinguished _ hdist
    exact ⟨_, _, _, _, _, h, pushforward_piece ℓ E i A hA, ih B hB⟩

/-- A constructible sheaf is a finite distinguished extension of its locally free pieces
(Hemo--Richarz--Scholbach, Lemma 5.3(2)). -/
theorem exists_condensedConstructible_extension_tower
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.val) T))
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E.val) T) M) :
    ∃ r : ℕ, (condensedConstructiblePiece T ℓ E).extensionProductIter r
      ((DerivedCategory.singleFunctor _ 0).obj M) := by
  suffices h : ∀ C : TopologicalSpace.Closeds T, ∀ (Z : Scheme.{u}) (i : Z ⟶ T)
      [_hi : IsClosedImmersion i], Set.range i ⊆ C →
      ∀ (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.val) Z)),
      IsConstructibleModuleObject
        (condensedRingObj (Profinite.continuousMapRingObj E.val) Z) M →
      ∃ r : ℕ, (condensedConstructiblePiece Z ℓ E).extensionProductIter r
        ((DerivedCategory.singleFunctor _ 0).obj M) by
    exact h ⊤ T (𝟙 T) (Set.subset_univ _) M hM
  intro C
  induction C using WellFoundedLT.induction with
  | _ C ih =>
    intro Z i hi hZC M hM
    have : TopologicalSpace.NoetherianSpace Z :=
      i.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
    rcases condensed_constructible_one_step Z ℓ E M hM with hpiece | hstep
    · exact ⟨0, hpiece⟩
    obtain ⟨Z', i', hi', hex, hproper, MZ, hMZ, A, f, g, k, hdist, hA⟩ := hstep
    let := hi'
    let := hex
    let C' : TopologicalSpace.Closeds T :=
      ⟨Set.range (i' ≫ i), (i' ≫ i).isClosedEmbedding.isClosed_range⟩
    have hC' : C' < C := by
      refine lt_of_le_of_ne (fun x hx ↦ ?_) fun heq ↦ ?_
      · obtain ⟨z, rfl⟩ := hx
        exact hZC ⟨_, rfl⟩
      · apply hproper
        intro z
        have hz : i z ∈ (C : Set T) := hZC ⟨z, rfl⟩
        rw [← heq] at hz
        obtain ⟨z', hz'⟩ := hz
        exact ⟨z', i.isClosedEmbedding.injective hz'⟩
    obtain ⟨r, hr⟩ := ih C' hC' Z' (i' ≫ i) subset_rfl MZ hMZ
    refine ⟨r + 1, ?_⟩
    rw [ObjectProperty.extensionProductIter_succ]
    exact ⟨_, _, f, g, k, hdist, hA, pushforward_tower ℓ E i' r _ hr⟩

end AlgebraicGeometry.ProEtale
