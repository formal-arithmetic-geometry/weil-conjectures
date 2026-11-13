/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import all WeilConjectures.AlgebraicGeometry.FlatFpLqfBoundedStratification
import WeilConjectures.AlgebraicGeometry.HasUniversallyBoundedFibersOfIsLocallyQuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.AlgebraicGeometry.FiniteFiberDegreeBaseChange
import WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange
import WeilConjectures.AlgebraicGeometry.QuasiFiniteDegreeUpperLocusCompact
import WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite

/-!
# Stratifying flat quasi-finite separated morphisms by degree

We index the closed filtration starting at zero: `Z 0` denotes the paper's `Z_{-1}`,
so the degree-`r` stratum is `Z (r + 1) \ Z r`, written out in place.

## References

* [Stacks Project, Tag 07RZ](https://stacks.math.columbia.edu/tag/07RZ)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- A flat, locally finitely presented, separated quasi-finite morphism admits a closed
filtration whose successive differences universally characterize finite local freeness
of each degree, and these strata meet every quasi-compact open in a quasi-compact subset
(Stacks, More on Morphisms, Tag 07RZ). -/
theorem exists_closed_stratification_of_flat_quasiFinite
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [IsSeparated f] (hf : f.IsQuasiFinite) :
    ∃ Z : ℕ → Set S,
      Z 0 = ∅ ∧ (∀ n : ℕ, IsClosed (Z n)) ∧ Monotone Z ∧
      Pairwise (fun r t : ℕ => Disjoint (Z (r + 1) \ Z r) (Z (t + 1) \ Z t)) ∧
      (⋃ r : ℕ, Z (r + 1) \ Z r) = Set.univ ∧
      (∀ (T : Scheme.{u}) (g : T ⟶ S) (r : ℕ),
        (pullback.snd f g).IsFiniteLocallyFreeOfDegree r ↔ Set.range g ⊆ Z (r + 1) \ Z r) ∧
      (∀ (r : ℕ) (W : S.Opens), IsCompact (W : Set S) →
        IsCompact ((Z (r + 1) \ Z r) ∩ (W : Set S))) := by
  classical
  have : LocallyOfFiniteType f := hf.1
  have : QuasiCompact f := hf.2.1
  have : LocallyQuasiFinite f :=
    locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr fun s ↦ by
      rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton]
      rintro ⟨x, hx⟩
      have hxs : f x = s := hx
      subst s
      simpa only [Set.image_singleton, asFiber, Homeomorph.apply_symm_apply] using
        (f.fiberHomeo (f x)).isOpenMap _ (hf.2.2 x)
  have h_lqf := (isQuasiFinite_iff_isLocallyQuasiFinite_and_quasiCompact f).mp hf |>.1
  have hfin (s : S) : IsFinite (f.fiberToSpecResidueField s) := inferInstance
  let δ : S → ℕ := fun s ↦ (f.fiberToSpecResidueField s).finrankΓ
  have hclosed (r : ℕ) : IsClosed {s : S | δ s ≤ r} := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro s hs
    let i := S.affineCover.idx s
    let g := S.affineCover.f i
    let f' := pullback.snd f g
    have hlqf' : IsLocallyQuasiFinite f' := (separated_lqf_base_change f g).2 h_lqf
    obtain ⟨n, hn⟩ := hasUniversallyBoundedFibers_of_isLocallyQuasiFinite f' hlqf'
    have hdeg (t : S.affineCover.X i) :
        (f'.fiberToSpecResidueField t).finrankΓ = δ (g t) :=
      (finite_fiber_degree_pullback f g t (hfin (g t))).2
    have hc := isClosed_fiber_degree_le n f' hlqf' hn r
    let V : Set (S.affineCover.X i) :=
      {t | (f'.fiberToSpecResidueField t).finrankΓ ≤ r}ᶜ
    refine ⟨g '' V, ?_, g.isOpenEmbedding.isOpenMap _ hc.isOpen_compl, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      change ¬ δ (g t) ≤ r
      simpa only [V, Set.mem_compl_iff, Set.mem_ofPred_eq, hdeg] using ht
    · obtain ⟨t, ht⟩ := S.affineCover.covers s
      refine ⟨t, ?_, ht⟩
      change ¬ (f'.fiberToSpecResidueField t).finrankΓ ≤ r
      rw [hdeg, ht]
      exact hs
  let Z : ℕ → Set S
    | 0 => ∅
    | r + 1 => {s | δ s ≤ r}
  have hstratum (r : ℕ) : Z (r + 1) \ Z r = {s | δ s = r} := by
    ext s
    cases r with
    | zero => simp [Z]
    | succ r =>
      simp only [Z, Set.mem_sdiff, Set.mem_ofPred_eq]
      omega
  have hfree : ∀ (T : Scheme.{u}) (g : T ⟶ S) (r : ℕ),
      (pullback.snd f g).IsFiniteLocallyFreeOfDegree r ↔
        Set.range g ⊆ {s : S | δ s = r} := by
    intro T g r
    constructor
    · intro h
      have := h
      rintro s ⟨t, rfl⟩
      change (f.fiberToSpecResidueField (g t)).finrankΓ = r
      rw [← (finite_fiber_degree_pullback f g t (hfin (g t))).2]
      exact h.fiberDegree_eq t
    · intro h
      let f' := pullback.snd f g
      have hlqf' : IsLocallyQuasiFinite f' := (separated_lqf_base_change f g).2 h_lqf
      have hdeg (t : T) : (f'.fiberToSpecResidueField t).finrankΓ = r := by
        rw [(finite_fiber_degree_pullback f g t (hfin (g t))).2]
        exact h (Set.mem_range_self t)
      have hr : BoundsFiberDegrees f' r := fun t ↦
        ⟨(finite_fiber_degree_pullback f g t (hfin (g t))).1, (hdeg t).le⟩
      obtain ⟨U, hU, hfinite⟩ :=
        exists_isFinite_morphismRestrict_maximal_fiber_degree f' hlqf' r hr
      have : IsFinite f' :=
        IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsFinite)
          (fun t ↦ ⟨U, (hU t).mpr (hdeg t), hfinite⟩)
      have : f'.IsFiniteLocallyFree := {}
      exact { fiberDegree_eq := fun t ↦ hdeg t }
  refine ⟨Z, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    cases r with
    | zero => exact isClosed_empty
    | succ r => exact hclosed r
  · intro a b hab
    cases a with
    | zero => exact Set.empty_subset _
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        intro s hs
        exact Nat.le_trans hs (by omega)
  · intro r t hrt
    rw [hstratum r, hstratum t, Set.disjoint_left]
    intro s hs ht
    exact hrt (hs.symm.trans ht)
  · simp_rw [hstratum]
    ext s
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨δ s, rfl⟩
  · intro T g r
    rw [hstratum]
    exact hfree T g r
  · intro r W hW
    rw [hstratum]
    have hupper : ∀ n : ℕ,
        IsCompact ({s : S | n ≤ δ s} ∩ (W : Set S)) := by
      intro n
      induction n with
      | zero => simpa only [Nat.zero_le, Set.ofPred_true, Set.univ_inter] using hW
      | succ n ih =>
        have hopen : IsOpen ({s : S | n ≤ δ s} ∩ (W : Set S)) := by
          have ho : IsOpen {s : S | n ≤ δ s} := by
            cases n with
            | zero => simpa only [Nat.zero_le, Set.ofPred_true] using isOpen_univ (X := S)
            | succ n =>
              have heq : {s : S | n + 1 ≤ δ s} = {s : S | δ s ≤ n}ᶜ := by
                ext s
                simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
                omega
              rw [heq]
              exact (hclosed n).isOpen_compl
          exact ho.inter W.isOpen
        obtain ⟨A, hA, hcover⟩ :=
          isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨ih, hopen⟩
        have hsub (U : S.affineOpens) (hU : U ∈ A) :
            (U : Set S) ⊆ {s : S | n ≤ δ s} ∩ (W : Set S) := by
          rw [hcover]
          exact Set.subset_iUnion_of_subset U (Set.subset_iUnion_of_subset hU Set.Subset.rfl)
        have hcompact (U : S.affineOpens) (hU : U ∈ A) :
            IsCompact ({s : S | n + 1 ≤ δ s} ∩ (U : Set S)) :=
          isCompact_successor_degree_locus_inter_affine f hf n U.1 U.2
            (hclosed n) (hfree · · n) (fun s hs ↦ (hsub U hU hs).1)
        have heq : {s : S | n + 1 ≤ δ s} ∩ (W : Set S) =
            ⋃ U ∈ A, {s : S | n + 1 ≤ δ s} ∩ (U : Set S) := by
          ext s
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
          constructor
          · rintro ⟨hs, hw⟩
            have hm : s ∈ {s : S | n ≤ δ s} ∩ (W : Set S) := ⟨Nat.le_trans (Nat.le_succ n) hs, hw⟩
            rw [hcover] at hm
            rcases Set.mem_iUnion.mp hm with ⟨U, hm⟩
            rcases Set.mem_iUnion.mp hm with ⟨hU, hsU⟩
            exact ⟨U, hU, hs, hsU⟩
          · rintro ⟨U, hU, hs, hsU⟩
            exact ⟨hs, (hsub U hU hsU).2⟩
        rw [heq]
        exact hA.isCompact_biUnion hcompact
    have heq : {s : S | δ s = r} ∩ (W : Set S) =
        ({s : S | r ≤ δ s} ∩ (W : Set S)) ∩ {s : S | δ s ≤ r} := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h, hw⟩
        exact ⟨⟨h.ge, hw⟩, h.le⟩
      · rintro ⟨⟨hge, hw⟩, hle⟩
        exact ⟨Nat.le_antisymm hle hge, hw⟩
    rw [heq]
    exact (hupper r).inter_right (hclosed r)

end AlgebraicGeometry.Scheme.Hom
