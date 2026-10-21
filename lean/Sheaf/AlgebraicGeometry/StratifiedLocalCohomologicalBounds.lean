/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Data.Finset.Max

/-!
# Global cohomological bounds from finite stratified local bounds

Source: Bhatt--Scholze, The pro-etale topology for schemes, Proposition 6.6.11,
reverse implication (finite-stratum locality); Stacks Tags 04ZA, 0989, 04JC and 09AH.
Lemma 6.5.3 is contextual: the argument here concerns arbitrary ring sheaves.
(blueprint: lem-sfb-stratified-local-cohomological-bounds).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Local intervals on pro-etale covers of finitely many strata give a global interval.
The selected opens retain their labels in the original covering family. The lower
endpoint is a lower bound attained among the selected lower endpoints, and the upper
endpoint is an upper bound attained among the selected upper endpoints. These are
exactly the finite minimum and maximum; when there are no selected opens both are zero.
All restriction functors use the actual inverse-image ring, without scalar extension.

Source: Bhatt--Scholze, Proposition 6.6.11, reverse-implication locality argument;
Stacks Tags 04ZA, 0989, 04JC, 010N, 015F, 09AH and 09AB.
(blueprint: lem-sfb-stratified-local-cohomological-bounds).

Proof:
1. A finite affine cover by spectra of Noetherian rings makes X locally Noetherian
and quasi-compact. Every subset of a Noetherian space is quasi-compact. An immersion
is a homeomorphism onto its image, so every stratum is quasi-compact too.
2. Choose a finite affine open cover of each stratum. The pro-etale covering
condition over each affine supplies finitely many affine opens of covering members
whose images cover it. These are quasi-compact opens of the original members;
covering transitivity makes all their composites a covering of the stratum. There
are only finitely many strata, hence finitely many selected opens in total.
3. Inverse image over the actual inverse-image ring is exact. Its termwise functor
therefore commutes with cohomology, degree by degree, also for unbounded complexes.
Composition of inverse images identifies restriction to a selected open with the
further restriction from its original covering member. Thus its original interval
still bounds its cohomology.
4. Take the minimum of the finitely many selected lower bounds and the maximum of
the upper bounds. Every original lower bound is at most its upper bound, so the
minimum is at most the maximum. Outside this interval all selected restrictions
have zero cohomology. For an empty selected family put both endpoints equal to zero.
5. Apply finite-stratum detection to the underlying abelian sheaf of H^q(K).
Its inverse images on the selected covering opens vanish by steps 3 and 4, hence
it is zero. A module sheaf with zero underlying abelian sheaf is zero. This also
handles empty strata and the empty scheme via the empty-cover sheaf axiom. No
flatness of K, dimension bound, constancy or completeness of the ring is used. -/
theorem exists_global_bounds_of_stratified_local_bounds
    (X : Scheme.{u}) [IsNoetherian X] (S : FiniteLocallyClosedStratification X)
    (V : ∀ α : Fin S.n, Scheme.Cover.{w} proetalePrecoverage (S.domain α))
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (K : DerivedCategory (ringedSiteModules.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))
    (lower upper : ∀ α : Fin S.n, (V α).I₀ → ℤ)
    (hinterval : ∀ (α : Fin S.n) (j : (V α).I₀), lower α j ≤ upper α j)
    (hlocal : ∀ (α : Fin S.n) (j : (V α).I₀) (q : ℤ),
      q < lower α j ∨ upper α j < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((proEtaleAllRingDerivedInverseImage ((V α).f j ≫ S.immersion α)
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj K))) :
    ∃ (m : Fin S.n → ℕ) (label : ∀ α : Fin S.n, Fin (m α) → (V α).I₀)
      (W : ∀ (α : Fin S.n) (k : Fin (m α)), ((V α).X (label α k)).Opens),
      (∀ (α : Fin S.n) (k : Fin (m α)), IsCompact (W α k : Set ((V α).X (label α k)))) ∧
      (∀ α : Fin S.n,
        Presieve.ofArrows (fun k : Fin (m α) ↦ (W α k).toScheme)
          (fun k ↦ (W α k).ι ≫ (V α).f (label α k)) ∈ proetalePrecoverage (S.domain α)) ∧
      ∃ a b : ℤ, a ≤ b ∧
        (∀ (α : Fin S.n) (k : Fin (m α)), a ≤ lower α (label α k)) ∧
        (∀ (α : Fin S.n) (k : Fin (m α)), upper α (label α k) ≤ b) ∧
        ((∃ α : Fin S.n, Nonempty (Fin (m α))) →
          (∃ (α : Fin S.n) (k : Fin (m α)), a = lower α (label α k)) ∧
          (∃ (α : Fin S.n) (k : Fin (m α)), b = upper α (label α k))) ∧
        ((∀ α : Fin S.n, m α = 0) → a = 0 ∧ b = 0) ∧
        ∀ q : ℤ, q < a ∨ b < q →
          IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := by
  classical
  let (α : Fin S.n) : IsImmersion (S.immersion α) := S.isImmersion α
  let (α : Fin S.n) : TopologicalSpace.NoetherianSpace (S.domain α) :=
    (S.immersion α).isEmbedding.noetherianSpace
  let (α : Fin S.n) : IsLocallyNoetherian (S.domain α) :=
    LocallyOfFiniteType.isLocallyNoetherian (S.immersion α)
  -- Compact strata let us refine each cover by finitely many affine opens.
  have hrefine (α : Fin S.n) := QuasiCompactCover.exists_isAffineOpen_of_isCompact
    (V α).toPreZeroHypercover
    (show IsCompact ((⊤ : (S.domain α).Opens) : Set (S.domain α)) from isCompact_univ)
  choose m label W haff hcov using hrefine
  have hsurj (α : Fin S.n) (x : S.domain α) :
      ∃ k y, y ∈ W α k ∧ (V α).f (label α k) y = x := by
    have hx : x ∈ ⋃ k, (V α).f (label α k) '' (W α k : Set _) := by
      rw [hcov α]
      trivial
    simpa only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe] using hx
  let C (α : Fin S.n) : Scheme.Cover (precoverage @WeaklyEtale) (S.domain α) :=
    Cover.mkOfCovers (Fin (m α)) (fun k ↦ (W α k).toScheme)
      (fun k ↦ (W α k).ι ≫ (V α).f (label α k))
      (fun x ↦ by
        obtain ⟨k, y, hy, heq⟩ := hsurj α x
        exact ⟨k, ⟨y, hy⟩, heq⟩)
      (fun k ↦ by
        have : WeaklyEtale ((V α).f (label α k)) :=
          (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1
            (V α).mem₀.2 |>.2 (label α k)
        infer_instance)
  let (α : Fin S.n) (k : Fin (m α)) : IsAffine (W α k).toScheme := haff α k
  let (α : Fin S.n) (k : (C α).I₀) : QuasiCompact ((C α).f k) := by
    change Fin (m α) at k
    change QuasiCompact ((W α k).ι ≫ (V α).f (label α k))
    exact quasiCompact_of_compactSpace _
  let (α : Fin S.n) : Finite (C α).I₀ :=
    inferInstanceAs (Finite (Fin (m α)))
  let (α : Fin S.n) : QuasiCompactCover (C α).toPreZeroHypercover :=
    QuasiCompactCover.of_finite
  have hC (α : Fin S.n) :
      (C α).presieve₀ ∈ proetalePrecoverage (S.domain α) :=
    ⟨presieve₀_mem_qcPrecoverage_iff.mpr inferInstance, (C α).mem₀⟩
  -- The original members selected by these opens still form a pro-etale cover.
  let E (α : Fin S.n) : PreZeroHypercover (S.domain α) :=
    { I₀ := Fin (m α)
      X k := (V α).X (label α k)
      f k := (V α).f (label α k) }
  let (α : Fin S.n) : QuasiCompactCover (E α) :=
    QuasiCompactCover.of_hom (𝒰 := E α) (𝒱 := (C α).toPreZeroHypercover)
      { s₀ k := k
        h₀ k := (W α k).ι }
  let V' (α : Fin S.n) : Scheme.Cover proetalePrecoverage (S.domain α) :=
    { __ := E α
      mem₀ := ⟨presieve₀_mem_qcPrecoverage_iff.mpr inferInstance,
        (ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).mpr ⟨fun x ↦ by
          obtain ⟨k, y, _, heq⟩ := hsurj α x
          exact ⟨k, y, heq⟩,
          fun k ↦ (ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).mp
            (V α).mem₀.2 |>.2 (label α k)⟩⟩ }
  let S' := Stratification.ofNoetherianSpace S.n S.stratum S.isLocallyClosed_stratum
    S.iUnion_stratum_eq_univ S.pairwise_disjoint_stratum S.domain S.immersion
    S.isImmersion S.range_immersion
  let R' := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  -- Detect a cohomology module by viewing it as a derived object in degree zero.
  have hdetect (q : ℤ)
      (hq : ∀ (α : Fin S.n) (k : Fin (m α)),
        q < lower α (label α k) ∨ upper α (label α k) < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := by
    let M := (DerivedCategory.homologyFunctor _ q).obj K
    have hs : IsZero ((DerivedCategory.singleFunctor _ 0).obj M) := by
      apply (proEtale_derived_stratum_cover_detection X S' V' R').1
      intro α k
      let P := proEtaleRingModuleInverseImage ((V α).f (label α k) ≫ S.immersion α) R'
      have hm : IsZero (P.obj M) :=
        (hlocal α (label α k) q (hq α k)).of_iso
          ((P.mapDerivedCategoryHomologyFunctorIso q).app K)
      exact ((DerivedCategory.singleFunctor _ 0).map_isZero hm).of_iso
        ((P.mapDerivedCategorySingleFunctor 0).app M)
    exact ((DerivedCategory.homologyFunctor _ 0).map_isZero hs).of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).symm.app M)
  refine ⟨m, label, W, fun α k ↦ (haff α k).isCompact, hC, ?_⟩
  -- Take attained extrema on the finite family, with [0, 0] for the empty family.
  let T := Σ α : Fin S.n, Fin (m α)
  by_cases ht : Nonempty T
  · let : Nonempty T := ht
    have huniv : (Finset.univ : Finset T).Nonempty := Finset.univ_nonempty
    obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
      (fun t : T ↦ lower t.1 (label t.1 t.2)) huniv
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
      (fun t : T ↦ upper t.1 (label t.1 t.2)) huniv
    have hlo (α : Fin S.n) (k : Fin (m α)) :
        lower i.1 (label i.1 i.2) ≤ lower α (label α k) := hi ⟨α, k⟩ (Finset.mem_univ _)
    have hup (α : Fin S.n) (k : Fin (m α)) :
        upper α (label α k) ≤ upper j.1 (label j.1 j.2) := hj ⟨α, k⟩ (Finset.mem_univ _)
    refine ⟨lower i.1 (label i.1 i.2), upper j.1 (label j.1 j.2),
      (hinterval _ _).trans (hup _ _), hlo, hup, ?_, ?_, ?_⟩
    · exact fun _ ↦ ⟨⟨i.1, i.2, rfl⟩, ⟨j.1, j.2, rfl⟩⟩
    · intro hempty
      have hlt := i.2.isLt
      have hz := hempty i.1
      omega
    · intro q hq
      apply hdetect q
      intro α k
      rcases hq with hq | hq
      · exact Or.inl (hq.trans_le (hlo α k))
      · exact Or.inr ((hup α k).trans_lt hq)
  · have hempty (α : Fin S.n) (k : Fin (m α)) : False := ht ⟨⟨α, k⟩⟩
    refine ⟨0, 0, le_rfl, ?_, ?_, ?_, fun _ ↦ ⟨rfl, rfl⟩, ?_⟩
    · exact fun α k ↦ (hempty α k).elim
    · exact fun α k ↦ (hempty α k).elim
    · rintro ⟨α, ⟨k⟩⟩
      exact (hempty α k).elim
    · exact fun q _ ↦ hdetect q (fun α k ↦ (hempty α k).elim)

end AlgebraicGeometry.Scheme
