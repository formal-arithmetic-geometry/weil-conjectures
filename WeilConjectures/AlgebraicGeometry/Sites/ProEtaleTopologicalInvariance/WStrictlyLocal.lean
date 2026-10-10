/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleTopologicalInvariance.Retraction
public import WeilConjectures.RingTheory.ProEtale.WStrictLocalization
public import WeilConjectures.RingTheory.ProEtale.RetractionsStrictlyHenselian

/-!
# Base change of the w-strict localization along a universal homeomorphism

Let `A → B` be a ring map such that `Spec B ⟶ Spec A` is a universal homeomorphism. We show
that the base change `WStrictLocalization A ⊗[A] B` of the w-strict localization of `A` is again
w-strictly local. Its spectrum is homeomorphic to that of `WStrictLocalization A`, so it is
w-local, and its local rings at closed points are those of the base change of the ind-étale
contraction `IndEtaleContraction (WLocalization A)`, which has retractions of all faithfully
flat étale algebras by `Algebra.IsUniversalHomeomorphism.exists_retraction_of_etale`.

This lets the proof of Stacks 097Z be run over `B` with a w-strictly local cover that is the
base change of one over `A`, which is the key to the topological invariance of the small
pro-étale site.

## Main statements

- `RingHom.IndZariski.isStableUnderBaseChange`: ind-Zariski ring maps are stable under base
  change.
- `AlgebraicGeometry.Algebra.IsUniversalHomeomorphism.isWStrictlyLocalRing_tensorProduct`: the
  base change of `WStrictLocalization A` along a universal homeomorphism `A → B` is w-strictly
  local.
-/

@[expose] public section

universe u

open PrimeSpectrum TensorProduct

/-- Ind-Zariski ring homomorphisms are stable under base change. -/
lemma RingHom.IndZariski.isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange RingHom.IndZariski := by
  intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ hpush hRS
  rw [iff_ind_isLocalIso] at hRS ⊢
  rw [← CommRingCat.isPushout_iff_isPushout] at hpush
  exact (inferInstance : (CategoryTheory.MorphismProperty.ind
    (RingHom.toMorphismProperty RingHom.IsLocalIso)).IsStableUnderCobaseChange).1 hpush.flip hRS

namespace WStrictLocalization

variable (R : Type u) [CommRing R]

/-- A maximal ideal of the w-strict localization lies over a maximal ideal of the ind-étale
contraction of the w-localization. -/
lemma isMaximal_comap_algebraMap (n : Ideal (WStrictLocalization R)) [hn : n.IsMaximal] :
    (n.comap (algebraMap (IndEtaleContraction (WLocalization R))
      (WStrictLocalization R))).IsMaximal := by
  have : n.IsPrime := hn.isPrime
  set B' := IndEtaleContraction (WLocalization R)
  have hn_mem : (⟨n, inferInstance⟩ : PrimeSpectrum (WStrictLocalization R)) ∈
      zeroLocus ((closedIdeal R).map
        (algebraMap (WLocalization R) (WStrictLocalization R))) := by
    rw [zeroLocus_map_eq_closedPoints]
    exact (isClosed_singleton_iff_isMaximal _).mpr hn
  set q : Ideal B' := n.comap (algebraMap B' (WStrictLocalization R)) with hq_def
  have : q.IsPrime := Ideal.IsPrime.comap _
  have hq_mem : (⟨q, inferInstance⟩ : PrimeSpectrum B') ∈ zeroLocus (contractionIdeal R) := by
    rw [mem_zeroLocus] at hn_mem ⊢
    intro x hx
    have : algebraMap B' (WStrictLocalization R) x ∈ n := by
      apply hn_mem
      have : (closedIdeal R).map (algebraMap (WLocalization R) (WStrictLocalization R)) =
          (contractionIdeal R).map (algebraMap B' (WStrictLocalization R)) := by
        rw [contractionIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
      rw [this]
      exact Ideal.mem_map_of_mem _ hx
    exact this
  have hq_closed : (⟨q, inferInstance⟩ : PrimeSpectrum B') ∈ closedPoints (PrimeSpectrum B') :=
    zeroLocus_map_algebraMap_subset_closedPoints
      (fun _ _ ↦ inferInstance) (zeroLocus_closedIdeal R).le hq_mem
  exact (isClosed_singleton_iff_isMaximal _).mp hq_closed

end WStrictLocalization

namespace AlgebraicGeometry.Algebra.IsUniversalHomeomorphism

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [_root_.Algebra.IsUniversalHomeomorphism A B]

/-- The map on spectra induced by a universal homeomorphism of rings is a homeomorphism. -/
lemma isHomeomorph_comap : IsHomeomorph (PrimeSpectrum.comap (algebraMap A B)) :=
  isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨PrimeSpectrum.continuous_comap _,
      PrimeSpectrum.isClosedMap_comap_of_isIntegral _
        (algebraMap_isIntegral_iff.mpr inferInstance),
      comap_bijective A B⟩

/-- A ring which is a universal homeomorphism over a w-local ring is w-local. -/
lemma isWLocalRing [IsWLocalRing A] : IsWLocalRing B :=
  ⟨(isHomeomorph_comap A B).isEmbedding.wLocalSpace_of_stableUnderSpecialization_range
    (by rw [(isHomeomorph_comap A B).surjective.range_eq]; exact stableUnderSpecialization_univ)⟩

/-- **The base change of the w-strict localization along a universal homeomorphism is
w-strictly local.** -/
instance isWStrictlyLocalRing_tensorProduct :
    IsWStrictlyLocalRing (WStrictLocalization A ⊗[A] B) := by
  set C := WStrictLocalization A
  set W := WLocalization A
  set K := IndEtaleContraction W
  let _ : Algebra A K := Algebra.compHom K (algebraMap A W)
  have : IsScalarTower A W K := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A K C := IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [show algebraMap A C x = algebraMap W C (algebraMap A W x) from rfl,
      IsScalarTower.algebraMap_apply W K C]
    rfl
  have : IsWLocalRing (C ⊗[A] B) := isWLocalRing C (C ⊗[A] B)
  refine ⟨fun n hn ↦ ?_⟩
  -- the ring map `K ⊗[A] B → C ⊗[A] B`, the base change of the ind-Zariski `K → C`
  let φ : K ⊗[A] B →ₐ[A] C ⊗[A] B :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A K C) (AlgHom.id A B)
  let _ : Algebra (K ⊗[A] B) (C ⊗[A] B) := φ.toRingHom.toAlgebra
  have : IsScalarTower K (K ⊗[A] B) (C ⊗[A] B) := .of_algebraMap_eq fun x ↦ by
    change algebraMap K C x ⊗ₜ[A] (1 : B) = φ (x ⊗ₜ[A] 1)
    simp [φ]
  have hpush : _root_.Algebra.IsPushout K C (K ⊗[A] B) (C ⊗[A] B) :=
    _root_.Algebra.IsPushout.tensorProduct_tensorProduct A B K C (RingHom.ext fun x ↦ by
      change φ (1 ⊗ₜ x) = 1 ⊗ₜ x
      simp [φ])
  have : _root_.Algebra.IndZariski K C :=
    inferInstanceAs <| _root_.Algebra.IndZariski _
      (WStrictLocalization.contractionIdeal A).WLocalization
  have hφ : (algebraMap (K ⊗[A] B) (C ⊗[A] B)).IndZariski :=
    RingHom.IndZariski.isStableUnderBaseChange K C (K ⊗[A] B) (C ⊗[A] B)
      ((RingHom.IndZariski.algebraMap_iff K C).mpr inferInstance)
  have : _root_.Algebra.IndZariski (K ⊗[A] B) (C ⊗[A] B) :=
    (RingHom.IndZariski.algebraMap_iff _ _).mp hφ
  -- `n` lies over a maximal ideal `q` of `K ⊗[A] B`
  have : n.IsPrime := hn.isPrime
  have hmC : (n.comap (algebraMap C (C ⊗[A] B))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n
  have hmK : ((n.comap (algebraMap C (C ⊗[A] B))).comap (algebraMap K C)).IsMaximal :=
    WStrictLocalization.isMaximal_comap_algebraMap A _
  set q : Ideal (K ⊗[A] B) := n.comap (algebraMap (K ⊗[A] B) (C ⊗[A] B)) with hq
  have : q.IsPrime := Ideal.IsPrime.comap _
  have hqK : q.comap (algebraMap K (K ⊗[A] B)) =
      (n.comap (algebraMap C (C ⊗[A] B))).comap (algebraMap K C) := by
    rw [hq, Ideal.comap_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
  have : q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q (hqK ▸ hmK)
  -- the local ring of `K ⊗[A] B` at `q` is strictly henselian
  have := IsStrictlyHenselianLocalRing.localization_atPrime_of_forall_retraction
    (A := K ⊗[A] B) (fun G _ _ hG hsurj ↦
      exists_retraction_of_etale (A := K) (B := K ⊗[A] B)
        (fun G _ _ hG hsurj ↦ RingHom.Etale.exists_comp_eq_id_indContraction (algebraMap _ G)
          (RingHom.etale_algebraMap.mpr hG) hsurj) G hsurj) q
  -- and it is identified with the local ring of `C ⊗[A] B` at `n`
  have hbos : _root_.Algebra.BijectiveOnStalks (K ⊗[A] B) (C ⊗[A] B) := inferInstance
  exact IsStrictlyHenselianLocalRing.of_ringEquiv
    (RingEquiv.ofBijective _ (hbos.bijective_localRingHom n))

end AlgebraicGeometry.Algebra.IsUniversalHomeomorphism
