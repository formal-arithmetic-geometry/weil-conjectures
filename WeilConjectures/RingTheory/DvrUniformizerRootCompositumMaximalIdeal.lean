/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import WeilConjectures.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra
import WeilConjectures.RingTheory.DvrStandardRootUnramifiedModel
import WeilConjectures.RingTheory.DvrUnramifiedCompositumBaseChange


/-! # Weak unramifiedness over a uniformizer-root base

## References

* Stacks Project, Tag 0BRM (the last two paragraphs), Tags 09EV, 09EQ and 09E7
-/

@[expose] public section

universe u
namespace RingTheory

/-- The root case of tame ramification cancellation, including further DVR base change. Let
`π` be a uniformizer of the DVR `B`, `θ ∈ A` an `e`-th root of `π` in a DVR `A` over `B`, with `e`
a unit in `B`, and `U` a DVR local over `B` with `m_B U = m_U ^ e` and separable residue field
extension. Let `E` be the fraction field of `U`, finite separable over `Frac B`, and `F` a field
over `A` generated over `A` by the image of `E`. Then any DVR `T` local over `A` with fraction
field `F` and compatible local map `U → T` is essentially of finite type and formally unramified
over `A`. -/
theorem dvr_uniformizer_root_compositum_formallyUnramifiedData
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (pi : B) (hpi : Irreducible pi)
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra B A]
    (U : Type u) [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [Algebra B U] [IsLocalHom (algebraMap B U)]
    (e : ℕ) (he : IsUnit (e : B))
    (theta : A) (hroot : theta ^ e = algebraMap B A pi)
    (hindexU : (IsLocalRing.maximalIdeal B).map (algebraMap B U) =
      IsLocalRing.maximalIdeal U ^ e)
    (hsep : Algebra.IsSeparable (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField U))
    (E : Type u) [Field E] [Algebra (FractionRing B) E]
    [Algebra B E] [IsScalarTower B (FractionRing B) E]
    [FiniteDimensional (FractionRing B) E] [Algebra.IsSeparable (FractionRing B) E]
    [Algebra U E] [IsFractionRing U E] [IsScalarTower B U E]
    (F : Type u) [Field F] [Algebra A F] (iE : E →+* F)
    (hcomm : ∀ b : B, iE (algebraMap B E b) =
      algebraMap A F (algebraMap B A b))
    (hgen : Algebra.adjoin A (Set.range iE) = ⊤)
    (T : Type u) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra A T] [IsLocalHom (algebraMap A T)]
    [Algebra T F] [IsFractionRing T F] [IsScalarTower A T F]
    (j : U →+* T) (hj : IsLocalHom j)
    (hjB : ∀ b : B, j (algebraMap B U b) =
      algebraMap A T (algebraMap B A b))
    (hjE : ∀ c : U, algebraMap T F (j c) = iE (algebraMap U E c)) :
    Algebra.EssFiniteType A T ∧ Algebra.FormallyUnramified A T := by
  classical
  have _ := hcomm
  have hepos : 0 < e := by
    by_contra h
    have he0 : e = 0 := Nat.eq_zero_of_not_pos h
    simp [he0] at he
  obtain ⟨q, hq⟩ := IsDiscreteValuationRing.exists_irreducible U
  have hassoc : Associated (q ^ e) (algebraMap B U pi) := by
    apply Ideal.span_singleton_eq_span_singleton.mp
    rw [← Ideal.span_singleton_pow, ← hq.maximalIdeal_eq, ← hindexU,
      hpi.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  obtain ⟨w, hw⟩ := hassoc
  let f := (Polynomial.X : Polynomial B) ^ e - Polynomial.C pi
  let R := AdjoinRoot f
  obtain ⟨hdomR, hdvrR, hmaxR⟩ :=
    AlgebraicGeometry.Scheme.dvr_uniformizer_root_algebra B pi hpi e hepos
  let := hdomR
  let := hdvrR
  let a : R →+* A := AdjoinRoot.lift (f := f) (algebraMap B A) theta (by
    simpa only [f, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, sub_eq_zero] using hroot)
  let : Algebra R A := a.toAlgebra
  let rho : R →+* T := (algebraMap A T).comp a
  have hrhoB : ∀ b : B, rho (algebraMap B R b) = j (algebraMap B U b) := by
    intro b
    change algebraMap A T (a (AdjoinRoot.of f b)) = _
    rw [show a (AdjoinRoot.of f b) = algebraMap B A b from AdjoinRoot.lift_of _]
    exact (hjB b).symm
  have hpower : rho (AdjoinRoot.root f) ^ e = (j q) ^ e * j (w : U) := by
    rw [show rho (AdjoinRoot.root f) = algebraMap A T theta from
      congrArg (algebraMap A T) (AdjoinRoot.lift_root _), ← map_pow, hroot]
    rw [← hjB, ← hw, map_mul, map_pow]
  have hassocT : Associated ((j q) ^ e) (rho (AdjoinRoot.root f) ^ e) := by
    rw [hpower]
    exact associated_mul_unit_right _ _ (w.isUnit.map j)
  have hassocRoot : Associated (j q) (rho (AdjoinRoot.root f)) := by
    apply dvd_dvd_iff_associated.mp
    exact ⟨(UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hepos.ne').mp hassocT.dvd,
      (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hepos.ne').mp hassocT.symm.dvd⟩
  obtain ⟨y, hy⟩ := hassocRoot
  have htmem : rho (AdjoinRoot.root f) ∈ IsLocalRing.maximalIdeal T := by
    rw [← hy]
    apply Ideal.mul_mem_right
    let := hj
    exact map_nonunit j q (by
      rw [hq.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self q)
  have hrho : IsLocalHom rho := by
    apply ((IsLocalRing.local_hom_TFAE rho).out 4 1).mp
    rw [hmaxR]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr htmem)
  let := hrho
  have ha : IsLocalHom (algebraMap R A) :=
    isLocalHom_of_comp a (algebraMap A T)
  let := ha
  obtain ⟨V, hringV, hdomV, hdvrV, aRV, hRV, hfaithV, hfiniteV, hunramV,
    k, _hk, hkR, iV, iEV, hiV, hiEV⟩ :=
    dvr_standard_root_unramified_model B pi hpi U e he hsep E T F iE j hj hjE
      q hq w hw hdomR hdvrR rho hrho hrhoB y hy
  have hgenV : Algebra.adjoin A (Set.range iV) = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_mono
    rintro _ ⟨x, rfl⟩
    exact ⟨iEV x, hiEV x⟩
  exact dvr_unramified_compositum_base_change R V A T k hkR F iV hiV hgenV


/-- In the setting of `dvr_uniformizer_root_compositum_formallyUnramifiedData`, the maximal ideal
of `A` generates the maximal ideal of `T`. -/
theorem dvr_uniformizer_root_compositum_map_maximalIdeal
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (pi : B) (hpi : Irreducible pi)
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra B A]
    (U : Type u) [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [Algebra B U] [IsLocalHom (algebraMap B U)]
    (e : ℕ) (he : IsUnit (e : B))
    (theta : A) (hroot : theta ^ e = algebraMap B A pi)
    (hindexU : (IsLocalRing.maximalIdeal B).map (algebraMap B U) =
      IsLocalRing.maximalIdeal U ^ e)
    (hsep : Algebra.IsSeparable (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField U))
    (E : Type u) [Field E] [Algebra (FractionRing B) E]
    [Algebra B E] [IsScalarTower B (FractionRing B) E]
    [FiniteDimensional (FractionRing B) E] [Algebra.IsSeparable (FractionRing B) E]
    [Algebra U E] [IsFractionRing U E] [IsScalarTower B U E]
    (F : Type u) [Field F] [Algebra A F] (iE : E →+* F)
    (hcomm : ∀ b : B, iE (algebraMap B E b) =
      algebraMap A F (algebraMap B A b))
    (hgen : Algebra.adjoin A (Set.range iE) = ⊤)
    (T : Type u) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra A T] [IsLocalHom (algebraMap A T)]
    [Algebra T F] [IsFractionRing T F] [IsScalarTower A T F]
    (j : U →+* T) (hj : IsLocalHom j)
    (hjB : ∀ b : B, j (algebraMap B U b) =
      algebraMap A T (algebraMap B A b))
    (hjE : ∀ c : U, algebraMap T F (j c) = iE (algebraMap U E c)) :
    (IsLocalRing.maximalIdeal A).map (algebraMap A T) = IsLocalRing.maximalIdeal T := by
  have h := dvr_uniformizer_root_compositum_formallyUnramifiedData B pi hpi A U e he theta hroot
    hindexU hsep E F iE hcomm hgen T j hj hjB hjE
  set_option linter.style.haveILetI false in
    haveI : Algebra.EssFiniteType A T := h.1
  set_option linter.style.haveILetI false in
    haveI : Algebra.FormallyUnramified A T := h.2
  exact Algebra.FormallyUnramified.map_maximalIdeal


end RingTheory
