/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.Algebra.Prime.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Reducedness from smooth or nodal closed points

Source: Stacks Project, curves.tex, Tag 0E37, reducedness paragraph; algebra.tex,
Tags 00MC and 05CK; varieties.tex, Tag 0478.
(blueprint: lem-trf-nodal-points-reduced-algebraically-closed).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

-- Setting one coordinate to zero detects exactly divisibility by that coordinate.
private theorem X_dvd_iff_killCompl_eq_zero
    {σ : Type*} {R : Type*} [CommRing R] (s : σ) (p : MvPowerSeries σ R) :
    MvPowerSeries.X s ∣ p ↔
      MvPowerSeries.killCompl (Function.Embedding.subtype (· ≠ s)) p = 0 := by
  classical
  rw [MvPowerSeries.X_dvd_iff, MvPowerSeries.ext_iff]
  constructor
  · intro h m
    rw [MvPowerSeries.coeff_killCompl, map_zero]
    apply h
    exact Finsupp.embDomain_of_notMem_range _ _ _ (by simp)
  · intro h m hm
    have hr : m ∈ Set.range
        (Finsupp.embDomain (Function.Embedding.subtype (· ≠ s))) := by
      rw [Finsupp.mem_range_embDomain_iff]
      intro i hi
      simp only [Set.mem_range, Function.Embedding.subtype_apply, Subtype.exists,
        exists_prop, exists_eq_right]
      intro his
      subst i
      exact (Finsupp.mem_support_iff.mp hi) hm
    obtain ⟨n, rfl⟩ := hr
    simpa only [MvPowerSeries.coeff_killCompl, map_zero] using h n

-- The coordinate quotient is a power-series domain in the remaining variables.
private theorem prime_powerSeries_X
    {σ : Type*} {R : Type*} [CommRing R] [IsDomain R] (s : σ) :
    Prime (MvPowerSeries.X s : MvPowerSeries σ R) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := congrArg (MvPowerSeries.coeff (Finsupp.single s 1)) h
    simp at this
  · intro h
    have := h.map (MvPowerSeries.killCompl (R := R)
      (Function.Embedding.subtype (· ≠ s))).toRingHom
    change IsUnit (MvPowerSeries.killCompl
      (Function.Embedding.subtype (· ≠ s)) (MvPowerSeries.X s : MvPowerSeries σ R)) at this
    rw [MvPowerSeries.killCompl_X_eq_zero (by simp)] at this
    exact not_isUnit_zero this
  · intro a b hab
    simp only [X_dvd_iff_killCompl_eq_zero, map_mul, mul_eq_zero] at hab ⊢
    exact hab

-- The distinct prime factors X₀ and X₁ make their product generate a radical ideal.
private theorem nodalRing_isReduced (F : Type u) [Field F] :
    _root_.IsReduced (MvPowerSeries (Fin 2) F ⧸ Ideal.span
      {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) F) * MvPowerSeries.X 1}) := by
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  rw [Ideal.isRadical_iff_pow_one_lt 2 (by decide)]
  intro p hp
  rw [Ideal.mem_span_singleton] at hp ⊢
  have h0 := (prime_powerSeries_X (R := F) (0 : Fin 2)).dvd_of_dvd_pow
    (dvd_trans (dvd_mul_right _ _) hp)
  have h1 := (prime_powerSeries_X (R := F) (1 : Fin 2)).dvd_of_dvd_pow
    (dvd_trans (dvd_mul_left _ _) hp)
  obtain ⟨q, rfl⟩ := h0
  have hn : ¬ (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) F) ∣ MvPowerSeries.X 0 := by
    rw [MvPowerSeries.X_dvd_iff]
    push Not
    exact ⟨Finsupp.single 0 1, by simp, by simp⟩
  obtain ⟨r, rfl⟩ := ((prime_powerSeries_X (R := F) (1 : Fin 2)).dvd_or_dvd h1).resolve_left hn
  exact ⟨r, (mul_assoc _ _ _).symm⟩

/-- A scheme locally of finite type over an algebraically closed field is reduced if each
closed point without a smooth open neighbourhood has completed local ring `F[[u,v]]/(uv)`.
The completed-ring isomorphism need only be a ring isomorphism. No dimension, quasi-compactness,
separatedness, properness or nonemptiness hypothesis is required.

Source: Stacks Project, curves.tex, Tag 0E37, reducedness paragraph, using algebra.tex,
Tags 00MC and 05CK and varieties.tex, Tag 0478.
(blueprint: lem-trf-nodal-points-reduced-algebraically-closed).

Proof plan:
1. The field is Noetherian, and locally finite type over a locally Noetherian scheme implies
   locally Noetherian (pqf-def-locnoeth, pqf-lem-locnoeth-lft). Affine-stalk localization and
   localization-noetherian then show that every local ring is Noetherian
   (lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-localization-noetherian).
2. At a closed point with a smooth open neighbourhood, smooth geometric fibres are reduced
   (sbc-lem-smooth-geometrically-reduced). The identity field extension gives reducedness of
   that neighbourhood, and its stalk agrees with the ambient stalk (def-pc-reduced-scheme).
3. Restrict power series to the two axes. Both restrictions vanish exactly for multiples of
   uv: shift coefficients by (1,1). Thus the quotient by (uv) embeds into the product of the
   one-variable power-series domains (def-weil-pbc-multivariate-power-series,
   lem-weil-pbc-power-series-domain), and is reduced.
4. At a nonsmooth closed point the Noetherian local ring injects into its completion by
   faithful flatness (lem-weil-pbc-local-completion-faithfully-flat,
   lem-weil-pbc-faithfully-flat-ideal-contraction with the zero ideal). The given ring
   isomorphism and step 3 show its stalk is reduced.
5. Every point y has a closed specialization x (lem-sc-lft-over-field-jacobson-space).
   In an affine neighbourhood of x, also containing y, the primes satisfy q = p_y <= p_x = p
   (def-weil-affine-spectrum). Its stalks are B_q and B_p
   (lem-weil-pbc-affine-open-stalk-localization). If a/b in B_q is nilpotent, choose n >= 1
   and t outside q with t*a^n = 0. Then (t*a/1)^n = 0 in the reduced ring B_p, so t*a/1 = 0.
   Choose u outside p with u*t*a = 0. Since u*t is outside q, a/b = 0 in B_q
   (def-weil-pbc-localization-at-prime).
6. All stalks are reduced, hence the scheme is reduced (def-pc-reduced-scheme). The empty
   case is vacuous, and the argument uses neither a finite cover nor a dimension bound. -/
theorem isReduced_of_nodal_closed_points
    (F : Type u) [Field F] [IsAlgClosed F]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of F)) [LocallyOfFiniteType f]
    (hnodal : ∀ x : C, x ∈ closedPoints C →
      (¬ ∃ U : C.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)) →
      Nonempty
        (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
          (C.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) F ⧸ Ideal.span
            {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) F) * MvPowerSeries.X 1}))) :
    IsReduced C := by
  classical
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace f
  have hclosed (x : C) (hx : x ∈ closedPoints C) :
      _root_.IsReduced (C.presheaf.stalk x) := by
    by_cases hs : ∃ U : C.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)
    · obtain ⟨U, hxU, hsm⟩ := hs
      have : IsReduced U := isReduced_of_smooth (U.ι ≫ f)
      exact isReduced_of_injective (U.stalkIso ⟨x, hxU⟩).inv.hom
        (U.stalkIso ⟨x, hxU⟩).symm.commRingCatIsoToRingEquiv.injective
    · obtain ⟨e⟩ := hnodal x hx hs
      have := nodalRing_isReduced F
      have : _root_.IsReduced
          (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
            (C.presheaf.stalk x)) := isReduced_of_injective e e.injective
      have : Module.FaithfullyFlat (C.presheaf.stalk x)
          (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
            (C.presheaf.stalk x)) := Module.FaithfullyFlat.of_flat_of_isLocalHom
      exact isReduced_of_injective (algebraMap (C.presheaf.stalk x)
        (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
          (C.presheaf.stalk x))) (FaithfulSMul.algebraMap_injective _ _)
  have (i : C.affineCover.I₀) : IsReduced (C.affineCover.X i) := by
    let X := C.affineCover.X i
    let R := Γ(X, ⊤)
    let g : Spec R ⟶ C := X.isoSpec.inv ≫ C.affineCover.f i
    have : _root_.IsReduced R := isReduced_ofLocalizationMaximal R fun p hp ↦ by
      let x : Spec R := ⟨p, hp.isPrime⟩
      have hx : x ∈ closedPoints (Spec R) :=
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mpr hp
      have hg : g x ∈ closedPoints C := by
        have he := g.isOpenEmbedding.preimage_closedPoints
        exact (Set.ext_iff.mp he x).mpr hx
      have := hclosed (g x) hg
      have : _root_.IsReduced ((Spec R).presheaf.stalk x) :=
        isReduced_of_injective (asIso (g.stalkMap x)).inv.hom
          (asIso (g.stalkMap x)).symm.commRingCatIsoToRingEquiv.injective
      exact isReduced_of_injective (Spec.stalkIso R x).inv.hom
        (Spec.stalkIso R x).symm.commRingCatIsoToRingEquiv.injective
    exact isReduced_of_isAffine_isReduced X
  exact IsReduced.of_openCover C C.affineCover

end AlgebraicGeometry
