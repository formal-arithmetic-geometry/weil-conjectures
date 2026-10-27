/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Sheaf.RingTheory.CompleteDVRFiniteNormalization
import Sheaf.AlgebraicGeometry.ComponentwiseNormalizationAffineCharts
import Sheaf.AlgebraicGeometry.ComponentwiseNormalizationProperties
import Sheaf.RingTheory.CommonFiniteTraitExtension
import Sheaf.AlgebraicGeometry.FiniteInseparableGeometricReduction
import WeilConjectures.AlgebraicGeometry.Curve.ReductionNilradicalNilpotence
import Sheaf.RingTheory.DvrNormalGenericReducedSpecial
import Sheaf.RingTheory.RaynaudFaltingsNormalizedReduction
import WeilConjectures.RingTheory.NagataOfCompleteLocal
import WeilConjectures.RingTheory.NagataUniversallyJapanese
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal
import Sheaf.AlgebraicGeometry.NormalizationGeonormalInsep
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Normalized reduced base change over a complete trait

Source: Prasad--Yu, Appendix by Brian Conrad, Theorem A.2 and Remark A.3, p.28;
Stacks Project, Tag 09IL and its preceding normalized-base-change construction.
(blueprint: lem-sfb-complete-trait-normalized-reduced-fibres).

The three abbreviations below name the actual reduction and its two structure maps;
they make no choices of models or normalization maps.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The reduction of the base change to the integral closure in `L`.
Source: Conrad Appendix A.2; Stacks Tag 09IL
(blueprint: lem-sfb-complete-trait-normalized-reduced-fibres). -/
noncomputable abbrev Scheme.Hom.reducedTraitBaseChange
    {D : Type u} [CommRing D] {X : Scheme.{u}} (f : X ⟶ Spec (.of D))
    (L : Type u) [Field L] [Algebra D L] : Scheme.{u} :=
  (pullback f (Spec.map (CommRingCat.ofHom
    (algebraMap D (integralClosure D L))))).nilradical.subscheme

/-- The canonical map from the reduction to the spectrum of the new trait ring.
Source: Conrad Appendix A.2; Stacks Tag 09IL
(blueprint: lem-sfb-complete-trait-normalized-reduced-fibres). -/
noncomputable abbrev Scheme.Hom.reducedTraitBaseChangeToBase
    {D : Type u} [CommRing D] {X : Scheme.{u}} (f : X ⟶ Spec (.of D))
    (L : Type u) [Field L] [Algebra D L] :
    f.reducedTraitBaseChange L ⟶ Spec (.of (integralClosure D L)) :=
  (pullback f (Spec.map (CommRingCat.ofHom
    (algebraMap D (integralClosure D L))))).nilradical.subschemeι ≫
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap D (integralClosure D L))))

/-- The canonical structure map of the componentwise normalization of the reduction.
Source: Conrad Appendix A.2; Stacks Tag 09IL
(blueprint: lem-sfb-complete-trait-normalized-reduced-fibres). -/
noncomputable abbrev Scheme.Hom.normalizedTraitBaseChangeToBase
    {D : Type u} [CommRing D] {X : Scheme.{u}} (f : X ⟶ Spec (.of D))
    (L : Type u) [Field L] [Algebra D L] :
    (f.reducedTraitBaseChange L).reducedNormalization ⟶ Spec (.of (integralClosure D L)) :=
  (f.reducedTraitBaseChange L).fromReducedNormalization ≫ f.reducedTraitBaseChangeToBase L

/-- Normalized reduced base change after a finite, possibly inseparable field extension
has a geometrically reduced special fibre and geometrically normal generic fibre.
Source: Conrad Appendix A.2 and A.3, p.28; Stacks Tag 09IL and Varieties Tags 04KT, 0BXT.
(blueprint: lem-sfb-complete-trait-normalized-reduced-fibres).

Proof:
1. For any intermediate finite extension K/F, its integral closure W is a finite complete
   DVR dominating D, with fraction field K, by lem-per-complete-dvr-finite-normalization.
   Base change preserves flatness, separatedness and finite type. On an affine chart T,
   if rho*t is nilpotent, flatness implies t is nilpotent. Thus T_red is torsion free,
   hence flat over the PID W (lem-weil-pbc-pid-torsion-free-module-flat). Reduction is
   finite and preserves separatedness and finite type.
2. Completeness makes W Nagata and universally Japanese. The affine charts of the
   componentwise normalization are products of integral closures of minimal-prime
   quotients (lem-per-componentwise-normalization-affine-charts). Each is finite by
   universal Japaneseness. Hence normalization is finite and, by
   lem-per-componentwise-normalization-properties, normal and surjective. Its source
   is separated and of finite type.
3. The uniformizer is a nonzerodivisor in each reduced chart and remains so in its total
   fraction ring and normalization. Thus normalization is W-flat by the PID criterion.
   Reduction commutes with inverting the uniformizer, directly from the nilpotence
   criterion; normalization does by integral-closure localization. These comparisons
   agree on overlaps. Zero rings and empty fibres are allowed.
4. Apply lem-pur-finite-inseparable-geometric-reduction to X_F, then
   lem-weil-pbc-normalization-geonormal-insep to its reduced base change. This gives K/F
   finite with reduced generic fibre geometrically reduced and normalized generic fibre
   geometrically normal. Nilpotence of the Noetherian nilradical identifies the reduced
   generic fibres after further extension. By lem-sfb-geonormal-normalization-field-extension,
   generic normalization persists under every further field extension.
5. Cover the resulting normalization N_0 by finitely many affine charts E_i. Apply
   lem-sfb-raynaud-faltings-normalized-reduction to each chart. By
   lem-per-epp-common-finite-trait-extension choose a common finite complete trait V;
   for an empty cover keep W_0. Its fraction field L is finite over F. Uniqueness in
   lem-per-complete-dvr-finite-normalization identifies V with integralClosure D L.
6. Base change each affine output C_i to V, obtaining P_i finite over E_i tensor V,
   V-flat, with normal generic fibre and geometrically reduced special fibre. By
   lem-sfb-dvr-normal-generic-reduced-special, P_i is normal. Flatness embeds it into
   its generic ring. By lem-weil-pbc-normal-ring-integrally-closed-total and the common
   total fraction ring after inverting the uniformizer, P_i is exactly the integral
   closure of E_i tensor V. The affine normalization formula then gives the required
   reduced closed fibre of the normalization of (N_0)_V.
7. The base change of H_0 is flat with reduced generic fibre, hence reduced by torsion
   freeness. Nilpotence of the original nilradical identifies it with H=(X_V)_red.
   On affine charts A subset B of H_0 and its normalization, A_V and B_V have the same
   total fraction ring: their generic rings do by step 4, and the uniformizer is regular.
   Since B_V is integral over A_V, their integral closures in this ring coincide by
   transitivity of integrality. These comparisons glue, identifying the normalization
   in step 6 with H.reducedNormalization. Steps 1--4 give every remaining clause.
-/
theorem exists_completeTrait_normalized_reduced_fibres
    (D : Type u) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
    (F : Type u) [Field F] [Algebra D F] [IsFractionRing D F]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of D))
    [Flat f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F L) (_ : Algebra D L)
      (_ : IsScalarTower D F L) (_ : IsDiscreteValuationRing (integralClosure D L)),
      Module.Finite F L ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure D L)) (integralClosure D L) ∧
      IsFractionRing (integralClosure D L) L ∧
      Module.Finite D (integralClosure D L) ∧
      (IsLocalRing.maximalIdeal (integralClosure D L)).comap
        (algebraMap D (integralClosure D L)) = IsLocalRing.maximalIdeal D ∧
      Flat (f.reducedTraitBaseChangeToBase L) ∧
      IsSeparated (f.reducedTraitBaseChangeToBase L) ∧
      LocallyOfFiniteType (f.reducedTraitBaseChangeToBase L) ∧
      QuasiCompact (f.reducedTraitBaseChangeToBase L) ∧
      Flat (f.normalizedTraitBaseChangeToBase L) ∧
      IsSeparated (f.normalizedTraitBaseChangeToBase L) ∧
      LocallyOfFiniteType (f.normalizedTraitBaseChangeToBase L) ∧
      QuasiCompact (f.normalizedTraitBaseChangeToBase L) ∧
      IsFinite (f.reducedTraitBaseChange L).fromReducedNormalization ∧
      Surjective (f.reducedTraitBaseChange L).fromReducedNormalization ∧
      GeometricallyReduced (pullback.snd (f.reducedTraitBaseChangeToBase L)
        (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure D L) L)))) ∧
      (∀ (Ω : Type u) [Field Ω] [Algebra L Ω],
        ∀ z : ↥(pullback (f.normalizedTraitBaseChangeToBase L)
          (Spec.map (CommRingCat.ofHom
            ((algebraMap L Ω).comp (algebraMap (integralClosure D L) L))))),
          IsDomain ((pullback (f.normalizedTraitBaseChangeToBase L)
            (Spec.map (CommRingCat.ofHom
              ((algebraMap L Ω).comp (algebraMap (integralClosure D L) L))))).presheaf.stalk z) ∧
          IsIntegrallyClosed ((pullback (f.normalizedTraitBaseChangeToBase L)
            (Spec.map (CommRingCat.ofHom
              ((algebraMap L Ω).comp (algebraMap (integralClosure D L) L))))).presheaf.stalk z)) ∧
      GeometricallyReduced (pullback.snd (f.normalizedTraitBaseChangeToBase L)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (integralClosure D L))))) := by
  sorry

end AlgebraicGeometry
