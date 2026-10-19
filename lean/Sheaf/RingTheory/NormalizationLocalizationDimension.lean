/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Ideal.Height
import Sheaf.RingTheory.UniversallyCatenaryDimensionFormula

/-!
# Dimension of maximal localizations of a finite normalization

Source: Stacks Project, Algebra, Tag 02IJ (dimension formula), specialized to the finite
birational normalization; Greco, Two theorems on excellent rings (1976), Lemma 5.5,
printed p. 147 (blueprint: lem-exc-weakly-etale-normalization-dimension).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace IsUniversallyCatenary

/-- Every maximal localization of the finite normalization of a Noetherian universally
catenary local domain, at a maximal ideal contracting to its maximal ideal, has the
same Krull dimension as the domain.
Source: Stacks Project, Algebra, Tag 02IJ; Greco, Two theorems on excellent rings (1976),
Lemma 5.5, printed p. 147 (blueprint: lem-exc-weakly-etale-normalization-dimension).

Proof:
1. Set C' = integralClosure C K and p = maximalIdeal C. The injection C -> K
   factors through C', so C -> C' is injective. Module finiteness makes C' finite
   type and integral over C, hence algebraic, with transcendence degree zero.
2. Use the canonical residue-field map kappa(p) -> kappa(m). Its compatibility with
   C -> C' makes C -> kappa(p) -> kappa(m) a scalar tower. Since m is maximal,
   kappa(m) is a finite C'-module, hence a finite C-module. It is integral over C,
   therefore also integral and algebraic over kappa(p), with transcendence degree zero.
3. Apply lem-exc-dimension-formula-universally-catenary-finite-type-domain to C -> C',
   p and m. Both transcendence degrees vanish, giving height(m) = height(p).
4. Mathlib's IsLocalization.AtPrime.ringKrullDim_eq_height identifies dim(C'_m)
   with height(m), and IsLocalRing.maximalIdeal_height_eq_ringKrullDim identifies
   height(p) with dim(C). Combining gives the claim, including dimension zero.
-/
theorem ringKrullDim_localization_integralClosure_eq
    {C : Type u} [CommRing C] [IsNoetherianRing C] [IsLocalRing C] [IsDomain C]
    {K : Type v} [Field K] [Algebra C K] [IsFractionRing C K]
    [Module.Finite C (integralClosure C K)]
    (hC : IsUniversallyCatenary C)
    (m : Ideal (integralClosure C K)) [m.IsMaximal]
    (hm : m.comap (algebraMap C (integralClosure C K)) = IsLocalRing.maximalIdeal C) :
    ringKrullDim (Localization.AtPrime m) = ringKrullDim C := by
  let p := IsLocalRing.maximalIdeal C
  let f := Ideal.ResidueField.map p m (algebraMap C (integralClosure C K)) hm.symm
  let : Algebra p.ResidueField m.ResidueField := f.toAlgebra
  have : IsScalarTower C p.ResidueField m.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap C m.ResidueField x = f (algebraMap C p.ResidueField x)
      rw [Ideal.ResidueField.map_algebraMap]
      exact IsScalarTower.algebraMap_apply C (integralClosure C K) m.ResidueField x
  have : Module.Finite C m.ResidueField :=
    Module.Finite.trans (integralClosure C K) m.ResidueField
  have : Algebra.IsIntegral p.ResidueField m.ResidueField :=
    Algebra.IsIntegral.tower_top C
  have : Algebra.IsAlgebraic p.ResidueField m.ResidueField :=
    Algebra.IsIntegral.isAlgebraic
  have hres : Algebra.trdeg p.ResidueField m.ResidueField = 0 := trdeg_eq_zero
  have hnorm : Algebra.trdeg C (integralClosure C K) = 0 := trdeg_eq_zero
  have hinj : Function.Injective (algebraMap C (integralClosure C K)) := by
    intro x y hxy
    apply IsFractionRing.injective C K
    exact congrArg (fun z : integralClosure C K => (z : K)) hxy
  have hheight := height_add_trdeg_residueField_eq hC hinj p m hm.symm
  have heq : m.height = p.height := by
    simpa only [hres, hnorm, map_zero, add_zero] using hheight
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m, heq]
  exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim

end IsUniversallyCatenary
