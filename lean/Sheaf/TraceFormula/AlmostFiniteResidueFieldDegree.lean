/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q150
-/
module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Sheaf.RingTheory.AdicCompletionNoetherianOfQuotient
import Sheaf.RingTheory.NormalizationCompletedBranchLift
import Sheaf.RingTheory.NagataOfCompleteLocal
import Sheaf.RingTheory.JapaneseDomain

/-!
# Finite residue field degrees for almost finite integral extensions

Source: Swanson--Huneke, *Integral Closure of Ideals, Rings, and Modules*,
Proposition 4.8.5, printed p. 85 (blueprint: lem-trf-almost-finite-residue-field-degree).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u v

@[expose] public section

namespace RingTheory

/-- The canonical map on fraction fields induced by a prime quotient of an
integral overring.  This is the fraction-field map of the injective quotient
map `R ⧸ Q.comap (algebraMap R C) → C ⧸ Q`.

Source: Swanson--Huneke, Proposition 4.8.5, residue-field fraction maps
(blueprint: lem-trf-almost-finite-residue-field-degree). -/
noncomputable def quotientFractionRingMap
    (R : Type u) (C : Type v) [CommRing R] [CommRing C] [Algebra R C]
    (Q : Ideal C) [Q.IsPrime] :
    FractionRing (R ⧸ Q.comap (algebraMap R C)) →+*
      FractionRing (C ⧸ Q) := by
  let g : (R ⧸ Q.comap (algebraMap R C)) →+* FractionRing (C ⧸ Q) :=
    (algebraMap (C ⧸ Q) (FractionRing (C ⧸ Q))).comp
      (Ideal.quotientMap Q (algebraMap R C) le_rfl)
  apply IsFractionRing.lift (g := g)
  exact (IsFractionRing.injective (C ⧸ Q) (FractionRing (C ⧸ Q))).comp
    (Ideal.quotientMap_injective)

/-- An integral subring of a finite extension of a Noetherian domain has finite
residue-field fraction degree at every prime.

Source: Swanson--Huneke, Proposition 4.8.5, printed p. 85
(blueprint: lem-trf-almost-finite-residue-field-degree).

Proof:
1. Scale a finite basis of `F` over `FractionRing R` to integral elements by clearing
   denominators in monic equations. Their `R`-algebra `A` is module-finite by
   `lem-sc-finite-generated-integral-subring`, Noetherian by
   `lem-weil-pbc-finite-algebra-noetherian`, and has fraction field `F`.
2. Put `D = integralClosure R F`. Both `A` and `C` lie in `D`. Lying over
   (`lem-weil-pbc-integral-injective-lying-over`) gives `N` above `Q`; set `a = N ∩ A`.
   Then `C/Q` embeds in `D/N`. Integrality transitivity
   (`lem-weil-pbc-integral-transitive`) identifies `D` with the integral closure of `A`.
3. Quotient generators show that `A/a` is finite over `R/P`, where `P = Q ∩ R`.
   The lemma `lem-trf-finite-domain-fraction-degree` gives finite degree of their
   fraction fields `k₁/k₀`.
4. Localize `A` at `a`, obtaining the Noetherian local domain `U`, with residue field
   `k₁` and fraction field `F` (`def-weil-pbc-localization-at-prime`,
   `lem-weil-pbc-localization-noetherian`). Its normalization `E` is the localization
   of `D` (`lem-weil-pbc-integral-closure-commutes-localization`). The prime induced
   by `N` lies over the maximal ideal of `U`, and its quotient has the same fraction
   field as `D/N`.
5. Complete `U` at its maximal ideal. The result `H` is Noetherian and complete
   (`lem-weil-pbc-completion-noetherian-quotient-noetherian`), and is local with
   unchanged residue field `k₁` (`lem-weil-pbc-local-completion-local-ring`).
6. Apply `lem-trf-normalization-completed-branch-lift`: for some minimal prime `p`
   of `H`, the branch normalization `T` admits a compatible map from `E` and a
   prime `M` whose contraction is the chosen prime of `E`. Thus `E/q` embeds in
   `T/M`, compatibly with the maps from `k₁`.
7. Completeness makes `H` Nagata (`lem-weil-pbc-complete-local-nagata`). Hence
   `H/p` is N-2 (`def-weil-pbc-japanese-domain`), so `T` is finite over `H/p`.
   Quotient generators make `T/M` finite over `k₁`; the fraction-degree lemma
   gives finite degree of `k₂ = Frac(T/M)` over `k₁`.
8. The quotient injections extend to fraction-field injections, compatibly over `k₀`.
   Products of finite spanning sets for `k₂/k₁` and `k₁/k₀` span `k₂/k₀`.
   Its subfield `Frac(C/Q)` is therefore finite dimensional over `k₀`.
-/
theorem almostFinite_residueField_fractionDegree
    (R : Type u) (F : Type v) [CommRing R] [IsNoetherianRing R] [IsDomain R]
    [Field F] [Algebra R F] [Algebra (FractionRing R) F]
    [IsScalarTower R (FractionRing R) F]
    [FiniteDimensional (FractionRing R) F]
    (C : Subalgebra R F) (hC : C ≤ integralClosure R F)
    (Q : Ideal C) [Q.IsPrime] :
    @FiniteDimensional (FractionRing (R ⧸ Q.comap (algebraMap R C)))
      (FractionRing (C ⧸ Q)) _ _
      (Module.compHom (FractionRing (C ⧸ Q)) (quotientFractionRingMap R C Q)) := by
  sorry

end RingTheory

end
