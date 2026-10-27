/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Localization.Ideal
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Residual conormal injectivity at a separable regular affinoid point

Source: Conrad, Irreducible components of rigid spaces, section 1.1, printed p. 477,
and proof of Lemma 3.3.1, printed p. 510; the agent-formulated continuous conormal
consequence and localization argument recorded in the DAG
(blueprint: lem-per-separable-regular-affinoid-residual-conormal).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace RestrictedSeries

/-- The coefficient-field action on the quotient of a Tate algebra is induced by its
actual constant series and the quotient map.
Source: Conrad, Irreducible components of rigid spaces, section 1.1, printed p. 477
(blueprint: lem-per-separable-regular-affinoid-residual-conormal). -/
noncomputable instance quotientConstantsAlgebra
    (F : Type u) [NormedField F] [IsUltrametricDist F] (r : ℕ)
    (n : Ideal ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ)))) :
    Algebra F
      (↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) ⧸ n) :=
  ((Ideal.Quotient.mk n).comp (constants F r)).toAlgebra

/-- Termwise derivatives descend to an injective residue-field-linear residual conormal
map at a regular point with finite separable residue field. The witnesses `dg` are actual
restricted series whose underlying formal series are the formal partial derivatives;
thus the displayed formula specifies the map on every representative, without choosing
an arbitrary differential map or assuming regularity after a field extension.
Source: Conrad, Irreducible components of rigid spaces, section 1.1, printed p. 477,
and proof of Lemma 3.3.1, printed p. 510; the continuous conormal consequence in the
DAG's agent-formulated algebraic-localization version
(blueprint: lem-per-separable-regular-affinoid-residual-conormal).

Proof:
1. The coefficient of the ith derivative at nu is (nu_i + 1) times the coefficient
   at nu + e_i. Since every natural number has norm at most one, this series is
   restricted. The coefficient formula gives Leibniz. For a in n and g in I,
   both terms in D_i(ag) lie in n. Reduction therefore kills nI and is linear for
   the quotient action of kappa = T/n. This constructs the map d in the statement.
2. By lem-per-tate-separable-local-cotangent-coordinates, R = T_n is regular local
   and its cotangent space p/p^2 has derivative coordinates giving kappa^r.
   The localization/quotient identity lem-weil-pbc-localization-at-prime-of-quotient
   identifies R/IR with the given regular local ring (T/I)_(n/I).
3. The canonical map I/nI to IR/pIR sends g to g/1 and is an isomorphism. Every
   fraction g/u is congruent to ag with au = 1 modulo n. If g/1 vanishes, clearing
   denominators gives vug in nI with vu outside n; lifting its residue inverse b
   gives g = bvug + (1-bvu)g in nI. These maps respect residue scalars.
4. By lem-weil-pbc-regular-local-quotient-independent-generators, IR has finite
   generators u_j with independent classes in p/p^2. This uses regularity of R
   and of R/IR and IR contained in p.
5. Inclusion induces IR/pIR to p/p^2. Write an element as sum b_j u_j. If its
   cotangent class is zero, independence forces each b_j into p, so it belongs
   to pIR. Hence this inclusion map is injective, including the empty set of generators.
6. The composite of the isomorphism in step 3, the injection in step 5, and the
   coordinate isomorphism in step 2 has exactly the formula for d, so d is injective.
   For r = 0 the Tate algebra is F, forcing n = I = 0. For s = 0 or I = 0 the
   source is zero. No scalar extension of the quotient ring occurs. -/
theorem separable_regular_affinoid_residual_conormal
    (F : Type u) [NormedField F] [IsUltrametricDist F] [CompleteSpace F]
    (hF : ∃ a : F, a ≠ 0 ∧ ‖a‖ ≠ 1) (r s : ℕ)
    (f : Fin s → ↥(MvPowerSeries.IsRestricted.subring (R := F)
      (fun _ : Fin r ↦ (1 : ℝ))))
    (I : Ideal ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))))
    (hf : Ideal.span (Set.range f) = I)
    (n : Ideal ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))))
    [n.IsMaximal] (hIn : I ≤ n)
    [Module.Finite F
      (↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) ⧸ n)]
    [Algebra.IsSeparable F
      (↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) ⧸ n)]
    (hregular : IsRegularLocalRing
      (@Localization.AtPrime _ _ (n.map (Ideal.Quotient.mk I))
        (Ideal.isPrime_map_quotientMk_of_isPrime hIn))) :
    ∃ d : (I ⧸ n • (⊤ : Submodule
        ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) I)) →ₗ[
        ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) ⧸ n]
        (Fin r →
          ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) ⧸ n),
      Function.Injective d ∧
      ∀ (g : I) (i : Fin r),
        ∃ dg : ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))),
          dg.val = MvPowerSeries.pderiv F i g.val.val ∧
          d (Submodule.Quotient.mk g) i = Ideal.Quotient.mk n dg := by
  sorry

end RestrictedSeries
