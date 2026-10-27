/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier
import Sheaf.AlgebraicGeometry.CartierDivisorFinite
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus

/-!
# Degree positivity from a section on a proper integral curve

Source: Stacks Project, Varieties, Tag 0B40, clauses (1) and (2), and Tag 0AYY
(blueprint: lem-trf-curve-section-degree-positivity).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A nonzero global section of an invertible module on a proper integral curve has
nonnegative degree; if its nonvanishing locus is not the whole curve, its degree is positive.

Source: Stacks Project, Varieties, Tag 0B40, clauses (1) and (2), using Tag 0AYY
(blueprint: lem-trf-curve-section-degree-positivity).

Proof:
1. The nonzero section has an effective Cartier zero ideal J by
   lem-pc-nonzero-section-integral-cartier. The zero-scheme/divisor isomorphism
   lem-pc-zero-scheme-divisor-iso identifies L with J.toModules dual.
2. Convert topological dimension one using lem-pc-scheme-dimension-local-rings.
   By lem-pc-cartier-divisor-finite-over-field, D = V(J) is affine and finite over k,
   and its coordinate ring is finite-dimensional.
3. Apply Euler-characteristic additivity to J tensor J-dual -> J-dual, using
   eulerChar_tensorObj_eq_add. Evaluation identifies J tensor J-dual with O_C.
   The quotient has the cohomology of the restriction of J-dual to D. Affine
   vanishing removes its positive cohomology; finrankH_zero_eq_finrankΓ_of_isFinite
   computes its degree-zero dimension as dim_k Gamma(D, O_D). Subtracting chi(O_C)
   gives degree(L) = dim_k Gamma(D, O_D), proving nonnegativity.
4. By lem-weil-pbc-section-nonvanishing-zero-locus and range_subschemeι, a proper
   nonvanishing locus makes D nonempty. A germ map at a point of D maps its global
   coordinate ring to a nontrivial local ring, so that coordinate ring is nontrivial.
   Its finite-dimensional k-vector-space dimension is therefore positive.
-/
theorem curve_section_degree_nonneg_and_pos (k : Type u) [Field k]
    (C : Scheme.{u}) [C.Over (Spec (.of k))] [IsIntegral C]
    [IsProper (C ↘ Spec (.of k))] (hC : topologicalKrullDim C = 1)
    (L : C.Modules) [L.IsInvertible] (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    0 ≤ L.degree k ∧ (nonvanishingLocus L s ≠ Set.univ → 0 < L.degree k) :=
  open scoped AlgebraicGeometry.Scheme.Modules in
  open CategoryTheory.Limits CategoryTheory.MonoidalCategory in
  by
    classical
    let J := (homOfGlobalSection L s).zeroLocus
    have hJ : J.IsInvertible := (nonzero_section_integral_cartier L s hs).2
    have hdim : C.dim ≤ 1 := by rw [C.dim_eq_topologicalKrullDim, hC]
    obtain ⟨_, _, _, hAff, hFin, hFD⟩ :=
      effectiveCartierDivisor_finite_over_field (k := k) C hdim J hJ
    let : J.subscheme.Over (Spec (.of k)) := ⟨J.subschemeι ≫ C ↘ Spec (.of k)⟩
    have : IsAffine J.subscheme := hAff
    have : IsFinite (J.subscheme ↘ Spec (.of k)) := hFin
    have := hJ.isInvertible_toModules
    have := hJ.isInvertible_dual_toModules
    have := IsInvertible.sheafOfModules_isInvertible L
    have := IsInvertible.sheafOfModules_isInvertible (tensorUnit C.Modules)
    obtain ⟨e⟩ := Hom.nonempty_iso_dual_toModules_tensorObj (homOfGlobalSection L s) hJ
    have he : L.degree k = J.toModulesᵛ.degree k := degree_congr k (e ≪≫ rightUnitor _)
    have hdeg : J.toModulesᵛ.degree k =
        (J.subschemeι ≫ C ↘ Spec (.of k)).finrankΓ := by
      have hadd := eulerChar_tensorObj_eq_add k J J.toModulesᵛ
      obtain ⟨d⟩ := nonempty_tensorObj_dual_iso_unit J.toModules
      rw [eulerChar_congr k (leftUnitor _), eulerChar_congr k d] at hadd
      have hzero : ((pullback J.subschemeι).obj J.toModulesᵛ).eulerChar k =
          (J.subscheme ↘ Spec (.of k)).finrankΓ := by
        let N := (pullback J.subschemeι).obj J.toModulesᵛ
        have hq (q : ℕ) (hq : q ≠ 0) : N.finrankH k q = 0 := by
          obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
          have := subsingleton_H_succ_of_isAffine N q
          exact Module.finrank_zero_of_subsingleton
        change N.eulerChar k = _
        rw [eulerChar, finsum_eq_single _ 0 (fun q h ↦ by rw [hq q h]; simp)]
        simpa using congrArg (fun n : ℕ ↦ (n : ℤ))
          (finrankH_zero_eq_finrankΓ_of_isFinite N)
      rw [hzero] at hadd
      change J.toModulesᵛ.eulerChar k = (tensorUnit C.Modules).eulerChar k +
        ((J.subschemeι ≫ C ↘ Spec (.of k)).finrankΓ : ℤ) at hadd
      change J.toModulesᵛ.eulerChar k - (tensorUnit C.Modules).eulerChar k = _
      linarith
    rw [he, hdeg]
    refine ⟨Int.natCast_nonneg _, ?_⟩
    intro hvan
    have hne : Nonempty J.subscheme := by
      by_contra h
      have hEmpty : IsEmpty J.subscheme := not_nonempty_iff.mp h
      apply hvan
      rw [nonvanishingLocus_eq_compl_support_zeroLocus]
      have hsupport : (J.support : Set C) = ∅ := by
        rw [← J.range_subschemeι]
        exact Set.range_eq_empty_iff.mpr hEmpty
      change (J.support.compl : Set C) = Set.univ
      exact (congrArg Set.compl hsupport).trans Set.compl_empty
    let := (J.subschemeι ≫ C ↘ Spec (.of k)).ΓAlgebra
    have : FiniteDimensional k Γ(J.subscheme, ⊤) := hFD
    obtain ⟨x⟩ := hne
    have : Nontrivial Γ(J.subscheme, ⊤) :=
      (J.subscheme.presheaf.germ ⊤ x trivial).hom.domain_nontrivial
    exact_mod_cast (Module.finrank_pos (R := k) (M := Γ(J.subscheme, ⊤)))

end AlgebraicGeometry.Scheme.Modules
