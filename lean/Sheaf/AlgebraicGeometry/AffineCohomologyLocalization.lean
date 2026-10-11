/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.AlgebraicGeometry.CohomologyFractionPresentation
import Sheaf.AlgebraicGeometry.Ample
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Localization of cohomology on an affine scheme

Source: Stacks Project, Cohomology of Schemes, Lemma 09MR, affine-open paragraph of
its proof; Properties, Tags 01PV and 01PW; Cohomology of Schemes, Tag 01XB
(blueprint: lem-sc-invert-s-cohomology-affine-case).
-/

universe uAffine

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- On an affine scheme the canonical degree-zero fraction comparison is an isomorphism
in every cohomological degree, and both groups vanish in positive degrees.
The canonical formula is expressed as `s^n e(ξ/s^n) = ξ|_U`: multiplication by `s^n`
is induced on cohomology by `F ≅ F ⊗ O_Y → F ⊗ L^n`. On the nonvanishing open it is
invertible, so this says exactly `e(ξ/s^n) = s⁻ⁿ ξ|_U`.

Source: Stacks Project, Cohomology of Schemes, Lemma 09MR, affine case
(blueprint: lem-sc-invert-s-cohomology-affine-case).
Proof:
1. By lem-sc-affine-cap-section-open, the nonvanishing open `Y_s` is affine.
2. By lem-sc-invertible-tensor-qcoherent, each integer twist of `F` is quasi-coherent.
Apply pqf-lem-affine-vanishing on `Y` to all twists, and on `Y_s` to the restriction
of `F`, quasi-coherent by lem-weil-pbc-module-restriction-open-immersion-colimits.
Thus all positive-degree numerator groups, their direct sum and its fraction quotient,
and the target group vanish.
3. For degree zero apply lem-sc-affine-section-localization (Stacks 01PW). Its formula
`ξ/s^n ↦ s⁻ⁿ ξ` is the displayed cohomology formula under the degree-zero identification
with sections. In positive degrees the unique map between zero groups is the comparison.
The additive isomorphism with this fraction formula is automatically compatible with
scalar multiplication, since restriction and tensor multiplication are linear. -/
theorem affine_cohomology_localization
    (Y : Scheme.{uAffine}) [IsAffine Y]
    (L : Y.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (F : Y.Modules) [F.IsQuasicoherent] :
    ∃ U : Y.Opens, (U : Set Y) = nonvanishingLocus L s ∧
      ∀ p : ℕ,
        (∃ e : CohomologyFractionPresentation L F s p ⊤ ≃+
            (RingedSpace.openModuleCohomology Y.toRingedSpace p U).obj F,
          ∀ (n : ℕ)
              (t : (RingedSpace.openModuleCohomology Y.toRingedSpace p ⊤).obj
                (F ⊗ L.tensorPow n : Y.Modules)),
            (RingedSpace.openModuleCohomology Y.toRingedSpace p U).map
                (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
                  F ⟶ (F ⊗ L.tensorPow n : Y.Modules))
                (e (cohomologyFraction L F s p ⊤ n t)) =
              (RingedSpace.openModuleCohomologyRestriction Y.toRingedSpace p
                (homOfLE (le_top : U ≤ ⊤))).app (F ⊗ L.tensorPow n : Y.Modules) t) ∧
        (0 < p → Subsingleton (CohomologyFractionPresentation L F s p ⊤) ∧
          Subsingleton ((RingedSpace.openModuleCohomology Y.toRingedSpace p U).obj F)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
