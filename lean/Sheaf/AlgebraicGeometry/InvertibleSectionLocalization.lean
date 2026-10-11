/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.AlgebraicGeometry.SectionFractionPresentation
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import Sheaf.AlgebraicGeometry.Ample
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Localization of sections at a section of an invertible module

Source: Stacks Project, Properties, Lemma 01PW (lemma-invert-s-sections), part (2),
equation module-invert-s (blueprint: lem-sc-p1-invertible-section-localization).
-/

universe uL

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Degree-zero section fractions identify canonically with sections on the nonvanishing
open. The fraction formula is written without choosing an inverse tensor power:
`e(t/s^n) ⊗ s^n = t|_U`. Scalar compatibility specifies an isomorphism of modules,
with scalars restricted along `Γ(X, O_X) → Γ(U, O_X)`.
Source: Stacks Project, Properties, Lemma 01PW (lemma-invert-s-sections), part (2).
(blueprint: lem-sc-p1-invertible-section-localization).

Step 1: if a fraction restricts to zero, its numerator restricts to zero because `s`
trivializes `L` on this open. Apply lem-sc-p1-section-restriction-s-torsion to obtain a
power of `s` killing the numerator; the fraction relations then kill the fraction.
Step 2: for a section on this open, lem-sc-p1-section-clearing-denominators-qcqs gives a
nonnegative exponent and a global twisted numerator whose restriction is the section
multiplied by that power of `s`. This fraction maps to the original section.
The tensor construction is additive and commutes with scalar restriction. -/
theorem exists_sectionFraction_nonvanishing_equiv
    (X : Scheme.{uL}) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ U : X.Opens, (U : Set X) = nonvanishingLocus L s ∧
      ∃ e : SectionFractionPresentation L F s ≃+ Γ(F, U),
        (∀ (r : Γ(X, ⊤)) (z : SectionFractionPresentation L F s),
          e (r • z) = (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) • e z) ∧
        (∀ (n : ℕ) (t : Γ(F ⊗ L.tensorPow n, ⊤)),
          tmulSection (e (sectionFraction L F s n t))
              (tensorPowSectionOne (homOfGlobalSection L s) n U) =
            (F ⊗ L.tensorPow n).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op t) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
