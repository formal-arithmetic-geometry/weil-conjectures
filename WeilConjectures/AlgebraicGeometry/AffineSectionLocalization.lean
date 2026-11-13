/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SectionFractionPresentation
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.InvertibleSectionLocalization

/-!
# Degree-zero localization of sections on an affine scheme

Source: Stacks Project, Properties, Lemma 01PW, equation module-invert-s; Cohomology of
Schemes, Lemma 09MR, affine case.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- On an affine scheme the canonical map from degree-zero section fractions to sections on
the nonvanishing open `Y_s` is an isomorphism of modules
(Stacks, Tags 01PW and 09MR). -/
theorem affine_section_localization
    (Y : Scheme.{u}) [IsAffine Y]
    (L : Y.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (F : Y.Modules) [F.IsQuasicoherent] :
    ∃ U : Y.Opens, (U : Set Y) = nonvanishingLocus L s ∧
      ∃ e : SectionFractionPresentation L F s ≃+ Γ(F, U),
        (∀ (r : Γ(Y, ⊤)) (z : SectionFractionPresentation L F s),
          e (r • z) = (Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) • e z) ∧
        (∀ (n : ℕ) (t : Γ(F ⊗ L.tensorPow n, ⊤)),
          tmulSection (e (sectionFraction L F s n t))
              (tensorPowSectionOne (homOfGlobalSection L s) n U) =
            (F ⊗ L.tensorPow n).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op t) := by
  exact exists_sectionFraction_nonvanishing_equiv Y L s F

end AlgebraicGeometry.Scheme.Modules
