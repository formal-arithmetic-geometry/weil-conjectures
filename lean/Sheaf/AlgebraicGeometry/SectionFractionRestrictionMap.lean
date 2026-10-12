/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.SectionFractionPresentation
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Restriction and division of section fractions

Source: Stacks Project, Properties, Lemma 01PW (lemma-invert-s-sections), canonical map.
(blueprint: lem-sc-p1-section-fraction-restriction-map)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite DirectSum

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction followed by division by a free generator descends to the fraction quotient.
Source: Stacks Project, Properties, Lemma 01PW (lemma-invert-s-sections), the canonical
map in part (2). (blueprint: lem-sc-p1-section-fraction-restriction-map)

Proof: On `U`, each tensor power of `s` is a free generator. Tensoring with it is a
bijection on sections for every module `F`. Its inverse is additive and linear over
`Γ(U, O_X)`, since tensoring is linear. Compose that inverse with restriction in each
numerator degree. The resulting maps are additive and linear along scalar restriction.
The tensor-power addition isomorphism shows that division of `t` by `s^n` agrees with
division of `t ⊗ s^b` by `s^(n+b)`. Thus the direct-sum map kills every generator of
`sectionFractionRelations`, hence its span, and descends to the quotient. On the
quotient generators it satisfies the displayed tensor formula; scalar compatibility
follows from linearity along restriction. No compactness or quasi-coherence is used.
-/
theorem exists_sectionFraction_restriction_map {X : Scheme.{u}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (U : X.Opens)
    (hs : IsFreeGenerator ((homOfGlobalSection L s).app U (unitSectionsEquiv U 1))) :
    ∃ f : SectionFractionPresentation L F s →+ Γ(F, U),
      (∀ (r : Γ(X, ⊤)) (z : SectionFractionPresentation L F s),
        f (r • z) = (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) • f z) ∧
      (∀ (n : ℕ) (t : Γ(F ⊗ L.tensorPow n, ⊤)),
        tmulSection (f (sectionFraction L F s n t))
            (tensorPowSectionOne (homOfGlobalSection L s) n U) =
          (F ⊗ L.tensorPow n).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op t) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
