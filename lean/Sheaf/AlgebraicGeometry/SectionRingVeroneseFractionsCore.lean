/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.InvertibleSectionRing
import Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsFormula
public import Sheaf.AlgebraicGeometry.SectionFractionPresentation
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-! # Additive equivalence for Veronese section fractions

Reuse the existing constructed Veronese fraction equivalence as the witness
of the core nonemptiness statement.
Source: Stacks Project, Properties, Tags 0B5L, 01PW, and 01Q1.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- Core additive equivalence for the Veronese fraction presentation.
Source: Stacks Project, Properties, Tag 0B5L and Lemma 01PW(2).
(blueprint: lem-sc-section-ring-veronese-fractions-core)
The equivalence is obtained by identifying each homogeneous summand with the
corresponding tensor-power section summand and quotienting by the transition relations.
-/
theorem sectionRing_veronese_fraction_core
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    Nonempty (HomogeneousLocalization.Away (sectionRingGrade L) s.val ≃+
      SectionFractionPresentation (L.tensorPow d) (𝟙_ X.Modules) (s.val d)) := by
  exact ⟨sectionRingVeroneseFractionEquiv X L d s⟩

end AlgebraicGeometry.Scheme.Modules
