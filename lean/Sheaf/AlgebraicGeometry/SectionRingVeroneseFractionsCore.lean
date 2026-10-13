/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.InvertibleSectionRing
public import Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsFormula
public import Sheaf.AlgebraicGeometry.SectionFractionPresentation
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-! # Bijection for Veronese section fractions

The canonical map from the section-fraction presentation, sending a class
`[n, ξ]` to the homogeneous fraction `ξ / s^n`, is the inverse of the
constructed Veronese fraction equivalence.
Source: Stacks Project, Properties, Tags 0B5L, 01PW, and 01Q1.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical map from section-fraction classes to homogeneous fractions. -/
noncomputable def sectionRingVeroneseFractionCanonicalMap
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    SectionFractionPresentation (L.tensorPow d) (𝟙_ X.Modules) (s.val d) →+
      HomogeneousLocalization.Away (sectionRingGrade L) s.val :=
  (sectionRingVeroneseFractionEquiv X L d s).symm.toAddMonoidHom

/-- The canonical Veronese fraction map is bijective.
Source: Stacks Project, Properties, Tag 0B5L and Lemma 01PW(2).
(blueprint: lem-sc-section-ring-veronese-fractions-core)
The map sends the class represented by a numerator `ξ` in degree `n` to the
homogeneous localization fraction `ξ / s^n`.  It is the inverse of the
explicit quotient equivalence, so its bijectivity follows from that construction.
-/
theorem sectionRing_veronese_fraction_core
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    Function.Bijective
      (sectionRingVeroneseFractionCanonicalMap X L d s) := by
  exact (sectionRingVeroneseFractionEquiv X L d s).symm.bijective

end AlgebraicGeometry.Scheme.Modules
