/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.InvertibleSectionRing
public import Sheaf.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Sheaf.Paper.NonvanishingSectionTrivializes

/-! # Constructing a section-ring morphism with the fraction formula

Source: Stacks Project, Properties, Tag 01PZ, and Constructions, Tag 01N8.
-/

@[expose] public section

universe v
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The local quotient maps glue to a morphism with the homogeneous fraction formula.
This states the construction and the algebraic formula, without its inverse-image clause.
Source: Stacks Project, Properties, Tag 01PZ, proof; Constructions, Tag 01N8, construction
of the local quotient maps (blueprint: lem-sc-ample-proj-canonical-map-chart-formula).

Proof: For each positive-degree section s, trivialize its tensor power on X_s by
nonvanishing_section_trivializes. Tensoring this trivialization constructs division by
s^n, including on the empty open and for n = 0. Send a homogeneous fraction a/s^n to
the coefficient of a in that basis. Equality of fractions can be checked after multiplying
by a power of s; this becomes cancellation of a free generator, so the map is well-defined.
The tensor multiplication laws give additivity, multiplicativity, and preservation of one.
The affine morphism correspondence and the Proj chart isomorphism turn this ring map into
a morphism X_s to D_+(s). For sections s and t of degrees d and e, the function t^d/s^e
on D_+(s) pulls back to the same quotient of sections. Its unit locus is X_s intersect X_t,
by the residue-field criterion for nonvanishing. On that intersection the two maps factor
through D_+(st). A fraction a/(st)^n pulls back to division by (st)^n from either side,
so the affine morphism correspondence proves their agreement. Glue over the assumed
cover using Scheme.Cover.glueMorphisms. The chart pullbacks restrict on each covering open
to the constructed quotient maps. Their fraction identities therefore agree locally and
hence globally as sections of the relevant tensor power. -/
theorem exists_sectionRing_proj_chart_formula (X : Scheme.{v}) (L : X.Modules)
    [L.IsInvertible]
    (hcover : ∀ x : X, ∃ (d : ℕ) (s : sectionRingGrade L d),
      0 < d ∧ x ∈ nonvanishingLocus (L.tensorPow d) (s.val d)) :
    ∃ f : X ⟶ Proj (sectionRingGrade L),
      ∀ (d : ℕ) (_hd : 0 < d) (s : sectionRingGrade L d),
        ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
          (f.app (Proj.basicOpen (sectionRingGrade L) s.val)
            (Proj.awayToSection (sectionRingGrade L) s.val
              (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
                ξ.val ξ.property))) •
            (L.tensorPow (n • d)).presheaf.map (homOfLE
              (le_top : f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val ≤ ⊤)).op
              ((s.val ^ n) (n • d)) =
          (L.tensorPow (n • d)).presheaf.map (homOfLE
              (le_top : f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val ≤ ⊤)).op
            (ξ.val (n • d)) := by sorry

end AlgebraicGeometry.Scheme.Modules
