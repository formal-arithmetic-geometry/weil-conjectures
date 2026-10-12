/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.InvertibleSectionRing
public import Sheaf.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Sheaf.Paper.NonvanishingSectionTrivializes

/-! # A single quotient chart for an invertible section ring

Source: Stacks Project, Constructions, Tags 01N8 and 01NK.
-/

@[expose] public section

universe v
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A single positive-degree section gives a quotient morphism on its nonvanishing open.
No compatibility with a second morphism is asserted.
Source: Stacks Project, Constructions, Tags 01N8 (lemma-converse-construction),
01NK (lemma-invertible-map-into-proj).
(blueprint: lem-sc-section-ring-single-quotient-chart).

Proof: On U, s is a free generator of L^{tensor d}. Its n-th tensor power
trivializes L^{tensor nd}. Define the image of a/s^n in S_(s) to be the unique
coefficient of the restriction of a in this basis. The localization equivalence
relation says that two fractions become equal after multiplication by a power of s;
cancelling the corresponding free generator shows that their coefficients agree.
Additivity, multiplication and the unit follow from tensor multiplication and unique
coefficients. The resulting ring map S_(s) -> Gamma(U,O_X), followed by the affine
morphism correspondence and the basic-chart inclusion, defines g.

To verify the formula for an arbitrary t of degree e > 0, cover U by opens on which
L is free, with basis z. Write s = b z^d and t = c z^e. Here b is a unit.
The local ring map sends a/s^n to its coefficient divided by b^n. The chart function
t^d/s^e pulls back to c^d/b^e, so the inverse image of D_+(t) is exactly where c
is a unit. Localizing there, a fraction xi/t^n maps to the coefficient of xi divided
by c^n. Multiplication by the restricted t^n gives xi, which is the desired equation.
These equations agree on changes of z and hence glue as equations of sections.
For n = 0 this is the unit-degree coefficient map. On an empty U the section rings
are zero rings and the morphism and equations are unique. -/
theorem exists_sectionRing_single_quotient_chart
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) (hd : 0 < d) (U : X.Opens)
    (hU : (U : Set X) = nonvanishingLocus (L.tensorPow d) (s.val d)) :
    ∃ g : U.toScheme ⟶ Proj (sectionRingGrade L),
      ∀ (e : ℕ) (_he : 0 < e) (t : sectionRingGrade L e)
        (n : ℕ) (ξ : sectionRingGrade L (n • e)),
        (show Γ(X, U.ι ''ᵁ (g ⁻¹ᵁ
            Proj.basicOpen (sectionRingGrade L) t.val)) from
          g.app (Proj.basicOpen (sectionRingGrade L) t.val)
          (Proj.awayToSection (sectionRingGrade L) t.val
            (HomogeneousLocalization.Away.mk (sectionRingGrade L) t.property n
              ξ.val ξ.property))) •
          (L.tensorPow (n • e)).presheaf.map (homOfLE
            (le_top : U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
              ⊤)).op ((t.val ^ n) (n • e)) =
        (L.tensorPow (n • e)).presheaf.map (homOfLE
          (le_top : U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
            ⊤)).op (ξ.val (n • e)) := by sorry

end AlgebraicGeometry.Scheme.Modules
