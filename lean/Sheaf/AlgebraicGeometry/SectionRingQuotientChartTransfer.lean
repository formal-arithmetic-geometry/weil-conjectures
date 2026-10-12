/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.AlgebraicGeometry.InvertibleSectionRing
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Verification of section-ring quotients on a second chart

Source: Stacks Project, Constructions, Tags 01N8 and 01NK.
(blueprint: lem-sc-section-ring-quotient-chart-transfer).
-/

@[expose] public section

universe v
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The coefficient equation on the chosen chart determines all other chart equations.
Source: Stacks Project, Constructions, Tag 01N8, proof, comparison on intersecting charts;
Tag 01NK, proof, passing between different positive degrees.
(blueprint: lem-sc-section-ring-quotient-chart-transfer).

Proof: Work locally on U where L has a basis z, and write s = b z^d and t = c z^e.
Since s generates L^{tensor d}, b is a unit. The coefficient equation says the map on
S_(s) sends a/s^n to the coefficient of a divided by b^n. The Proj chart intersection
D_+(s) intersect D_+(t) is the basic open of t^d/s^e in Spec S_(s). Its pullback is the
unit locus of c^d/b^e, which equals the unit locus of c. The map on this intersection
is the localization of the map on S_(s), since q has that map on global sections.
For xi in degree ne the identity of fractions
xi/t^n = (xi t^{n(d-1)}/s^{ne}) / (t^d/s^e)^n
shows that its pullback is the coefficient of xi divided by c^n: the factors b^{ne}
and c^{n(d-1)} cancel. Multiplying by t^n gives xi. A positive power is a unit exactly
when its base is a unit, so this works in arbitrary local rings, including rings with
nilpotents. Changes of z preserve the equation; the sheaf separation axiom glues these
local equations on the ambient image in X. For n=0 the same fraction identity has unit
denominator and is the degree-zero coefficient equation. Empty chart intersections
have unique sections, so their equations are automatic. -/
theorem sectionRing_quotient_chart_transfer
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) (hd : 0 < d) (U : X.Opens)
    (hs : IsFreeGenerator ((L.tensorPow d).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op (s.val d)))
    (ρ : HomogeneousLocalization.Away (sectionRingGrade L) s.val →+* Γ(X, U))
    (hρ : ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
      ρ (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
          ξ.val ξ.property) •
        (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          ((s.val ^ n) (n • d)) =
      (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (ξ.val (n • d)))
    (q : U.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away
      (sectionRingGrade L) s.val)))
    (hq : (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away
        (sectionRingGrade L) s.val))).inv ≫ q.appTop =
      CommRingCat.ofHom ρ ≫ U.topIso.inv) :
    let g := q ≫ Proj.awayι (sectionRingGrade L) s.val s.property hd
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
