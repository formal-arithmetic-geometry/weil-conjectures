/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.InvertibleSectionRing
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Clearing denominators between section-ring charts

Source: Stacks Project, Constructions, Tags 01N8 and 01NK.
(blueprint: lem-sc-section-ring-chart-cross-multiplication).
-/

@[expose] public section

universe v
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The numerator identity after clearing the second-chart denominator.
Source: Stacks Project, Constructions, Tag 01N8, comparison on overlapping charts;
Tag 01NK, passage between different positive degrees.
(blueprint: lem-sc-section-ring-chart-cross-multiplication).

Proof: Put k=n*(d-1), i=n*e and j=k*e. Then i+j=n*e*d.
On the chart intersection let r=t^d/s^e and η=ξ*t^k, so η has degree n*e*d.
The homogeneous-localization identity (ξ/t^n)*r^n=η/s^(n*e) follows by
multiplying numerators and denominators: n+k=n*d. Restrict this identity to
the intersection and pull it back along q. The chart restriction on the
s-side is localization at r; its map on sections agrees with ρ by hq.
Use hρ with exponent n*e and numerator η, and with exponent e and numerator t^d.
Locally write s=b*z^d and t=c*z^e in a basis z of L, where b is a unit.
The pulled-back identity becomes a*(c^d/b^e)^n=η_coeff/b^(n*e), where a is
exactly the displayed pullback of ξ/t^n. Multiply by the unit b^(n*e):
a*c^(n*d)=η_coeff. Tensor multiplication identifies c^(n*d)*z^(n*e*d)
with the displayed tensor of t^n and t^k through tensorPowAddIso.
Thus the cleared identity holds locally. Naturality of tensor sections and
of tensorPowAddIso lets these equalities glue on the ambient image W.
This argument does not cancel c or assume t generates on W. For n=0 the
identity has no denominators or extra factors, and for d=1 one has k=0.
Empty intersections have unique sections, so the same conclusion holds there. -/
theorem sectionRing_chart_cross_multiplication
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
      let W := U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val)
      let k := n * (d - 1)
      (show Γ(X, W) from
        g.app (Proj.basicOpen (sectionRingGrade L) t.val)
          (Proj.awayToSection (sectionRingGrade L) t.val
            (HomogeneousLocalization.Away.mk (sectionRingGrade L) t.property n
              ξ.val ξ.property))) •
        (L.tensorPowAddIso (n • e) (k • e)).inv.app W
          (tmulSection
            ((L.tensorPow (n • e)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
              ((t.val ^ n) (n • e)))
            ((L.tensorPow (k • e)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
              ((t.val ^ k) (k • e)))) =
        (L.tensorPow (n • e + k • e)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
          ((ξ.val * t.val ^ k) (n • e + k • e)) := by sorry

end AlgebraicGeometry.Scheme.Modules
