/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.InvertibleSectionRing
public import Sheaf.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-! # Reverse implication for the section-ring chart formula

Source: Stacks Project, Constructions, Tag 01N8; Properties, Tag 01PZ
(blueprint: lem-sc-ample-proj-canonical-map-preimage-reverse).
-/

@[expose] public section

universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- If a homogeneous section is nonvanishing at a point, the point lies in the inverse
image of its basic open. Choose a positive-degree denominator chart through the point;
the fraction identity makes the corresponding quotient a unit in the local ring.
Source: Stacks Project, Constructions, Tag 01N8; Properties, Tag 01PZ
(blueprint: lem-sc-ample-proj-canonical-map-preimage-reverse).

Proof: write y = f(x). The homogeneous prime y does not contain the irrelevant
ideal, so choose a positive-degree homogeneous t, of degree e, outside that prime.
Thus y lies in D_+(t). Trivialize L near x and pass to the residue-field fibre.
The value of s^e is nonzero, since s is nonvanishing and e > 0. Specialize hformula
on the t-chart to n = d and numerator s^e, using e*d = d*e to match degrees.
It gives alpha times the value of t^d equals the nonzero value of s^e. Hence alpha
and the value of t^d are both nonzero. Here alpha is the residue of the pullback of
the chart function s^e/t^d. Thus its pullback germ is a unit in O_X,x. The stalk
homomorphism O_Proj,y to O_X,x is local and reflects units, so the original germ of
s^e/t^d is a unit. The Proj stalk identification with homogeneous localization and
the unit criterion in localization at a prime imply that s^e is outside the prime y.
Primality, or just closure of an ideal under multiplication, implies that s is outside
y as well. This is y in D_+(s). The hypothesis hx is harmless and is not needed for
this direction. All positive-power tests occur over residue fields, including for
nonreduced X. -/
theorem sectionRing_proj_mem_basicOpen_reverse (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (f : X ⟶ Proj (sectionRingGrade L))
    (hformula : ∀ (d : ℕ) (_hd : 0 < d) (s : sectionRingGrade L d),
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
            (ξ.val (n • d)))
    (x : X)
    (hx : ∃ (e : ℕ) (t : sectionRingGrade L e),
      0 < e ∧ x ∈ nonvanishingLocus (L.tensorPow e) (t.val e))
    (d : ℕ) (hd : 0 < d) (s : sectionRingGrade L d) :
    x ∈ nonvanishingLocus (L.tensorPow d) (s.val d) →
      x ∈ f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val := by sorry

end AlgebraicGeometry.Scheme.Modules
