/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.InvertibleSectionRing
public import Sheaf.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Forward implication for the section-ring chart formula

Source: Stacks Project, Constructions, Tag 01N8; Properties, Tag 01PZ
(blueprint: lem-sc-ample-proj-canonical-map-preimage-forward).
-/

@[expose] public section

universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- If a point lies in the inverse image of a homogeneous basic open, the section is
nonvanishing there. The proof uses the fraction identity with a section already known
to be nonvanishing at the point; in the residue-field fibre, a nonzero numerator cannot
be a multiple of a vanishing denominator.
Source: Stacks Project, Constructions, Tag 01N8; Properties, Tag 01PZ
(blueprint: lem-sc-ample-proj-canonical-map-preimage-forward).

Proof: choose e > 0 and t nonvanishing at x from hx. Trivialize L near x and
pass to its one-dimensional residue-field fibre. Multiplication in the section ring is
tensor multiplication transported through tensorPowAddIso, so the value of a positive
power is the corresponding scalar power times a tensor-power basis. In particular,
t^d has nonzero value, and s^e has zero value if s has zero value. On the inverse image
of D_+(s), specialize hformula to n = e and numerator t^d; use e*d = d*e to
regard the numerator as having degree e*d. Restriction and taking germs respect scalar
multiplication. The resulting fibre identity is alpha times the value of s^e equals
the nonzero value of t^d. Hence s^e is nonzero, and therefore s is nonzero.
This is the asserted nonvanishingLocus membership, since reduction modulo the maximal
ideal identifies that predicate with nonzero fibre value. No reducedness assumption
on X is used: the calculation takes place over its residue field. -/
theorem sectionRing_proj_mem_basicOpen_forward (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
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
    x ∈ f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val →
      x ∈ nonvanishingLocus (L.tensorPow d) (s.val d) := by sorry

end AlgebraicGeometry.Scheme.Modules
