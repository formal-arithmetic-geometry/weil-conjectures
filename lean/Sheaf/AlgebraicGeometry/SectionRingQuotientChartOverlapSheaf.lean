/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.AlgebraicGeometry.InvertibleSectionRing
public import Sheaf.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Sheaf components of section-ring quotient charts

Source: Stacks Project, Constructions, Tags 01N8 and 01NK, uniqueness arguments.
(blueprint: lem-sc-section-ring-quotient-chart-overlap-sheaf-map).
-/

@[expose] public section

universe v
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- After identifying the underlying maps, their pullbacks agree on every target open.
The equality includes the restriction transport induced by that identification.
Source: Stacks Project, Constructions, Tags 01N8 and 01NK, uniqueness arguments.
(blueprint: lem-sc-section-ring-quotient-chart-overlap-sheaf-map).

Proof: Write F and H for the two restrictions to U intersect V. Fix a point of
this overlap and a positive-degree homogeneous a of degree r whose chart contains
its common image under F and H. The fraction equations imply that a is
nonvanishing near the point: apply the equation with denominator a, exponent d
and numerator s^r (or exponent e and numerator t^r), and pass to the residue
field. A nonzero numerator forces the denominator power, and hence a, to be
nonvanishing. The locus is open, and a trivializes L^{tensor(r)} on it.
Restrict hg and hh to the intersection of the two inverse-image a-charts with
the overlap. Tensor powers of this free generator are free generators, so the
equations with denominator a imply equality of the scalar pullbacks of every
homogeneous fraction xi/a^n: both multiplied by a^n equal the restriction of xi.
For n = 0 the generator is the tensor unit and the same cancellation applies.
Every element of the degree-zero homogeneous localization S_(a) has such a
representative. Thus the induced ring maps from S_(a) to sections on this source
open agree. The affine morphism correspondence for D_+(a) identifies the two
restricted maps, including their sheaf components. These source opens cover the
overlap, so equality of pullbacks of any section on any target open follows by
sheaf locality on its inverse image. The equality of underlying maps identifies
these inverse images; in Lean the displayed eqToHom restriction is that transport.
Empty inverse images have unique sections. Nilpotents are retained: cancellation
uses a free generator, not reducedness or cancellation in the section ring. -/
theorem sectionRing_overlap_sheaf_map
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d e : ℕ) (s : sectionRingGrade L d) (t : sectionRingGrade L e)
    (hd : 0 < d) (he : 0 < e) (U V : X.Opens)
    (hU : (U : Set X) = nonvanishingLocus (L.tensorPow d) (s.val d))
    (hV : (V : Set X) = nonvanishingLocus (L.tensorPow e) (t.val e))
    (g : U.toScheme ⟶ Proj (sectionRingGrade L))
    (h : V.toScheme ⟶ Proj (sectionRingGrade L))
    (hg : ∀ (e : ℕ) (_he : 0 < e) (t : sectionRingGrade L e)
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
              ⊤)).op (ξ.val (n • e)))
    (hh : ∀ (e : ℕ) (_he : 0 < e) (t : sectionRingGrade L e)
          (n : ℕ) (ξ : sectionRingGrade L (n • e)),
          (show Γ(X, V.ι ''ᵁ (h ⁻¹ᵁ
              Proj.basicOpen (sectionRingGrade L) t.val)) from
            h.app (Proj.basicOpen (sectionRingGrade L) t.val)
            (Proj.awayToSection (sectionRingGrade L) t.val
              (HomogeneousLocalization.Away.mk (sectionRingGrade L) t.property n
                ξ.val ξ.property))) •
            (L.tensorPow (n • e)).presheaf.map (homOfLE
              (le_top : V.ι ''ᵁ (h ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
                ⊤)).op ((t.val ^ n) (n • e)) =
          (L.tensorPow (n • e)).presheaf.map (homOfLE
            (le_top : V.ι ''ᵁ (h ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
              ⊤)).op (ξ.val (n • e)))
    (hbase : (X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ g).base =
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ h).base) :
    ∀ W, (X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ g).app W ≫
      (U ⊓ V).toScheme.presheaf.map
        (eqToHom congr((TopologicalSpace.Opens.map $hbase.symm).obj W)).op =
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ h).app W := by sorry

end AlgebraicGeometry.Scheme.Modules
