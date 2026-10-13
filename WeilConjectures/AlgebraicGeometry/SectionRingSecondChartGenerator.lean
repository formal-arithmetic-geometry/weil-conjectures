/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Free generation on a second section-ring chart

Source: Stacks Project, Constructions, Tags 01N8 and 01NK.
(blueprint: lem-sc-section-ring-second-chart-generator).
-/

@[expose] public section

universe v
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The second section freely generates its tensor power on its chart preimage.
Source: Stacks Project, Constructions, Tag 01N8, comparison of chart preimages;
Tag 01NK, comparison of different positive degrees.
(blueprint: lem-sc-section-ring-second-chart-generator).

Proof: On a local trivialization z of L in U, write s=b z^d and t=c z^e.
The hypothesis on s says b is invertible. Apply hρ with exponent e and
numerator t^d (transporting d*e=e*d) to identify ρ(t^d/s^e) with c^d/b^e.
The inverse image of D_+(t) in the s-chart is the principal open of t^d/s^e;
use the affine basic-open preimage formula and hq to identify its inverse
image in U with the unit locus of c^d/b^e. This is the unit locus of c,
since b is invertible and d>0. Thus t is a unit multiple of z^e there.
Its multiplication map is an isomorphism on each such local trivialization.
These isomorphisms agree, because each is multiplication by the same section t,
and glue to a trivialization on the ambient image W. This also proves the
bijectivity on every subopen required by IsFreeGenerator. Empty W causes no
exception: all its modules of sections have one element. No reducedness is used. -/
theorem sectionRing_second_chart_generator
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
    ∀ (e : ℕ) (_he : 0 < e) (t : sectionRingGrade L e),
      IsFreeGenerator ((L.tensorPow e).presheaf.map (homOfLE
        (le_top : U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤ ⊤)).op
        (t.val e)) := by sorry

end AlgebraicGeometry.Scheme.Modules
