/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Degree
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
import WeilConjectures.AlgebraicGeometry.DensePoints
import WeilConjectures.AlgebraicGeometry.Descent
import WeilConjectures.AlgebraicGeometry.Picard.Defs
import WeilConjectures.AlgebraicGeometry.Picard.RationalPoint

/-! # Fpqc descent for degree parts of the Picard functor

Source: Stacks Project, Tags 0D28, 0D2B and 023T.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- The fppf sheafification of the fibrewise degree-`d` Picard presheaf of a smooth proper
 geometrically integral curve is an fpqc sheaf.

Proof: geometric integrality makes the curve nonempty. Density of closed points with finite
 separable residue field on a smooth scheme supplies such a point; base change to its
 residue field supplies a rational point. This extension is an fppf covering. Over it the relative
 Picard sheaf identifies with the normalized Picard functor, since the structure sheaf has
 universally trivial direct image. The degree part identifies with the normalized classes
 having fibrewise degree `d`: twisting by a class from the base has degree zero, and fppf-local
 representatives give exactly this condition.

For a normalized class choose a trivialization along the section. Normalize each overlap
 isomorphism to preserve this trivialization. Such an isomorphism is unique because every
 global unit on the curve over any test scheme comes from that scheme. Uniqueness implies
 the cocycle equation. Fpqc descent of invertible modules and their morphisms therefore glues
 normalized classes uniquely. Fibrewise degree descends too: a covering is jointly surjective,
 and degree is unchanged by extension of residue fields. Thus the normalized degree part is
 an fpqc sheaf.

To descend this assertion from the finite extension, pull a compatible family for an fpqc
 covering back to that extension and glue it there. Its two restrictions on the double
 overlap agree after the original fpqc covering, by separatedness of the normalized degree
 functor there. Hence fppf descent along the finite extension glues the resulting section
 over the original test scheme. Equality with the original family and uniqueness can be
 tested after the same finite fppf cover. This proves the asserted fpqc sheaf condition.

Source: Stacks Project, Lemmas 99.11.4 and 99.11.7 (Tags 0D28 and 0D2B), and fpqc descent
 of invertible modules, Tag 023T; finite separable points, Tag 056U.
 The degree criterion uses residue-field base change.
(blueprint: lem-pd-degree-picard-sheaf-fpqc) -/
theorem isSheaf_fpqc_sheafify_picardDegree
    {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIntegral f]
    (d : ℤ) (S : Subfunctor (picardPresheaf f))
    (hS : ∀ (T : Over (Spec (.of k))) (L : (picardPresheaf f).obj (op T)),
      L ∈ S.obj (op T) ↔ ∀ t, picardPresheafDegree f L t = d) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over (Spec (.of k)))
      ((presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1))).obj
        S.toFunctor).obj := by sorry

end AlgebraicGeometry
