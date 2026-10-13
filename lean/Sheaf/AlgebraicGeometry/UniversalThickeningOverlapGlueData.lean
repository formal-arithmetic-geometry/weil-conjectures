/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Overlap glue data for universal first order thickenings

Source: Stacks Project, More on Morphisms, Tag 04F3, the overlap construction
in the proof of Lemma 37.7.1.
(blueprint: lem-weil-pbc-universal-thickening-overlap-glue-data)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Universal thickenings of open charts admit compatible overlap glue data.
This only constructs local overlaps and transitions, not a glued scheme.

Source: Stacks Project, More on Morphisms, Tag 04F3, proof of Lemma 37.7.1,
paragraphs beginning "Choose an affine open covering" and "By the general remarks".
(blueprint: lem-weil-pbc-universal-thickening-overlap-glue-data)

Proof: The square-zero kernel of each thickening has full support, so the
closed immersion is a homeomorphism. For each ordered pair of charts, take the
unique open in the first thickened chart whose inverse image is the source
intersection. Apply the open-pieces theorem over the whole base to obtain a
universal thickening of this intersection. Identify the sources of the two
restricted thickenings by the pullback symmetry. Universal uniqueness gives
an isomorphism between them, over the base and fixing the source intersection.
Its base compatibility is the first displayed equality, and its compatibility
with the source supplies the morphisms s and both displayed factorizations.
For three charts, restrict to the common intersection. The composites of the
transition maps and the direct transition extend the same source map over X;
universal uniqueness equates them. This gives the maps t prime, their
factorization identity, and the cocycle required by Scheme.GlueData. On repeated
indices uniqueness gives identity transitions and isomorphic diagonal opens.
Use these opens and maps as V, f, t, and t prime of the glue datum, with U equal
to the given thickened charts. The equivalence a and isomorphisms b can therefore
be identities; allowing them permits any equivalent presentation of the data.
The last equivalence is exactly the inverse-image identity defining the overlap
open. If the index type is empty, take empty glue data; every condition is
vacuous. Repeated charts use the same uniqueness argument and need no exclusion. -/
theorem universalFirstOrderThickening_overlapGlueData
    {Z X : Scheme.{u}} (h : Z ⟶ X) (C : Z.OpenCover.{u})
    (Z' : C.I₀ → Scheme.{u}) (i : ∀ k, C.X k ⟶ Z' k)
    (h' : ∀ k, Z' k ⟶ X)
    (H : ∀ k, IsUniversalFirstOrderThickening (C.f k ≫ h) (i k) (h' k)) :
    ∃ (D : Scheme.GlueData.{u}) (a : C.I₀ ≃ D.J)
      (b : ∀ k, Z' k ≅ D.U (a k)),
      (∀ k l, D.f (a k) (a l) ≫ (b k).inv ≫ h' k =
        D.t (a k) (a l) ≫ D.f (a l) (a k) ≫ (b l).inv ≫ h' l) ∧
      (∀ k l, ∃ s : pullback (C.f k) (C.f l) ⟶ D.V (a k, a l),
        s ≫ D.f (a k) (a l) = pullback.fst _ _ ≫ i k ≫ (b k).hom ∧
        s ≫ D.t (a k) (a l) ≫ D.f (a l) (a k) =
          pullback.snd _ _ ≫ i l ≫ (b l).hom) ∧
      ∀ k l (z : C.X l),
        (b l).hom (i l z) ∈ Set.range (D.f (a l) (a k)) ↔
          C.f l z ∈ Set.range (C.f k) := by sorry

end AlgebraicGeometry
