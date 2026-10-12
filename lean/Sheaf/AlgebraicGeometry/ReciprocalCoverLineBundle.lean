/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Sheaf.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.GlueComponentTransitionCocycle
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-! # A line bundle and two sections from reciprocal local functions

Source: Stacks Project, Varieties Lemma 09NB, cocycle and two-section construction.
(blueprint: lem-sc-reciprocal-cover-line-bundle)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Reciprocal local functions glue two trivial line bundles and two global sections.
This construction requires neither dimension nor separatedness nor an affine open.

Source: Stacks Project, Varieties Lemma 09NB (varieties-lemma-find-globally-generated),
proof, cocycle construction and the two displayed sections.
(blueprint: lem-sc-reciprocal-cover-line-bundle).

Proof: On U intersect V, the restrictions of f and g multiply to 1. Use the unit g
as the transition from the frame e_U to e_V, so e_U = g e_V. Use its inverse for
the reversed overlap and identity transitions on equal indices. The two-open Cech
identities follow by cancellation of inverse units. Glue using the Cech transition
lemma, obtaining an invertible L with these local frames. The pairs (e_U, g e_V)
and (f e_U, e_V) agree on the overlap, hence glue by the sheaf axiom to s and t.
Restriction of global sections to all opens turns these into elements of L.sections.
The section s is a free generator on U. On V its nonvanishing locus is D(g),
because a coefficient times a local frame has nonzero residue exactly when that
coefficient is a unit in the local ring. Since D(g) = U intersect V, the cover gives
X_s = U. Likewise t is a free generator on V, so V is contained in X_t.
For an empty chart the unique sections glue and the same argument applies.
-/
theorem exists_line_bundle_sections_of_reciprocal_cover
    (X : Scheme.{u}) (U V : X.Opens) (f : Γ(X, U)) (g : Γ(X, V))
    (hcover : U ⊔ V = ⊤)
    (hinv : X.presheaf.map (homOfLE inf_le_left).op f *
      X.presheaf.map (homOfLE inf_le_right).op g = 1)
    (hlocus : X.basicOpen g = U ⊓ V) :
    ∃ (L : X.Modules) (s t : L.sections), L.IsInvertible ∧
      nonvanishingLocus L (s.val (Opposite.op ⊤)) = (U : Set X) ∧
      (V : Set X) ⊆ nonvanishingLocus L (t.val (Opposite.op ⊤)) := by sorry

end AlgebraicGeometry.Scheme.Modules
