/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FpqcSingletonAffineRefinement
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.RingTheory.FaithfullyFlat.Amitsur

/-! # Additive group torsors over an affine scheme have a section

Source: Milne, Algebraic Groups (2017), Definition 2.66 and Examples 2.67 and 2.72,
printed pp.60--61 (blueprint: lem-sfb-additive-affine-torsor-section).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every represented right additive-group torsor over Spec A has a section, for
an arbitrary commutative k-algebra A. No reducedness, Noetherian, finite type, or
perfectness condition is assumed.

Source: Milne, Algebraic Groups (2017), Example 2.72, printed p.61
(blueprint: lem-sfb-additive-affine-torsor-section).

Proof:
1. Flatness, surjectivity and local finite presentation make the projection an
fppf singleton cover (`def-pc-fppf-site`). It is fpqc by
`lem-trf-fppf-covering-is-fpqc`. Apply
`lem-galois-fpqc-singleton-affine-refinement` to get an affine fpqc cover
U = Spec B of S = Spec A and an S-map h : U -> P. By
`lem-weil-pbc-flat-morphism-affine-criterion` and
`lem-weil-pbc-flat-surjective-spectrum-faithfully-flat`, A -> B is faithfully flat.
If A is the zero ring, S is empty and its unique map to P is already a section.
2. On U x_S U the inverse torsor isomorphism gives the unique difference c with
h_2 = h_1 + c. By `lem-weil-pbc-fibre-product-affine-spectra`, this is an element
of B tensor_A B. Polynomial evaluation identifies maps into the specified G_a
with ring elements, compatibly with its addition (`def-sc-gm-ga`). On the triple
product the action law and uniqueness give c_23 - c_13 + c_12 = 0. This is an
identity of scheme morphisms, including for nonreduced A.
3. Apply `lem-pc-cech-exact` to A -> B and M = A. Exactness in degree one gives
b in B with c = 1 tensor b - b tensor 1. Translate h by -b using the given right
action. For t = h - b, the two restrictions satisfy
 t_2 = h_2 - b_2 = h_1 + c - b_2 = h_1 - b_1 = t_1.
4. Apply `lem-weil-pbc-fpqc-representable-descent` to descend t to e : S -> P.
The action preserves the projection, so f t = q. After composition with the
fpqc cover q, both f e and the identity of S are q. Uniqueness in the same
representable descent statement, now with target S, gives f e = id_S. Since
all maps are over Spec k, this is exactly the displayed section equation. -/
theorem additive_affine_torsor_section {k : Type u} [Field k]
    (A : Type u) [CommRing A] [Algebra k A]
    (P : RepresentedRightTorsor (Grp.mk (StandardGroupSchemes.additive k))
      (StandardGroupSchemes.affine k A)) :
    ∃ e : StandardGroupSchemes.affine k A ⟶ P.space,
      e ≫ P.projection = 𝟙 (StandardGroupSchemes.affine k A) := by
  sorry

end AlgebraicGeometry
