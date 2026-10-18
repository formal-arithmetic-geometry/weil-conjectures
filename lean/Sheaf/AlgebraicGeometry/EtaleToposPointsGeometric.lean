/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.CategoryTheory.Sites.GeometricMorphism

import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.CategoryTheory.CofilteredSystem
import Sheaf.AlgebraicGeometry.GeometricStalkToposPoint

/-!
# Every point of the small etale topos is geometric

Source: Stacks Project, Etale Cohomology, Tag 04HU, parts (1) and (2), and Tag 04FM
(blueprint: lem-trf-etale-topos-points-geometric).

The conclusion uses the equivalent inverse-image formulation: a natural isomorphism
with the geometric stalk functor. Its defining colimit is over the opposite of the
category of elements of the geometric lift functor, hence over pointed etale neighbourhoods.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Every geometric morphism from sets to the small etale topos of a scheme has
inverse image naturally isomorphic to the stalk at an algebraically closed geometric point.
Here `sheafFiber` is the colimit of sections over opposite pointed etale neighbourhoods.
The site has objects in `Type (u + 1)` and morphisms in `Type u`; sets and stalks are
taken in `Type (u + 1)`. The field can already be chosen in `Type u`, by taking an
algebraic closure of a residue field.
Source: Stacks Project, Tags 04HU and 04FM
(blueprint: lem-trf-etale-topos-points-geometric).

Proof:
1. Set `L(U) = p.inverse(h_U^#)`. By lem-trf-site-point-reconstruction-sets,
   this preserves finite limits, sends covers to jointly surjective families, and
   reconstructs `p.inverse` by a neighbourhood colimit. The terminal value is a
   singleton; the empty-cover value is empty. Monomorphisms give injections and
   disjoint unions give disjoint unions, using pullbacks and the summand cover.
2. The union W of opens with empty L-value has empty value. Its complement is
   nonempty and irreducible, by preservation of intersections and maximality of W.
   By lem-weil-pbc-scheme-sober it has a unique generic point s. An open has nonempty
   value exactly when it contains s. An etale object's image is open by
   lem-weil-pbc-flat-lfp-open and covers that image, so its value is nonempty exactly
   when its image contains s (def-weil-etale-morphism and
   lem-weil-pbc-etale-composition-cancellation).
3. Choose an affine open A containing s. Restrict to its etale site using
   lem-weil-pbc-etale-composition-cancellation. Choose an algebraic closure Omega
   of the residue field by lem-pc-algebraic-closure-exists-unique; the residue-field
   map defines the geometric point of def-weil-geometric-point over s.
4. For an affine etale A-scheme U, lem-trf-affine-etale-split-neighbourhood supplies
   a pointed V with U times V a finite disjoint union of copies of V and a remainder
   having no point over s. The remainder's value is empty. Taking a fibre over an
   element of L(V) shows L(U) is finite of the geometric fibre's cardinality,
   including cardinality zero. For pointed U the value is also nonempty.
5. Use lem-weil-pbc-affine-etale-essentially-small-cover to choose a small skeleton
   of affine pointed neighbourhoods over A. It is cofiltered by
   lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered and affine refinement.
   Apply lem-trf-cofiltered-finite-sets-section to its finite nonempty L-values,
   obtaining compatible elements without requiring surjective transition maps.
6. Extend those elements to all pointed neighbourhoods by affine refinement over A.
   Common refinements and equalizers show independence and compatibility with every
   pointed arrow. Thus geometric lifts into each T map naturally to L(T).
7. For affine U over A, use the split neighbourhood of step 4. Its copy sections
   enumerate the geometric lifts. Compatibility identifies their chosen elements
   with the distinct points of the fibre of L(U) times L(V) over the chosen element
   of L(V). Thus the natural map from geometric lifts to L(U) is bijective.
8. For arbitrary T replace T by T times A, which changes neither lifts nor L-value.
   An affine open cover and joint surjectivity give surjectivity. For injectivity,
   two lifts with equal images lie in affine opens; their L-elements pair in the
   overlap fibre product. Refine this by an affine cover and lift the paired element.
   Step 7 and naturality identify both original lifts with the same composite.
9. The resulting natural bijections identify pointed geometric neighbourhoods with
   the reconstruction category. Reindex its colimit formula to obtain the asserted
   natural isomorphism. By lem-fix-geometric-stalk-topos-point this stalk is the
   inverse image of the actual geometric point. Adjunction mates identify the right
   adjoints too, as in def-trf-geometric-morphism. All colimits use the stated size
   convention def-weil-size-convention. -/
theorem etaleToposPoint_isGeometric (S : Scheme.{u})
    (p : GeometricMorphism (Type (u + 1))
      (Sheaf S.smallEtaleTopology (Type (u + 1)))) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (s : Spec (.of Ω) ⟶ S),
      Nonempty (p.inverse ≅ (pointSmallEtale s).sheafFiber (A := Type (u + 1))) := by
  sorry

end AlgebraicGeometry.Scheme
