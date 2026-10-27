/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.UnramifiedMorphism

/-!+# An open unit forces etale groupoid projections

Source: Stacks Project, `more-groupoids.tex`, Tag 04R9, `lemma-sheaf-differentials`;
`morphisms.tex`, Tags 02G5 and 02GV; `stacks-morphisms.tex`, Tag 06N0, final paragraph
(blueprint: lem-sfb-groupoid-open-unit-etale).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- In a groupoid scheme over any base, flat locally finitely presented source and target
maps are etale if the unit is an open immersion. The maps in `Over S` retain the base
structure; composition is a scheme map on the underlying pullback. Its compatibility
with the base follows from the composition-source law and the compatibility of `s`.

Source: Stacks Project, Tag 04R9 (`lemma-sheaf-differentials`), together with Tags 02G5
and 02GV, as applied in the final paragraph of Tag 06N0 (`lemma-DM-residual-gerbe`)
(blueprint: lem-sfb-groupoid-open-unit-etale).

Proof (the five steps of the DAG node):
1. Put P = R x_[s,U,t] R and Q = R x_[t,U,t] R. Inversion in the first factor gives
   an isomorphism P -> Q, (a,b) -> (i(a),b), with inverse the same formula.
   Use def-a1-groupoid-scheme and def-pc-fibre-product.
2. The map j : R -> P, a -> (i(a),a), is the pullback of the unit along composition,
   with left side s. On arbitrary test schemes, if c(a,b) = e(u), the source and target
   laws give s(b) = t(a) = u. Associativity, inverse and unit laws then give b = i(a),
   hence a = i(b); the unique lift is b since the second projection of j is identity.
3. By lem-weil-pbc-open-immersion-base-change, j is an open immersion. The isomorphism
   of step 1 carries it to the diagonal of t. Fibre-product uniqueness and invariance
   under isomorphisms (def-pc-fibre-product, def-weil-open-immersion) make that diagonal
   an open immersion.
4. Applying inversion in both factors gives an isomorphism from R x_[s,U,s] R to Q,
   intertwining the diagonal of s with the diagonal of t composed with i. Thus the
   diagonal of s is also an open immersion, by def-a1-groupoid-scheme.
5. The projections are locally of finite type: apply lem-a1-map-over-base-finite-presentation
   over U with target id_U, which is locally of finite type. The open diagonals give
   unramifiedness (def-weil-unramified-morphism). Together with the assumed flatness
   and local finite presentation, this gives etaleness (def-weil-etale-morphism).
No Noetherian, reducedness, field, separatedness or nonemptiness assumption is used. -/
theorem IsGroupoidScheme.etale_of_isOpenImmersion_unit
    {S : Scheme.{u}} {U R : Over S} (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s.left t.left ⟶ R.left)
    (_hG : IsGroupoidScheme s.left t.left e.left i.left c)
    [Flat s.left] [Flat t.left]
    [LocallyOfFinitePresentation s.left] [LocallyOfFinitePresentation t.left]
    [IsOpenImmersion e.left] : Etale s.left ∧ Etale t.left := by
  sorry

end AlgebraicGeometry
