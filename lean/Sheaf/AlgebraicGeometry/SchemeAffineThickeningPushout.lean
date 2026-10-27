module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.ThickeningAffineScheme
import Sheaf.AlgebraicGeometry.AffineClosedPinchingPushout
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Scheme pushouts along arbitrary thickenings and affine morphisms

Source: Stacks Project, More on Morphisms, Tag 07RT, `lemma-pushout-along-thickening`
(blueprint: lem-sfb-scheme-affine-thickening-pushout).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An arbitrary scheme thickening and an affine morphism admit a scheme pushout.
The map from `S` is again a thickening, and the same square is cartesian.
`IsPushout` includes commutativity and unique factorization against every scheme target;
`IsPullback` identifies `T` with `pullback j b` compatibly with `a` and `i`.
No finite-order, Noetherian, separatedness, or nonemptiness assumption is imposed.

Source: Stacks Project, More on Morphisms, Tag 07RT, `lemma-pushout-along-thickening`
(blueprint: lem-sfb-scheme-affine-thickening-pushout).

Proof plan from the node:
1. Identify the point spaces of `T` and `T'` using the thickening. On the space of `S`,
   form the sheaf of matching pairs of sections of O_S and the direct image of O_T',
   whose images agree in the direct image of O_T. Restrictions and ring operations are
   coordinatewise, so componentwise sheaf gluing proves this is a sheaf of rings.
2. For affine U in S, its inverse image V in T is affine since a is affine; the
   corresponding open V' in T' is affine by lem-weil-pbc-thickening-affine-scheme.
   Write U = Spec B, V = Spec A, V' = Spec A'. The map alpha : A' -> A is surjective
   by def-weil-closed-immersion. Put C = A' times_A B. Its projection q to B is
   surjective by lifting along alpha. The topological pushout in
   lem-sfb-ring-fibre-product-spectrum identifies Spec C with the space of U,
   because V -> V' is a homeomorphism.
3. For c = (h',g) in C, with common image h in A, principal inverse images are
   D(g), D(h'), D(h). The principal-localization open immersions identify their
   sections with B_g, A'_(h'), A_h. The localization clause of
   lem-sfb-ring-fibre-product-spectrum gives C_c = A'_(h') times_(A_h) B_g,
   compatibly with both projections and all further principal localizations.
4. By lem-weil-pbc-spec-localization-away-basic-open these opens form a basis.
   On overlaps D(c) intersect D(d) = D(cd), the comparisons agree by localization
   compatibility. Glue the comparisons and their inverses to identify the ringed
   space over U with Spec C. All stalks are local and the affine charts cover by
   lem-weil-pbc-affine-opens-basis, so this explicitly constructed ringed space is a scheme P.
5. The two sheaf projections induce j and b. In these charts they are Spec q and
   Spec p, so are morphisms of schemes. The matching condition gives a >> j = i >> b.
   The map j is a homeomorphism and, since q is surjective, a closed immersion;
   hence it is a thickening. Surjectivity is needed on stalks, not all open sections.
6. For compatible maps S -> Z and T' -> Z, with Z any scheme, apply
   lem-sfb-affine-closed-pinching-pushout on each affine chart of P. Uniqueness makes
   the local extensions agree on smaller affine opens, hence on overlaps by the
   affine-open basis. Apply lem-weil-pbc-scheme-morphism-gluing to obtain the unique
   global extension. This proves the scheme pushout property, including nonaffine Z.
7. On a chart let K = ker alpha and J = ker q = {(k,0) : k in K}. The map
   A' tensor_C B -> A sends x tensor b to alpha(x) beta(b). Its inverse sends a to
   x tensor 1 for a lift x of a. It is independent of the lift because
   k tensor 1 = 1 tensor q(k,0) = 0. Additivity and multiplicativity follow by
   choosing sums and products of lifts. To verify the other inverse equation,
   lift b to (y,b) in C and use x tensor b = xy tensor 1.
8. By lem-weil-pbc-fibre-product-affine-spectra the canonical comparison
   T -> S times_P T' is therefore an isomorphism on each affine chart, with the
   correct projections. These local inverses agree on overlaps by uniqueness;
   scheme-morphism gluing gives the global inverse, proving the cartesian square.
   If S is empty then T and T' are empty as well. The construction and argument
   allow zero coordinate rings and locally nilpotent ideals with no global exponent.
-/
theorem exists_scheme_affine_thickening_pushout
    {T T' S : Scheme.{u}} (i : T ⟶ T') (a : T ⟶ S)
    (hi : IsThickening i) [IsAffineHom a] :
    ∃ (P : Scheme.{u}) (j : S ⟶ P) (b : T' ⟶ P),
      IsPushout a i j b ∧ IsThickening j ∧ IsPullback a i j b := by
  sorry

end AlgebraicGeometry
