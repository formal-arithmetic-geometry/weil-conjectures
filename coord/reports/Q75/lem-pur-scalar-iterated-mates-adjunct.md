## Worker report

The module `Sheaf.Paper.ScalarIteratedMatesAdjunct` defines the displayed
composite-adjunction adjunct for an arbitrary arrow h and states its normal form
on the two specified scalar mates. The theorem's whole proof is `sorry`; the
helper definition contains actual morphisms, with no postponed data or proofs.
The item's statement and dependency lists are unchanged. No new nodes or
dependency repairs are required.

Source read: Stacks Project, sites-cohomology.tex, Tag 0E46,
`remark-compose-base-change`, including the two successive square mates and the
outer rectangle. The node supplies the explicit omitted adjunct calculation.
Also read the current blueprint main-20261015 proof of
`cor-pur-vector-bundle-purity`, paragraph 2, where coefficient reduction and
composition of adjunctions are performed before transposing.

Hypotheses and clauses, matched to Lean:

- The finite commutative rings A and B are `{A B : Type (u + 1)}` with
  `[CommRing A] [CommRing B] [Finite A] [Finite B]` on the theorem.
  `(φ : A →+* B)` is the unital coefficient map, including noninjective and
  nonflat maps. The definition of the adjunct also works without finiteness.
- The schemes and arbitrary composable morphisms are
  `{X Y Z : Scheme.{u}} (r : X ⟶ Y) (s : Y ⟶ Z)`. There are no geometric
  property assumptions on either arrow.
- The ordinary unbounded category D_A(X) is `DerivedCategoryModule A X`,
  and `(M : DerivedCategoryModule A X)` is unrestricted.
- `Q_T` is the existing `scalarExtension φ T`, the canonical ordinary derived
  scalar extension. No completed category or chosen arbitrary comparison is used.
- `R_{u,R}` is `R(lowerStar (ModuleCat.{u + 1} R) u)`. The exact inverse image
  `P_{u,R}` is represented by `L(upperStar (ModuleCat.{u + 1} R) u)` using the
  canonical `leftDerivedUpperStarIsoMapDerivedCategory`. This is the same
  representation used by the dependency records for scalarPullbackIso and
  scalarMate; it is canonically the termwise functor induced by exact inverse
  image, and does not change the mathematical functor in the statement.
- Every epsilon is the component of
  `(derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) u).counit`.
  Thus these are the given canonical counits, rather than additional data.
- Lambda is exactly `(scalarPullbackIso φ u).hom.app K`. Its existing definition
  fixes its K-flat representative normalization. Chi is exactly
  `(scalarMate φ u).app K`, whose existing definition is the counit-defined mate
  of that normalized isomorphism.
- U is expanded everywhere as `R(lowerStar (ModuleCat.{u + 1} A) r).obj M`;
  V is the s-direct image of that expression. There are no let-bound substitutes.
- The helper `scalarIteratedAdjunct φ r s M h` accepts every h with precisely
  the displayed source Q_Z V and target R_s,B R_r,B Q_X M. Its result has source
  P_r,B P_s,B Q_Z V and target Q_X M. Its body is, in Lean's diagrammatic order,
  P_r,B(P_s,B(h)), P_r,B(epsilon_s,B at R_r,B Q_X M), epsilon_r,B at Q_X M.
  This is exactly the displayed definition of Adj_B(h). By
  `CategoryTheory.Adjunction.comp_counit_app` it is the inverse Hom equivalence
  of the composite adjunction, with s as the first left adjoint and r as the second.
- The helper's argument in `scalarMate_iterated_adjunct` is the s-mate at U
  followed by `R(lowerStar (ModuleCat.{u + 1} B) s).map` of the r-mate at M.
  This is G_M in diagrammatic composition order.
- The right side consists of four arrows: P_r,B(lambda_s,V),
  lambda_r,P_s,A(V), Q_X(P_r,A(epsilon_s,A,U)), Q_X(epsilon_r,A,M).
  These are precisely the four factors of T_M in diagrammatic order.
- The conclusion is equality of these morphisms in D_B(X). No boundedness,
  properness, coefficient flatness or invertibility of either mate is assumed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom
  (reexported by the geometric dependencies).
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`, reexporting
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`.
- The current recorded change-of-rings module is
  `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`, publicly reexporting
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem.
  The small-etale specialization used in the actual formula is the existing
  `AlgebraicGeometry.Etale.scalarExtension` abbreviation from
  `Sheaf.Paper.EtaleDerivedScalarTensor`, reexported by the scalar-mate module.
  Both existing interfaces were read; no new extension construction is introduced.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`, with its exactness and
  compatibility with the abelian adjunction. The termwise derived inverse image
  is identified with its left-derived presentation by the existing
  `AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`, reexporting
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`:
  `AlgebraicGeometry.Etale.derivedUpperStarLowerStarAdjunction` and its counit.
  The recorded projection map is not needed as an extra hypothesis.
- `Sheaf.Paper.PurEtaleScalarMateProjection`:
  `AlgebraicGeometry.Etale.scalarPullbackIso` and
  `AlgebraicGeometry.Etale.scalarMate`. Their full signatures, docstrings and
  definitions were read.
- `Mathlib.CategoryTheory.Adjunction.Basic`:
  `CategoryTheory.Adjunction.comp`, `comp_counit_app` and
  `eq_unit_comp_map_iff`. The last is the Mathlib match of the proof dependency
  `lem-weil-pbc-adjunct-counit-identity`. The theorem docstring gives all four
  proof steps from the node, including both naturality substitutions.

Edge cases checked before writing: zero object M (all displayed arrows remain
defined and the equality is between the prescribed zero-object arrows); identity
r or s (no strict replacement of their chosen derived adjunction by identity is
assumed); empty schemes (no nonemptiness hypotheses); zero coefficient ring
where a unital map exists (no Nontrivial instances); nonflat finite quotient maps
(no exactness assumption on scalar extension); unbounded M (no Plus/Bounded
subcategory). All object and ring universes are explicit, with the existing
coefficient-universe u+1 and scheme-universe u convention. Every factor in the
normal form has the specified source and target.

Searches for an existing statement (2026-10-22):

- `msearch.py leanfinder`, query “Adjunct of two successive derived scalar change
  mates equals scalar extension of two counits after the normalized pullback
  comparisons”: 8 hits, including PullbackShift.adjunction and exponentiable
  pushforward/pullback counit formulas; none states this etale scalar formula.
- `msearch.py loogle`, query
  `CategoryTheory.mateEquiv_counit, CategoryTheory.Adjunction.comp_counit_app`:
  0 hits for the combined query.
- `msearch.py grep`, query
  `mateEquiv_hcomp|comp_counit_app|mateEquiv_counit` in CategoryTheory/Adjunction:
  6 hits in Basic.lean and Mates.lean. Read their signatures; these give the
  generic composite counit and single-mate identities, not the specified normal form.
- `msearch.py leansearch`, query “The transpose of a composition of two scalar
  change mates under the composite adjunction equals pullback comparisons
  followed by scalar extension of both counits”: 8 hits, including Adjunction.comp
  and ModuleCat.homEquiv_extendScalarsComp, no exact statement.
- `rg` of `scalarMate|scalarPullbackIso|iterated.*[Mm]ate` in `lean/Sheaf` and
  `lean/WeilConjectures`, and of the item id in `lean/WeilConjectures`: existing
  scalar definitions and generic mate results; no occurrence of this item id.
- Follow-up `rg` for scalar composition names found
  `EtaleDirectImageScalarComposition.scalarMate_directImage_composition` and a
  private generic `scalarMate_comp` in PbcScalarExtension. Both were read:
  the former states compatibility with compositors, and the latter is a generic
  pasted-square result with extra comparison data, not this adjunct equality.
- `rg` for `scalarIteratedAdjunct|scalarMate_iterated_adjunct` in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` found no
  existing declaration of either proposed name.

Validation: `scompile.py Q75 lem-pur-scalar-iterated-mates-adjunct` compiled the
delivered file cleanly in sandbox mode (5.1 s) and library mode (5.3 s), each within
the standard 60-second per-file limit. There are no diagnostic commands in the
delivery and no lines over 100 characters. No statement dispute or node fault found.

## Second reading by Q75

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
