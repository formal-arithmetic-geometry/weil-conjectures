## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteClosedSupportExchange` states
`AlgebraicGeometry.Etale.finite_closedSupport_exchange` and gives three real
helper constructions belonging to the node's canonical comparison. Every theorem
proof in the delivered module is `sorry`; the definitions contain real data.
No mathematical statement correction or dependency-interface repair was needed.

Hypotheses and clauses, checked against the full node and ILO XVII, proof of
Proposition 5.4.1, printed p. 291 (PDF page 297):

- Finite commutative coefficient ring: the module variables are
  `(A : Type (u + 1)) [CommRing A] [Finite A]`. Lean includes these parameters in
  every declaration that uses them. This is the existing ModuleCat encoding,
  with scheme universe `u` and coefficient universe `u+1`.
- Noetherian schemes X' and X: `{X' X Y : Scheme.{u}} [IsNoetherian X']
  [IsNoetherian X]`. Mathlib's IsNoetherian is locally Noetherian plus compact,
  equivalent to the finite affine cover convention specified in the node.
  No separatedness or excellence is added.
- Finite map p and closed immersion i: `(p : X' ⟶ X) [IsFinite p]`
  and `(i : Y ⟶ X) [IsClosedImmersion i]`. The recorded Mathlib definitions
  are used unchanged. No additional conditions on Y are imposed.
- Y' is the chosen fiber product `pullback i p`; p' is `pullback.fst i p`
  and i' is `pullback.snd i p`. The common composite q appears inside
  `finiteClosedSupportDirectImageIso`: it compares the two derived composite
  direct images through `pullback.snd i p ≫ p`, using pullback.condition.
  These are canonical pullback projections, not arbitrary maps satisfying
  a square condition.
- Ordinary small-etale bounded-below derived categories are literally
  `_root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology
  (ModuleCat.{u+1} A))`. Direct images are `lowerStar ... .rightDerivedFunctorPlus`.
  For the five finite maps involved these are the exact direct images, by the
  recorded finite-exactness dependency. The D+ exceptional functors and their
  actual adjunctions are the published `closedSupportPlus` and
  `closedSupportPlusAdjunction`, with no constructibility or coefficient-order
  invertibility condition.
- The natural isomorphism i^!p_* ≅ p'_*i'^! is the existential `e`, an isomorphism
  of functors on D+, not just unrelated objectwise isomorphisms. It is specified
  by `e.inv = finiteClosedSupportExchange A p i`.
- The canonical map c: i_*p'_* ≅ p_*i'_* is
  `finiteClosedSupportDirectImageIso`. It is built with the existing
  `lowerStarComp` and `Functor.rightDerivedFunctorPlusCompIso'`; on sections
  its two sides are both N(V times_X Y'). Its derived composition comparison
  uses the ordinary pullback/direct-image adjunctions. The necessary
  preservation-of-injectives instances are constructed from those adjunctions
  inside this definition, rather than added as hypotheses.
- `finiteClosedSupportCounit` is the actual composite of c and p_* of
  `(closedSupportPlusAdjunction A i').counit`. Reassociation and unitors only
  express the domains of these natural transformations.
- `finiteClosedSupportExchange` is u followed by i^! of that counit composite.
  Thus it is the adjunction transpose specified in proof Step 6. Steps 5–6 of
  the docstring explain its identification with canonical pullback/closed
  exchange followed by the ordinary adjunctions. The canonical map is fixed
  before invertibility is asserted; it is not chosen from a bare existence.
- The normalization i^!i_* ≅ id is the inverse of the closed exceptional unit;
  `IsIso (closedSupportPlusAdjunction A i).unit` states its invertibility. The
  equation `u.app (...) ≫ i^!.map (finiteClosedSupportCounit.app M) ≫
  e.hom.app M = 𝟙 _` is exactly the node's normalized identity on p'_*i'^!M.
  The final `IsIso` clause asserts invertibility of the actual image under i^!
  of p_* of the i' counit, after the canonical compositor c. Since c is already
  an isomorphism, this is equivalent to the displayed untransported map being
  an isomorphism.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`
  (also inspected IsIntegralHom in its owning Integral module).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` and its base-change instance.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.condition`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: ordinary derived and
  bounded-below category convention; inspected current source using
  `scompile.py --source` because the recorded module is absent locally.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `lowerStar`,
  `upperStarLowerStarAdjunction`, `lowerStarComp`.
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`:
  `isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`, the recorded
  ambient existence theorem (used in the D+ interpretation/proof plan).
- `def-per-closed-support-plus-adjunction` (new definition node, existing:true),
  module `Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange`: read the full
  declarations and docstrings of `closedSupportPlus_isLeftAdjoint`,
  `closedSupportPlus`, `closedSupportPlusAdjunction`, and
  `closedSupportPlusCommShift`. These are the general bounded-below adjunction
  helpers for a closed immersion and finite commutative A. The item cites their
  definition node; it does not cite or use the ind-etale base-change theorem.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence` and
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp`:
  the existing D+ direct images and `rightDerivedFunctorPlusCompIso'`.
- All recorded, stated proof dependencies are imported: finite exactness and
  base change, exact inverse image and its module adjunction, ringed-site
  modules, exact derived adjunction, exact-functor comparison, closed ordinary
  full faithfulness, and the Mathlib adjunction and coyoneda tools. Their
  modules are the ones in the node records; no source-library target module
  imports were added.

Edge cases checked before writing: empty Y gives zero support and zero target,
so its identity is the zero-object identity; empty X or X' is allowed. For i=id,
the comparison is the ordinary identity comparison, normalized by its actual
adjunction unit and counit; for p=id it is the same closed right adjoint on both
sides, with pullback unitors. Nonreduced closed subschemes are allowed. Finite
rings of arbitrary characteristic, including the zero ring, are allowed. There
is no reducedness, constructibility, flatness, bounded-above, or invertibility
assumption. Naturality is built into each helper as a natural transformation
and into e as a natural isomorphism. No statement dispute was found.

Searches (before defining anything):

- msearch.py leanfinder: "For finite morphisms of schemes closed exceptional
  inverse image commutes with finite direct image, with counit normalization";
  eight hits about normalization and scheme morphisms, none about this exchange.
  A second query "closed exceptional inverse image finite direct image counit"
  gave eight unrelated topology/closed-set results.
- msearch.py loogle: "CategoryTheory.Adjunction,
  CategoryTheory.Functor.rightAdjoint"; the exact ordinary adjunction constructor
  `CategoryTheory.Adjunction.ofIsLeftAdjoint` was found, not this statement.
- msearch.py grep: "closed.*[Ee]xchange|[Ee]xchange.*closed|lowerStarComp"
  in CategoryTheory; no matching statement.
- rg in the upstream WeilConjectures tree for the node id: no occurrence.
  Searches for closed exchange and finite base change found the existing
  ordinary/derived exchange and direct-image composition APIs, which are reused.
- rg in lean/Sheaf for closedSupportExchange and closed-support/D+ adjoints
  found `EtaleGenericExchangeAlgClosed` (pullback/exceptional comparison, a
  different statement) and `IndEtaleClosedSupportBaseChange` (the required
  bounded-below adjoint, reused). Neither states finite direct-image exchange.
  rg for finiteClosedSupport/closedSupportExchange in the upstream name index
  found no naming collision with the new declarations.

Validation: prescribed scompile.py compiled this file in sandbox and library
modes cleanly (2.3 and 2.5 seconds). Universes and all variables are explicit;
`set_option autoImplicit false` is enabled. The main theorem docstring follows
all seven proof steps, including the exchange/counit identification.

## New nodes

`def-per-closed-support-plus-adjunction` records the existing D+ closed-support
right adjoint, its chosen adjunction and its canonical mate shift structure in
`Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange`. Its four declarations
are `AlgebraicGeometry.Etale.closedSupportPlus_isLeftAdjoint`,
`AlgebraicGeometry.Etale.closedSupportPlus`,
`AlgebraicGeometry.Etale.closedSupportPlusAdjunction`, and
`AlgebraicGeometry.Etale.closedSupportPlusCommShift`. Source: Stacks Tags 09XQ
and 0A45, the supported kernel and its bounded-below derived adjunction.
Finite commutative A is `(A : Type (u+1)) [CommRing A] [Finite A]`; arbitrary
schemes and a closed immersion are `{Z T : Scheme.{u}} (i : Z ⟶ T)
[IsClosedImmersion i]`. The right adjoint is `rightDerivedFunctorPlus.rightAdjoint`;
its actual unit/counit come from `Adjunction.ofIsLeftAdjoint`, and its shift
comparison from `rightAdjointCommShift ℤ`. There is no Noetherian, ind-etale,
constructibility or nonzero-ring restriction in these helpers. Empty schemes,
the identity immersion and the zero coefficient ring remain allowed.

Searches for this node: LeanSearch returned eight ordinary module/open
adjunction and closed-immersion hits; Loogle returned `Adjunction.ofIsLeftAdjoint`
and its unrelated lifting construction; Mathlib grep found only the generic
shift-adjunction API. Source grep found no upstream specialized declaration.
Project grep found exactly the four published helpers in the named module.
DAG grep found them only in the theorem node's declaration inventory;
`blueprint_refs.py search 'closed support'` found twelve nodes with other
support settings, and no definition node carrying these helpers. Therefore
this is an existing:true binding, with no new Lean module or private copy.
The actual search records are in the new node's `mathlib_searches`.

## Repair of returned delivery

The immutable returned head was `7eff593465ab`. H2 is repaired: restore the
base's six statement dependencies and add only the new definition node
`def-per-closed-support-plus-adjunction`. In particular,
`lem-per-ind-etale-closed-support-base-change` is removed from the item's
statement dependencies; none of its base-change conclusions is used.
The Lean file is unchanged from the reviewed packet. The mathematical
statement, all hypotheses, canonical maps and normalization are unchanged.
The new definition node owns precisely the four general adjunction helpers
requested by the maintainer. Existing published declarations are reused
without changing their original module or docstrings.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
