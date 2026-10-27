# Local representing schemes: stage 2

## Worker report

The module `Sheaf.AlgebraicGeometry.FppfLocalRepresentationsFullyFaithful` states
`AlgebraicGeometry.fppfLocalRepresentationsFullyFaithful`, with its entire proof
`sorry`. There are no definitions, additional postponed theorems, new nodes,
dependency repairs, statement corrections, or disputes. The node copy changes only
`lean`. Its existing Q117 PASS is the stage-1 split review, not a Lean-statement
review; the existing stage-1 split is retained unchanged.

Read the item, all seven statement dependencies and their records, the recorded
interfaces in SchemeCoverDescentDatum.lean, SiteCoveringAxioms.lean, Mathlib's
Scheme.lean, Sites/Fpqc.lean, Sites/Over.lean, Yoneda.lean, the pullback interface,
and ModuleCat/Sheaf/PushforwardContinuous.lean. Read the parent equivalence module
for comparison, but do not import it or use its theorem (that would be circular).
Read Stacks descent.tex, lemma-descent-data-sheaves (02W5), its full proof and
remark-what-product-means, and the existing set-sheaf gluing interface (04TQ).

Hypotheses and clauses, in statement order:

- Scheme and set-indexed family: `T : Scheme.{u}`, `I : Type (u + 1)`,
  `U : I → Scheme.{u}`, `f : ∀ i, U i ⟶ T`. These are precisely the shared
  dependency's size conventions: scheme objects have universe u+1, and Hom sets are lifted into the
  universe u+1 of section sets and the covering index when necessary.
  Additional `v w` only parameterize diagrams in the final naturality clause.
- Fppf covering: `hcov : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T`.
  This is joint surjectivity, flatness and local finite presentation, without
  an affine, finite, quasi-compact, separated, or nonempty-family assumption.
- Big fppf sheaves and the full category L:
  `(IsLocallyRepresentableFppfSheaf f).FullSubcategory`, using the dependency's
  predicate on `Sheaf (Scheme.fppfTopology.over T) (Type (u + 1))`.
  Its definition uses representability of restriction, exactly the equivalent
  condition in the last sentence of the dependency and in the Stacks remark.
- Chosen representing schemes and alpha: `X H i : Over T`, and
  `alpha H i : (prod (uliftYoneda.obj (Over.mk (f i))) H.obj.obj).RepresentableBy
  (X H i)`. `RepresentableBy.homEquiv` is a natural bijection on every test
  object and is equivalent to the natural isomorphism in the node. ULift
  merely places the Hom sets in the sheaves' value universe.
- Existence of R into the specified D: the existential `R` has target
  `SchemeCoverDescent f`, the recorded Yoneda encoding of scheme descent data.
  `p H i` is a map from the *chosen* `(X H i).left` to `U i`.
  `localEq` says that the local scheme of R is exactly `Over.mk (p H i)`.
  The comparison `q H i` is over T and has underlying map the identity of
  `(X H i).left`. Thus it imposes `p H i ≫ f i = (X H i).hom`, rather than
  replacing the chosen representing scheme with an unrelated representative.
- The first projection is represented by p: the first product-projection
  equality says, for every `W : Over T` and `x : W ⟶ X H i`, that the
  underlying map of alpha(x)'s first coordinate is `x.left ≫ p H i`.
  Equality of these underlying maps is equality of the maps over T by Over
  extensionality. This specifies the first projection on all sections.
- Slice fibre bijections, natural in every test object and map: `b H i` is
  the `RepresentableBy` structure for the sectionwise restriction of H on
  `Over (U i)`, represented by `Over.mk (p H i)`. Its `homEquiv` is exactly
  `Mor_{U_i}((W,a),X_i) ≃ H(W)` and its `homEquiv_comp` is the required
  naturality equation. Its equivalence includes both inverse identities.
  The second product-projection equality says that its value is precisely
  alpha's second coordinate, after forgetting the slice map via `Over.map`
  and the identity comparison q. Together the two projection equalities
  recover alpha on every fibre: an arbitrary map into X has the slice
  structure `a = x.left ≫ p`, and every pair `(a,s)` is obtained uniquely
  by the inverse of `b` over a. This is the disjoint-union recovery clause;
  it is expressed by the two projections of the actual presheaf product,
  rather than a new copy of the product or a second representability notion.
- Overlap transitions preserving all three coordinates: `e` is a natural
  isomorphism from `R ⋙ schemeCoverDescentForget f` to the inclusion of L
  followed by Mathlib's `toDescentData f`. The latter uses the actual
  sectionwise restrictions and their canonical overlap comparisons.
  The compatibility equation with b identifies the coordinate map from
  each local representing scheme with precisely this `e.hom` component.
  The descent-isomorphism compatibility in e therefore says, on every
  double-slice test object `(W,a_i,a_j)`, that b_j(phi(x,a_j)) = b_i(x).
  The two base coordinates are retained because the representing maps
  are maps in the over-categories. Yoneda identifies this with exactly
  the stated scheme isomorphism, and the descent data already includes
  its identity, invertibility, naturality, and triple cocycle.
- For a sheaf map v, the local map represents `id × v`: naturality of e
  says that its local maps, conjugated by b, are the restrictions of v.
  The preceding alpha-coordinate equations identify this with `id × v`
  in the product presentations. This records a natural isomorphism of
  *functors*, not just objectwise comparisons, so it includes this clause.
- Bijective Hom map: `Function.Bijective (R.map : (H ⟶ K) → ...)`, for
  every H and K. This is the Hom map of the constructed functor itself.
- Compatible local isomorphisms extend uniquely: `∀ H K (c : R.obj H ≅
  R.obj K), ∃! z : H ≅ K, R.mapIso z = c`. By the shared induced-category
  encoding and e, c is precisely a compatible family of local slice
  isomorphisms. This includes uniqueness of the isomorphism, not merely
  existence of an unspecified global comparison.
- Naturality of families: for every category J and diagrams A and B in L,
  every compatible natural family `c : A ⋙ R ≅ B ⋙ R` lifts uniquely to
  `z : A ≅ B` with `Functor.isoWhiskerRight z R = c`. The preceding unique
  componentwise extension makes this equivalent to the node's assertion
  that global comparisons are natural whenever their restrictions are.

Dependencies used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, scheme Hom.
- Mathlib.AlgebraicGeometry.Sites.Fpqc: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology` (re-exported by SchemeCoverDescentDatum).
- Mathlib.CategoryTheory.Sites.Over: `GrothendieckTopology.over`,
  `overMapPullback` (sectionwise restriction), `Over.map`.
- Sheaf.CategoryTheory.SiteCoveringAxioms:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, imported transitively;
  the actual site used is the recorded fppf Grothendieck topology.
- Sheaf.AlgebraicGeometry.SchemeCoverDescentDatum:
  `SchemeCoverDescentDatum`, `SchemeCoverDescent`,
  `schemeCoverDescentForget`, `IsLocallyRepresentableFppfSheaf`.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous: imported
  publicly as the localization dependency's recorded module; the set-sheaf
  component used here is the same `GrothendieckTopology.overMapPullback`.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`
  and its projections, supplied transitively by the scheme/site imports;
  overlaps are represented by Mathlib descent data on all test objects,
  so no second fibre-product construction is introduced.
- Mathlib.CategoryTheory.Yoneda: `Functor.RepresentableBy`,
  `uliftYoneda`, `Yoneda.fullyFaithful`; the last is a Mathlib proof leaf.
- Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver and
  Sites.Descent.DescentData: `pseudofunctorOver`, `toDescentData`, and its
  descent-object/morphism compatibility. These are the dependency's
  recorded scheme-data encoding, not a replacement category.
- Sheaf.CategoryTheory.SetSheafCoverDescent:
  `CategoryTheory.setSheafCoverDescent`, imported only for the proof.
  Its morphism clause gives precisely the proof's unique sheaf-map gluing.

Edge cases checked mathematically before writing: an empty cover is permitted
exactly when the base is empty, in which case the sheaf axiom makes all section
sets singletons and the unique empty descent morphism gives the required Hom
bijection. Identity singleton covers and covers with repeated indices give the
expected restrictions and identity/cocycle clauses. Empty representing schemes
cause no choice of an element of an empty section set: only natural equivalences
are used. No argument requires global representability, effective scheme descent,
or any separation assumption. Arbitrary diagram universes in the naturality
clause introduce no additional size condition on the original site.

Searches actually run with the prescribed msearch.py wrapper:

- LeanFinder: "For an fppf covering choosing local representing schemes of
  sheaves gives a fully faithful functor to scheme descent data". Eight hits,
  including Pseudofunctor.fullyFaithfulToDescentData, the IsPrestackFor variants,
  and unrelated fully faithful forgetful functors. No exact match: none gives
  the chosen product representations and their fibre/coordinate compatibility.
- Loogle: `CategoryTheory.Pseudofunctor.fullyFaithfulToDescentData`. One hit,
  the generic restriction functor given a prestack; not this full statement.
- Mathlib grep: `FullyFaithful|fullyFaithfulToDescentData` in
  CategoryTheory/Sites/Descent. Eleven hits, generic descent interfaces only.
- LeanSearch: "The functor assigning local representing schemes to locally
  representable fppf sheaves is fully faithful". Eight hits, generic Yoneda,
  descent, and sheaf forgetful full-faithfulness; none states all these clauses.
- Direct rg in lean/WeilConjectures and lean/Sheaf for
  `SchemeCoverDescent|LocalRepresent|localRepresentation|descentFunctor` found
  the recorded scheme descent category, the larger parent equivalence, and
  Zariski or unrelated representations. The larger parent is deliberately not
  used. Exact item-id search in both trees found no existing declaration.
  Exact declaration-name search in both trees and Mathlib found no collision.

Validation: scompile.py compiled both its private sandbox module and the actual
module path cleanly, with no errors or warnings (1.9 s and 2.1 s). The only proof
postponed in this delivery is the named theorem of this item, and its docstring
contains the entire coordinate construction and unique-gluing argument.

## Second reading by Q12

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
