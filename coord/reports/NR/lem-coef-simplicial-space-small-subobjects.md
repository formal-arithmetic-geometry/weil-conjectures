## Worker report

The delivery states `CategoryTheory.simplicial_space_small_subobjects` in
`Sheaf.AlgebraicTopology.SimplicialSpaceSmallSubobjects`. Its proof is `sorry`.
The helpers construct real data: the total simplex type `bisimplices`, subspaces as
Mathlib subfunctors, their bounded subtype, inclusion maps, pullback intersections,
the inclusion transition squares, their functor `intersectionDiagram`, and the
specified cocone `intersectionCocone`. All helper declarations are recorded in
`lean.declarations`. There are no additional postponed theorems or hollow definitions.
The elementary naturality, commutativity, and functor-law proofs only construct the
structures needed to type the main statement.

Hypothesis and clause correspondence:

- The fixed universe is `universe u`. Simplicial spaces are Mathlib's
  `SimplicialObject SSet.{u}` directly, hence functors from the opposite simplex
  category to simplicial sets. No duplicate simplicial-space definition is introduced.
  This is definitionally the existing `SSet.SegalSpace.SimplicialSpace` from
  `Sheaf.AlgebraicTopology.SegalCartesianExponent`; the larger model-category module
  is unnecessary for the purely combinatorial statement.
- `bisimplices B` is `Σ p, Σ q, (B.obj p).obj q`, exactly the coproduct over all
  bidegrees. `HasCardinalLT (bisimplices B) γ` expresses the strict total-cardinal bound.
- Small infinite regular cardinals are `γ : Cardinal.{u}` with `[Fact γ.IsRegular]`.
  `Cardinal.aleph0 < γ` is uncountability. The morphism bound is
  `HasCardinalLT (Arrow (SimplexCategory × SimplexCategory)) γ`: Mathlib `Arrow C`
  has exactly one object for each morphism of `C`.
- In the first conjunct, `∀ {A B} (f : A ⟶ B)` ranges over every arrow, with no mono
  requirement. The two hypotheses `HasCardinalLT (bisimplices A) γ` and
  `HasCardinalLT (bisimplices B) γ` are both present. Its conclusion is
  `IsCardinalPresentable (Arrow.mk f) γ`, Mathlib's preservation of all small
  `γ`-filtered colimits by the ordinary Hom functor in the arrow category.
- In the second conjunct, `f : X ⟶ Y` and `[Mono f]` express the given monomorphism.
  The same uncountability, regularity and simplex-category morphism bound are repeated.
- `SimplicialSubspace Y` is `Subfunctor (Functor.uncurry.obj Y)`. Its objects are
  subsets in each bidegree stable under both directions, its partial order is
  inclusion, and its restricted functor is curried back to a simplicial space.
  `SmallSubspaces Y γ` is the subtype imposing the strict total-cardinal bound.
  It inhabits `Type u` with its inherited small poset category, so the required
  smallness is built into this index. `IsCardinalFiltered (SmallSubspaces Y γ) γ`
  is the required filteredness, including existence of cocones on the empty diagram.
- `intersectionArrow γ f B` is the pullback projection
  `X ×_Y B ⟶ B`. For a mono this is the intersection `X ∩ B ⟶ B`, after the
  canonical identification of `X` with its image. This avoids replacing an arbitrary
  given monomorphism by an unrelated subset embedding. Presheaf pullbacks are pointwise,
  so these are precisely bidegreewise intersections.
- `intersectionTransition` uses the identity of `X` and the actual inclusion
  `B ⟶ C`; `intersectionDiagram` packages these transition squares with their
  functor laws. `intersectionCocone` has point `Arrow.mk f` and its component at `B`
  has left map the pullback projection to `X` and right map the inclusion `B ⟶ Y`.
  Thus `Nonempty (IsColimit (intersectionCocone γ f))` asserts the universal property
  of this exact canonical cocone, without existentially choosing different transition
  maps or cocone legs.

Dependency sources read and used:

- `def-weil-pbc-simplicial-set` is a Mathlib leaf. Read `SSet` in
  `Mathlib.AlgebraicTopology.SimplicialSet.Basic` (lines 33--37), its underlying
  `CategoryTheory.SimplicialObject` in `SimplicialObject.Basic` (lines 47--51),
  `SSet.degenerate`/`nonDegenerate` in `SimplicialSet.Degenerate` (lines 34--42),
  `SSet.Subcomplex` in `Subcomplex` (lines 44--45), and `SSet.Finite` in `Finite`
  (lines 30--33). Only the functor notion is needed here. Bidegree subspaces use
  `CategoryTheory.Subfunctor` in `CategoryTheory.Subfunctor.Basic` (lines 34--45),
  with its existing partial order, `toFunctor`, and `homOfLe`.
- `def-weil-pbc-category-colimit` records `CategoryTheory.Limits.colimit` in
  `Mathlib.CategoryTheory.Limits.HasLimits`. Read the chosen cone/limit declarations
  and `to_dual` attributes generating `colimit`, plus the `Cocone`/`IsColimit` interface.
  This statement uses `Cocone` and `IsColimit` directly for the specified cocone.
- Proof input `lem-coef-accessible-set-functor-limits` is the Mathlib leaf
  `CategoryTheory.Functor.isCardinalAccessible_of_isLimit` in
  `Mathlib.CategoryTheory.Presentable.Limits` (lines 158--168), read in full and
  imported without `public`. Its bound is `HasCardinalLT (Arrow K) κ` and its
  conclusion is accessibility of the limit; it imposes no extra domain accessibility.
- Cardinal filteredness and presentability use the existing definitions in
  `Mathlib.CategoryTheory.Presentable.IsCardinalFiltered` (lines 39--47) and
  `Presentable.Basic` (Hom accessibility via `IsCardinalPresentable`).

Source: read the current main-20261015 ancestor proof
`sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`
in full. As the node itself records, that ancestor concerns derived coefficient
adjunction and does not literally state this auxiliary combinatorial lemma. The
formal statement follows the reviewed node and its six explicit agent proof steps;
the module docstring identifies this provenance and the theorem docstring includes
those steps in full.

Edge cases checked: empty `A` or `B`; the unique arrow on empty simplicial spaces;
empty `Y`, for which the bounded-subspace poset still has the empty subspace; empty
indexing diagrams in cardinal filteredness; bidegrees with empty sets; simplices in
bidegree `(0,0)`; and arbitrary arrows in the presentability clause rather than only
monomorphisms. The universe of the total set and cardinal is `u`, and `Type u` indexes
all colimits in the `IsCardinalPresentable` convention. No new equality between
independent universe levels is imposed. Both endpoint bounds are essential and are
explicit in the final signature. There is no statement correction or dispute.

Searches actually run in this worker session:

1. `msearch.py ... leanfinder "bounded simplicial subspaces arrows cardinal presentable filtered union"`
   returned eight hits, including `SSet.Finite.instIsFinitelyPresentable`, generic
   cardinal presentation results, and stability of simplicial monos under filtered
   colimits. None states the bounded bisimplicial arrow and subspace-exhaustion theorem.
2. `msearch.py ... loogle "IsCardinalPresentable, Arrow"` returned zero hits and an
   unknown-identifier diagnostic for unqualified `IsCardinalPresentable`. This query
   alone is not evidence of absence.
3. `msearch.py ... grep "Arrow.*[Pp]resentable|[Pp]resentable.*Arrow" CategoryTheory/Presentable`
   returned `Presentable/Dense.lean` lines 69 and 79 about costructured-arrow categories
   of presentables; neither is this statement.
4. `msearch.py ... leansearch "A bounded bisimplicial set is cardinal presentable in the arrow category and small subobjects form a filtered colimit"`
   returned eight generic presentability and finite-simplicial-set results, including
   `isCardinalPresentable_of_isColimit` and `ColimitPresentation.isCardinalPresentable`.
   They require presentation data and do not supply the bounded arrow theorem or
   this specific canonical intersection cocone.
5. `rg` over Mathlib category-theory, simplicial-set, and cardinal sources found the
   reused APIs listed above. `rg` over upstream `WeilConjectures`, project `lean/Sheaf`,
   and `dag/lean_names_upstream.json` for the item id, `SimplicialSpace`,
   `simplicial_space_small_subobjects`, `bisimplices`, bounded subspaces and canonical
   intersection diagrams found no exact theorem or existing bounded-subspace API.
   The existing simplicial-space abbreviation was read and replaced in this module
   by its Mathlib expression rather than declared again. The full existing node
   search history was also read, but is not represented as fresh searches by this worker.

Validation: the final module passes `scompile.py NR lem-coef-simplicial-space-small-subobjects`
without errors or warnings; it is compiled both as sandbox source and at its final
module path. The final dry run is run after updating the JSON signature verbatim.
No new definition nodes or dependency modules were necessary: all helpers construct
objects already specified by this item's statement and use existing Mathlib notions.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
