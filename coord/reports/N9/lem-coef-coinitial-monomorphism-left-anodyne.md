## Worker report

The item is stated in `lean/Sheaf/CategoryTheory/CoinitialMonomorphismLeftAnodyne.lean`
as `SSet.Enhanced.coinitial_monomorphism_left_anodyne`. Its sole proof is `sorry`.
The statement is unchanged. One missing definition is added below; no dependency interface
is replaced and no theorem is proved.

Hypothesis and clause correspondence:

- Small simplicial sets: `{K L : SSet.{u}}`, with the universe `u` explicitly declared.
  The same arbitrary universe serves both simplicial sets and their degreewise pullback.
- Both are quasicategories: `[Quasicategory K] [Quasicategory L]`, Mathlib's inner-horn
  filling class, reexported by the enhanced-diagrams dependency.
- The simplicial map: `(j : K ⟶ L)`; degreewise injectivity is literally
  `hj : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (j.app n)`.
- Each vertex is quantified as `l : L _⦋0⦌`. Its map from the standard point is
  `SSet.yonedaEquiv.symm l`.
- The incoming join slice is the dependency's `joinSlice (SSet.yonedaEquiv.symm l)`.
  `JoinSliceSimplex` stores the join extension and its determined initial restriction;
  the dependency theorem asserts that each join map over the point occurs exactly once.
  Its operators precompose on the first block, as required by the node.
- The source projection is the existing `joinSliceProjection`. The comma is exactly
  `pullback j (joinSliceProjection (SSet.yonedaEquiv.symm l))`, the categorical pullback
  of simplicial presheaves, computed degree by degree. This uses incoming arrows to `l`,
  rather than outgoing arrows or a homotopy-category comma.
- Weak contractibility of every comma is `hcomma : ∀ l, IsContractible (...)`.
  The dependency's `IsContractible` is the weak homotopy equivalence of its unique map
  to the standard point. `IsWeakHomotopyEquivalence` uses bijectivity on realization's
  path components and all positive based homotopy groups, so an empty comma fails.
- The conclusion is `SSet.leftAnodyneExtensions j`, defined by the new definition node.
  Its `sInf` ranges over all morphism classes containing isomorphisms and the stipulated
  horns, stable under pushouts, transfinite compositions, and retracts.
- The horn conditions are `1 ≤ n` and `i < Fin.last n`, for `i : Fin (n + 1)`.
  Thus exactly `n ≥ 1` and `0 ≤ i < n` occur. Isomorphisms use
  `MorphismProperty.isomorphisms SSet ≤ P`; closure uses `P.pushouts ≤ P`,
  `MorphismProperty.transfiniteCompositions.{u} P ≤ P`, and `P.retracts ≤ P`.
- There is no full-subcomplex assumption. The image may omit edges between its vertices.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsContractible` and
  `SSet.Enhanced.IsWeakHomotopyEquivalence`; also read the recorded `coneCategory`
  declaration and docstring. Mathlib's `SSet.Quasicategory` supplies the quasicategory notion.
- `Sheaf.CategoryTheory.JoinSliceRightFibration`: `SSet.Enhanced.JoinSliceSimplex`,
  `joinSlice`, `joinSliceProjection`, and the full signature and docstring of the recorded
  `joinSlice_right_fibration`.
- The new `Sheaf.CategoryTheory.LeftAnodyne`: `SSet.leftAnodyneExtensions`.
- Mathlib `AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic` supplies the existing
  morphism-property weak-saturation operations, also used by the project's right-anodyne
  definition. Its all-horn `SSet.anodyneExtensions` is not the one-sided notion here.

All recorded, available proof-dependency modules are imported without `public`:
`InfinityFibrationsOverSimplicialBases`, `RightAnodyne`, `LeftFibrationEquivalenceLift`,
`SimplicialGroupoidLocalization`, `InfinityCofinalCommaCriterion`, `IsofibrationPullbackLimit`,
`RelativeConeEquivalence`, and `SliceArrowEquivalence` (all under `Sheaf.CategoryTheory`).
The shared statement dependency `JoinSliceRightFibration` is a public import.
`lem-coef-universal-cocone-restriction-right-anodyne` has no recorded Lean module on the
read base, so there is no module to import for this proof-only prerequisite. It remains
explicitly named in the proof docstring and in the unchanged DAG proof dependency list.
The theorem's docstring includes all five proof steps, including the strict/homotopy
comma comparison, slice-arrow identification, groupoid localization, cocone recognition,
and reversal of the weak saturation.

Edge cases checked before drafting:

- `K = L` and the identity: the incoming slice has terminal object `id_l`; the conclusion
  includes every isomorphism, including the empty identity.
- Empty `K` and nonempty `L`: incoming commas are empty, so their component map to a point
  is not bijective. The theorem cannot incorrectly deduce the addition of an isolated vertex.
- Empty `L`: a map into it forces empty `K`; the vertex hypothesis is vacuous and the map is
  an isomorphism. No nonemptiness assumption is added.
- The inclusion `{0} → Δ[1]` satisfies the incoming-comma condition and is the dimension-one
  left horn. The inclusion `{1} → Δ[1]` fails at vertex `0`. This checks the orientation.
- The non-full inclusion `Λ[2,0] → Δ[2]` is a valid case: its source is the nerve of the
  category with arrows `0 → 1` and `0 → 2`, its incoming commas are contractible, and it is
  itself a left-horn generator. No fullness is silently imposed.
- Dimension zero contributes no generators. The final horn is excluded in every dimension.

Searches:

- `msearch.py ... leanfinder` with “A degreewise injective map of quasicategories whose
  incoming comma simplicial sets are weakly contractible is left anodyne”: eight results,
  all general horn/boundary generators, mono properties, or quasicategory horn filling;
  no matching statement or one-sided anodyne class.
- `msearch.py ... loogle` with `SSet.leftAnodyne, SSet.rightAnodyne`: zero results,
  unknown identifier `SSet.leftAnodyne`.
- `msearch.py ... grep` with `left.?[Aa]nodyne|coinitial`, restricted to `AlgebraicTopology`:
  zero results.
- `msearch.py ... leansearch` with “left anodyne maps simplicial sets weakly saturated left
  horn inclusions”: eight results about all-horn generators, ordinary Kan fibrations and
  horn filling; none defines this one-sided class.
- Direct `rg` in the named Mathlib tree, upstream `WeilConjectures`, and shared `lean/Sheaf`
  found no declaration matching `leftAnodyne|left_anodyne|leftHorn|LeftAnodyne`. Wider
  textual searches found uses of left-anodyne terminology and the existing right-anodyne
  class, not a left-anodyne definition or this theorem. Searching the upstream source for
  the item's blueprint id found no match. The upstream name index has no matching name.
- Definition-node scan in `dag/nodes` found no definition containing “left anodyne” or
  “left-anodyne”; `tools/blueprint_refs.py search "left anodyne"` returned zero blueprint
  nodes. `ancestor` identifies `prop-coef-integral-exceptional-adjoint`.

Source checked: [HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf), Definition the project server,
Remark the project server, Proposition the project server(4), and Theorem the project server. The last two applied to
opposites give precisely this orientation. No statement correction or dispute is needed.

Validation: `scompile.py N9 lem-coef-coinitial-monomorphism-left-anodyne` compiled
both delivered files separately in dependency order, including their library-path checks,
with no errors and no warnings. Each individual compile took under three seconds.
The required `deliver2.py ... --no-push` checks follow; no push is authorized for this worker.

## New nodes

`def-coef-infinity-left-anodyne` defines the weakly saturated class of positive-dimensional
left horns, in its own `lean/Sheaf/CategoryTheory/LeftAnodyne.lean`. It uses the existing
simplicial sets and horns through `def-cbc-enhanced-diagrams-cones`, with actual data given
by an infimum of morphism properties. Source: HTT Definition the project server and Remark the project server,
where the small object argument identifies the horn-generated weak saturation. The searches
above found only ordinary all-horn anodyne extensions and the distinct right-anodyne class;
there was no node or usable declaration for this notion. Their raw msearch records and the
local source-search results are recorded in the new node's `mathlib_searches`. The item's
`stmt_deps` gains this node; all other existing node fields besides `lean` are preserved.


## Second reading by N9

I independently opened the item node, both delivered Lean modules, the new definition node,
all statement-dependency records, and the source declarations those records name. There is
no repair note for this item. I read the actual HTT PDF online at its recorded source URL:
Definition the project server and Remarks the project server--7 (printed pp.53--55), Proposition the project server(4)
(printed pp.223--224), and Theorem the project server (printed p.236). This item has no Stacks source.
The theorem is the opposite of the outgoing-comma criterion followed by the monomorphism
recognition result. The source requires no fullness, finiteness, or nonemptiness assumption.
The node already asks for both source and target to be quasicategories, so retaining both
Lean instances is exact even though HTT's more general criterion only needs the target.

Objects, hypotheses, and conclusions, checked item by item (H3):

1. Small simplicial sets K and L: `{K L : SSet.{u}}`, with explicit `universe u`.
   Verdict: exact, arbitrary common small universe, no bound or extra size instance.
2. K and L are quasicategories: `[Quasicategory K] [Quasicategory L]`. I opened
   Mathlib's `AlgebraicTopology/Quasicategory/Basic.lean`: these are the inner-horn
   filling predicates, with neither outer-horn filling nor inhabitedness added.
   Verdict: exact.
3. A simplicial map j: `(j : K ⟶ L)`; its degreewise injectivity:
   `(hj : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (j.app n))`.
   All simplex degrees are covered; no fullness or bijectivity is imposed.
   Verdict: exact.
4. Every vertex l of L: `∀ l : L _⦋0⦌` inside `hcomma`. The canonical map from
   the standard point is `SSet.yonedaEquiv.symm l`. Verdict: exact, no chosen vertex
   and no nonempty-L assumption.
5. The incoming slice L_/l: `joinSlice (SSet.yonedaEquiv.symm l)`, used through
   `joinSliceProjection`. I opened `JoinSliceRightFibration.lean`, including
   `joinStandardFunctor`, `JoinSliceSimplex`, `joinSlice`, `joinSliceProjection`,
   and `joinSlice_right_fibration`. The join has the variable standard simplex
   first and the fixed point last; restriction on the final block is l, and
   operators precompose the variable block. The stored base is determined by
   restriction to the first block. The recorded theorem explicitly gives unique
   representation of every join extension, so the stored data do not restrict
   the stipulated maps. Verdict: the recorded dependency supplies exactly L_/l.
6. Source projection L_/l -> L: `joinSliceProjection` sends a simplex to its
   initial-block `base`; it does not evaluate at the fixed final vertex.
   Verdict: correct orientation.
7. The strict comma K x_L L_/l:
   `pullback j (joinSliceProjection (SSet.yonedaEquiv.symm l))`.
   This is the simplicial-presheaf pullback, hence degreewise. It is not an
   ordinary homotopy-category comma. No additional quasicategory hypothesis
   on the comma is necessary: it follows from the recorded right-fibration
   dependency by base change. Verdict: exact object and quantifier order.
8. Each comma is weakly contractible: `IsContractible (...)`. I opened
   `EnhancedDiagramsCones.lean`, including `componentsMap`, `homotopyGroupMap`,
   `IsWeakHomotopyEquivalence`, and `IsContractible`. The latter tests the unique
   map to the actual standard point; it includes bijectivity of path components
   and of every positive based homotopy-group map after realization.
   Verdict: exactly the node's weak contractibility, not just connectedness.
9. The conclusion: `SSet.leftAnodyneExtensions j`. The new definition is an
   actual infimum of all morphism properties containing isomorphisms and
   `P (SSet.horn n i).ι` when `1 ≤ n` and `i < Fin.last n`.
   A `Fin (n+1)` index is automatically nonnegative. The three closure clauses
   `P.pushouts ≤ P`, `transfiniteCompositions.{u} P ≤ P`, and `P.retracts ≤ P`
   are precisely pushout, small transfinite-composition, and arrow-retract
   closure. I opened those Mathlib definitions and the existing right-anodyne
   definition for comparison. Verdict: exactly the smallest class in the node.
10. No full-image assumption: the binders are exhausted by items 1--8 above.
    Verdict: the explicitly permitted non-full case remains included.

Edge cases: empty L forces empty K and gives a vacuous vertex hypothesis, with an
isomorphism as conclusion. Empty K and nonempty L fails the component condition on
an incoming comma, so it cannot add an isolated vertex. Identity maps, including the
empty identity, are covered. The point inclusion at 0 in Delta[1] satisfies the
incoming-comma condition and is the left horn; inclusion at 1 fails at vertex 0.
The non-full inclusion Lambda[2,0] -> Delta[2] is also covered: its source is the
nerve of the fork 0 -> 1, 0 -> 2, and each incoming comma is contractible. For n=0
there is no allowed generator; in dimension one exactly i=0 occurs, and the final
horn is excluded in every dimension. The small transfinite-composition universe is
u, matching the small simplicial sets and the existing weak-saturation convention.
There are no fields, characteristic assumptions, schemes, or additive zero objects
in this statement; the pertinent empty simplicial set cases were checked above.

Independent searches (H4), using different queries from the first worker:

- `msearch.py ... leanfinder` with "A simplicial inclusion between infinity
  categories is initial when each overcategory pullback has contractible geometric
  realization": eight hits, including ordinary truncated-simplex initiality,
  initial simplicial objects, and `CategoryTheory.Nerve.quasicategory`; no match.
- `msearch.py ... leansearch` with "weak saturation generated by all horns except
  the final horn in simplicial sets": eight hits, all basic quasicategory/Kan
  fillers or all-horn generators; no one-sided saturation.
- `msearch.py ... loogle` with `SSet.horn, CategoryTheory.MorphismProperty`:
  only `SSet.innerHornInclusions_eq_iSup`; inner horns omit both outer horns,
  so this is a different generating family.
- `msearch.py ... grep` with `initial|covariant` in
  `AlgebraicTopology/SimplicialSet`: 23 hits, ordinary initial objects, opposite
  involutions, and pushout-product lemmas; none states the criterion or definition.
- Direct `rg` of Mathlib's algebraic-topology tree, the upstream `WeilConjectures`,
  shared `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `left[A-Za-z_]*[Aa]nodyne|[Ii]nitial.*[Mm]onomorphism|[Cc]oinitial|left.horn`
  found terminology in unrelated docstrings, not an existing declaration.
  The ordinary `SSet.anodyneExtensions` was opened: it uses all horns and differs
  from this one-sided notion. The existing right-anodyne class has the opposite
  generator indices. The marked-coanodyne DAG definition was also opened and
  concerns marked simplicial sets and additional marking generators, not this class.

New-node review (H12): `def-coef-infinity-left-anodyne` is absent from the shared DAG
and supplies a genuinely missing unmarked notion. Its self-contained statement and
its real infimum construction agree with the horn family in HTT the project server, with weak
saturation identified by the small object argument of Remark the project server. Its sole cited
notion is `def-cbc-enhanced-diagrams-cones`, exactly its `stmt_deps`; its source,
searches, creation, blueprint ancestry/via, empty proof fields, null match,
`lean_audit`, chapter, unit, and Lean record have the required forms. The item cites
it. No dependency module repair is needed (H13).

H5--H9: the new definition has actual data and contains no postponed proof. The only
new theorem has exactly a `sorry` proof. Both module/declaration docstrings carry the
correct source and blueprint id, and the theorem docstring follows all five DAG proof
steps, including the slice-arrow comparison and reversal of weak saturation. All
recorded proof-dependency modules are imported; the sole unstated proof-only prerequisite
has no module and is explicitly identified in the worker report. There is no statement
correction, so no `statement_change` or citer audit is required. There are no local
notations, private duplicate notions, hidden `let` binders, unbound variables or universes,
or lines over 100 characters. Both `lean.statement` records were compared with the
corresponding declaration signatures and agree verbatim.

Mismatches found and changes: none in the Lean, item statement, or new-node data.
I preserved both modules and node records and appended this independent reading only.
Validation: I ran the required `scompile.py N9 lem-coef-coinitial-monomorphism-left-anodyne`
on `LeftAnodyne.lean` followed by `CoinitialMonomorphismLeftAnodyne.lean`. Both compiled
cleanly, including overlay and library-path checks, with no errors or warnings; each
individual compile took at most two seconds. The delivery dry run and push are next.
