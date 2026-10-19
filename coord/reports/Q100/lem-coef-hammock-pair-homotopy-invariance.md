## Worker report

The delivery adds the definition module `Sheaf.CategoryTheory.SimplicialHammockPair` and the
statement module `Sheaf.CategoryTheory.HammockPairHomotopyInvariance`.  The definition module
uses the landed `CategoryTheory.ReducedHammock`, `CategoryTheory.HammockReduces`, and
`CategoryTheory.hammockRows` declarations from `Sheaf.CategoryTheory.HammockInfinityLocalization`.
`WideSimplicialSubcategory` records the marked morphism property, its multiplicative closure,
and the wide simplicial subcomplexes. `SimplicialHammockMapping` records the degree-
`n` equivalence with reduced rectangular hammocks and the row operators. `SimplicialHammockPair`
records the family and concatenation reduction, and `SimplicialHammockComparison` records the
common object set, the simplicial functor, preservation of marked arrows, ambient and marked
mapping-space weak equivalences, and the comparison obtained by applying the functor and
reducing.

The item theorem is
`CategoryTheory.hammock_pair_homotopy_invariance`.  Its sole explicit hypothesis is a
`SimplicialHammockComparison C`; the fields of that structure render the source hypotheses as
follows.

* `C.O`, `C.objectA`, `C.objectB`, and `C.object_identity` render the small fixed object set
  and the assertion that the functor is the identity on objects (up to the displayed object
  identifications).
* `C.A`, `C.B`, `C.U`, and `C.V` render the two simplicial categories and their wide marked
  simplicial subcategories.  `U.multiplicative` and `V.multiplicative` give closure under
  identities and composition; no saturation or two-out-of-three field occurs.
* `C.S` is the simplicial functor. `C.sends_marked` renders that marked arrows map to marked
  arrows. `C.mapping_weak_equivalence` renders the weak equivalence
  `A(x,y) -> B(x,y)` for every pair, and `C.marked_map` together with
  `C.marked_mapping_weak_equivalence` renders the corresponding assertion for `U(x,y) ->
  V(x,y)`.
* `C.hammockA` and `C.hammockB` render `diag H(A,U)` and `diag H(B,V)`.  Their mapping
  fields identify each degree with `ReducedHammock`, while `row_operators` and `composition`
  render deletion/repetition of rows, reduction of identity and like-directed columns, and
  concatenation followed by reduction.  The empty/length-zero path is present in
  `ReducedHammock` via `Quiver.Path.nil`.
* `C.comparison` is the map applying `S` to arrows and reducing, and `C.reduction` records
  this representativewise.  The theorem conclusion is
  `∀ x y, SSet.Enhanced.IsWeakHomotopyEquivalence (C.comparison x y)`, exactly the
  mappingwise weak homotopy equivalence conclusion.

The proof is intentionally `sorry`; its docstring follows the node proof: fixed-word graph
invariance, properness of the signed-word diagrams, proper-colimit invariance, and the hammock
graph colimit presentation.  The statement module imports the coherent-nerve comparison and
simplicial-hammock definition modules, which are the statement dependencies used here.

Edge cases checked before writing: the object set `O` may be empty; the endpoint case `x = y`
contains the length-zero `Quiver.Path.nil`; degree `n = 0` gives one row; identity columns are
removed by the canonical `HammockReduction`; adjacent columns of equal direction are composed;
leftward columns retain the marked-arrow condition; and no freeness, cofibrancy, saturation, or
2-out-of-3 assumption is present.

Searches for existing notions: `msearch.py leanfinder` query “reduced hammock mapping
simplicial set for a simplicial category pair” returned only `SimplicialCategory.sHom` and
`SimplicialThickening.SimplicialCategory.Hom`, which are not hammock constructions;
`msearch.py loogle` query `"Hammock"` returned no Mathlib hits; `msearch.py grep` query
`hammock|Hammock|ReducedHammock` in `AlgebraicTopology` found no Mathlib declaration and
found the project’s landed `CategoryTheory.ReducedHammock` in
`Sheaf.CategoryTheory.HammockInfinityLocalization`, which is reused.  `rg` over both source
checkouts and `lean/Sheaf` found no existing declaration of this item or a pair-invariance
comparison.

No `STATEMENT-DISPUTED` flag or node fault was found.

## New nodes

`def-coef-simplicial-hammock-pair` defines the reduced hammock mapping object and comparison
interface required by the item.  Its source is Dwyer--Kan, Definitions 2.1 and 5.1 (printed
pp.20 and 24).  LeanFinder, Loogle, and Mathlib/project grep searches are recorded in its node;
there is no existing Mathlib or project declaration of this simplicial-pair notion.  It reuses
rather than duplicates the landed `ReducedHammock` and row-reduction declarations.

## Dependency modules

None.  The recorded declaration of `lem-coef-coherent-nerve-comparison`,
`CategoryTheory.coherent_nerve_comparison` in
`Sheaf.CategoryTheory.CoherentNerveComparison`, is usable as recorded; the canonical hammock
reduction declarations are imported from the landed `lem-coef-hammock-infinity-localization`
module.

## Earlier second reading (a previous round; superseded)

I reread the two modules and the two node records independently. The fixed-object clause is
rendered by the two object equivalences and `object_identity`; the functor is enriched and sends
marked arrows to marked arrows. Ambient and marked mapping weak equivalences are separate fields.
The hammock mapping objects use the landed `ReducedHammock` path type, with endpoint identities,
row restriction/repetition, identity-column and like-direction reduction, and concatenation
reduction. The comparison map is a simplicial-set map and its representativewise `reduction`
field states that it is obtained by applying the functor and reducing. The theorem conclusion
quantifies over every pair of objects and asks exactly for a weak homotopy equivalence. I found
no mismatch in the Lean rendering or in the dependency records; the first dry run's record-shape
issues (ancestor/via, search-kind coverage, signature delimiters, and this section) were repaired.

## Superseded preliminary second reading by Q100

I opened the item node, its `def-coef-simplicial-hammock-pair` dependency, the two delivered
modules, and the source place (Dwyer--Kan, *Calculating simplicial localizations*, Lemma 2.4,
Definitions 2.1 and 5.1). The statement list and Lean rendering are:

* The small fixed object set is `C.O : Type u`, with `C.objectA`, `C.objectB` and
  `C.object_identity`; these provide the two object identifications and the assertion that `S`
  fixes objects under them.
* The simplicial categories are `C.A` and `C.B`; their marked wide simplicial subcategories are
  `C.U` and `C.V`. `marked`, `multiplicative`, and `wide` record the marked arrows, closure, and
  mapping subcomplexes. No saturation or two-out-of-three assumption is present.
* `C.S : C.A ⟶ C.B` is the simplicial functor, `C.sends_marked` preserves marked arrows, and
  `C.mapping_weak_equivalence` gives the ambient mapping-space weak equivalences for every pair.
* `C.marked_map` gives the marked mapping map and `C.marked_mapping_weak_equivalence` gives its
  weak equivalence. The repaired `C.marked_map_commutes` forces this map to be the restriction
  induced by `S` (the square with both subcomplex inclusions commutes), as required by the node.
* `C.hammockA` and `C.hammockB` are the diagonal hammock mapping objects. Their `simplices`
  fields identify each degree with the canonical `ReducedHammock`; `row_operators` gives row
  deletion/repetition followed by reduction; `composition` gives concatenation followed by
  reduction. `ReducedHammock` includes the empty path, so the length-zero case is present.
* `C.comparison` is the mapping simplicial-set map and `C.reduction` records representativewise
  application of `S` followed by canonical reduction. The conclusion is exactly
  `∀ x y, SSet.Enhanced.IsWeakHomotopyEquivalence (C.comparison x y)`.

Edge cases checked: `O` may be empty; `x = y` admits `Quiver.Path.nil`; degree `n = 0` has one
row; identity columns are removed; adjacent like-directed columns compose; leftward columns are
marked; and no freeness, cofibrancy, saturation, characteristic, or finiteness hypothesis is
introduced. Universes are uniform at `u`, matching `CoherentNerve.SCat.{u}` and `SSet.{u}`.

I repeated the existing-definition searches with LeanFinder, Loogle, LeanSearch, and `rg` over
Mathlib, `WeilConjectures`, and `lean/Sheaf`. They found no Dwyer--Kan reduced hammock pair or
homotopy-invariance theorem; the landed `ReducedHammock`, `HammockReduces`, and `hammockRows`
declarations are the canonical primitives and are reused.

The mismatch found was that the original `marked_map` field was an arbitrary map between the
marked subcomplexes, with no relation to `S`; consequently the Lean hypothesis did not state the
node's functor-induced marked mapping map. I added `marked_map_commutes`, the commutative square
with the two subcomplex inclusions, which uniquely forces the required restriction. No other
field or clause was changed. Both modules compile cleanly with `scompile.py`; only the theorem's
intentional `sorry` remains.

## Second reading by Q100

This is the completed independent second reading. It supersedes the preliminary reading above
and repairs the packet initially pushed at `9bf7c0ae4e`. The worker report is preserved as the
historical first draft; its claims about ordinary marked arrows, diagonal operators, and the
comparison reduction did not survive this reading.

Source checked directly: Dwyer--Kan, *Calculating simplicial localizations*, Sections 1.2 and
2.1, Lemma 2.4, Remark 2.5 (printed pp.18--20), Definition 5.1 and Section 5.6 (p.24).
Section 1.2 fixes an arbitrary small object set and defines weak equivalences mappingwise;
Lemma 2.4 assumes only weak equivalence of the ambient and restricted simplicial functors.
There is no cofibrancy, freeness, saturation, or two-out-of-three assumption. The source is the
PDF URL recorded in the node; there is no Stacks source for this result.

The node's complete statement list, matched against the repaired Lean:

* Small fixed object set `O`: `C.O : Type u`, `C.objectA : O ≃ A`,
  `C.objectB : O ≃ B`, and `C.object_identity` express fixed objects under the two displayed
  identifications. Verdict: exact, including the empty object set.
* Small simplicial categories `A,B`: `C.A,C.B : CoherentNerve.SCat.{u}`. I opened
  `CoherentNerveInfrastructure`: this is Mathlib's `EnrichedCat` over `SSet.{u}`, with enriched
  functors as morphisms, rather than an ordinary category or a locally Kan special case.
  Verdict: exact.
* Wide simplicial subcategories `U,V`: `WideSimplicialSubcategory.wide` is a family of
  `SSet.Subcomplex` values. `identities` and `composition` assert closure under the evaluated
  enriched operations in EVERY simplicial degree. `U.degree n` is exactly membership in those
  subcomplexes, and its multiplicative instance uses those closure fields. Verdict: exact;
  the old unrelated ordinary morphism property was removed.
* Functor `S` fixes objects and sends `U` to `V`: `C.S`, `C.object_identity`, and
  `C.sends_marked`. The latter quantifies over ALL degree categories. Verdict: exact.
* Both families of mapping weak equivalences for EVERY endpoint pair:
  `C.mapping_weak_equivalence` on `S.map x y` and `C.marked_mapping_weak_equivalence` on
  `C.marked_map x y`. `C.marked_map_commutes` gives the square with the two subcomplex
  inclusions, so the marked map is uniquely the restriction of the given `S`, not an arbitrary
  map between the same mapping spaces. Verdict: exact.
* Ordinary reduced width-k grids: `ReducedHammock (U.degree n) x y k` from the landed
  `HammockInfinityLocalization`. I opened `HammockChain`, `HammockStep`, `hammockEndpoint`,
  `HammockReduction`, `HammockReduces`, and `ReducedHammock`: chains give downward marked
  verticals, natural transformations give commutative squares, endpoint chains are constant,
  backward steps are marked, and irreducibility excludes identity columns and equal-direction
  neighbors. `Quiver.Path.nil` supplies length zero. Verdict: exact and reused, not duplicated.
* Diagonal formula `diag H(A,U)(x,y)_n = H(A_n,U_n)(x,y)_n`:
  `SimplicialHammockDegree A n` transports the enrichment along evaluation at n, and its
  category is Mathlib's `categoryOfEnrichedCategoryType`. Thus its arrows are literally
  `(CoherentNerve.hom A x y).obj n`. `SimplicialHammockPair.simplices` identifies the
  enrichment's n-simplices with width-n reduced grids in this degree-n category. Verdict:
  exact; the former identification with grids in the underlying ordinary category was wrong.
* BOTH simplicial operators applied together: `row_operators` first uses
  `simplicialHammockDegreeOperator A a.op` through the existing `hammockMapPath`, then uses
  `hammockRows` on the same ordinal map, and requires actual `HammockReduces` to the image
  simplex. Subcomplex closure supplies preservation of marked arrows. Verdict: exact.
* Identity and concatenation/reduction composition: `enrichment` carries the genuine
  associative unital simplicial composition. `identities` pins it to the empty path;
  `composition` pins the ACTUAL enriched composite to concatenation followed by reduction.
  Verdict: exact; the old existential composite did not specify a composition operation.
* Comparison applies `S_n` to every arrow and reduces: `C.reduction` now asserts
  `HammockReduces (hammockMapPath ... (simplicialHammockDegreeFunctor S n) ... p) q`,
  where `q` is the representative of the actual `C.comparison` image. I opened
  `hammockMapColumns` and `hammockMapPath`: they apply the ordinary marked functor to all
  objects, verticals, and horizontal arrows and transport the constant endpoints. Verdict:
  exact; the former `∃ t, HEq (comparison.app _ s) t` was tautological and supplied no formula.
* Conclusion: `∀ x y : CoherentNerve.underlying C.A,
  SSet.Enhanced.IsWeakHomotopyEquivalence (C.comparison x y)`. The underlying-category
  synonym has the same object type as `C.A`; there is no omitted endpoint pair. Verdict:
  exactly mappingwise weak homotopy equivalence of the induced diagonal comparison.

Edge cases: no `Nonempty O` or inhabited endpoint type is imposed; empty categories are
included. Equal endpoints include the empty path, with the enriched identity pinned to it.
At n = 0 the degree category uses vertices of the original mapping sets and grids have one
row. Faces that make a column an identity or bring equal-direction columns together explicitly
reduce afterward. The marked subcomplex may contain only identities; no invertibility or
saturation condition is imposed. All objects, mapping simplices, and degree categories are
small at the same arbitrary universe u, with no fixed universe or characteristic restriction.
The constant simplicial-category case recovers ordinary hammocks, including actual arrows.

I reviewed the NEW definition node against the source as well. Its draft statement omitted
that the construction is the diagonal. It now states the evaluated categories, wide mapping
subcomplexes with closure, the diagonal formula, both operators, actual enriched identity and
composition, and the functor-induced comparison. Its source now includes Remark 2.5. It cites
the existing coherent-nerve and ordinary-hammock nodes; there is no new independent theorem,
extra assumption, or choice from an existence axiom. All data definitions are real Mathlib
constructions; the degree functors use existing enriched functor laws and naturality for their
structure proofs. The only postponed theorem is this item's theorem, whose docstring now
records all five proof steps and their DAG dependencies. No dependency node/module was altered.
The three proof-dependency nodes currently have no recorded Lean modules, so there is no
available proof-dependency import to add. The main node's mathematical statement is unchanged;
no statement_change or citer audit is needed.

Independent searches actually run in this reading:

* LeanFinder: "Evaluation at a simplex makes a simplicial enriched category an ordinary
  category with n-simplices as morphisms" returned generic simplicial categories and
  `SimplicialCategory.homEquiv'`; no degree-category/hammock-pair construction.
* Loogle: `"EnrichedCategory", "TransportEnrichment"` found
  `instEnrichedCategoryTransportEnrichment`, which is reused. The ordinary-enriched-category
  equivalence is about a preexisting ordinary category and does not give the diagonal here.
* LeanFinder: "Wide simplicial subcategories defined by mapping subcomplexes closed under
  enriched identity and composition" found `SSet.Subcomplex`, `SimplicialCategory`, and
  thickening declarations. The mapping subcomplex is reused; no closed-family interface exists.
* LeanSearch: "Dwyer Kan homotopy lemma diagonal hammock localization mapping spaces" found
  derived-category homotopy invariance and ordinary localizations, without this statement.
* `rg` with `SimplicialHammockDegree|WideSimplicialSubcategory|SimplicialHammockPair` and
  related closure words over Mathlib, upstream `WeilConjectures`, `lean/Sheaf`, and the DAG
  found no existing pair or theorem. Mathlib's `WideSubcategory` is ordinary. The existing
  `DkEnrichedPresentation` presents a chosen simplicial ordinary category; it is not evaluation
  of an arbitrary enriched category and is not duplicated. The ordinary primitives and
  `hammockMapPath` from `HammockInfinityLocalization` are reused directly.

Mismatches repaired: unrelated marked arrows and subcomplexes; missing enriched closure;
arbitrary marked map; use of the underlying ordinary category in place of A_n; omission of
the original simplicial operator from the diagonal; absence of actual unital associative
composition; tautological comparison formula; inaccurate new-node description; incomplete
proof docstring; and an undocumented instance. The theorem signature and main node statement
remain unchanged. Both delivered files compile with the required `scompile.py`, without errors
or warnings. The corrected signatures were checked verbatim against `lean.statement`.

## Maintainer review fix (2026-10-17)

The delivered `def-coef-simplicial-hammock-pair` listed `lem-coef-hammock-infinity-localization`
in `stmt_deps`. That closed a DAG cycle: item -> def-coef-simplicial-hammock-pair (stmt) ->
lem-coef-hammock-infinity-localization (stmt) -> lem-coef-dk-cofibrant-localization-comparison
(proof) -> item (proof). `tools/check_dag.py` refuses cycles introduced by a delivery. The fix
removes that statement dependency and writes the reduced-grid notion H(P,T) inline in the
definition node's statement, in the item's own words. The new node now cites only
`lem-coef-coherent-nerve-comparison`. The Lean modules are unchanged. They still reuse the
definitional primitives `ReducedHammock`, `HammockReduces`, `hammockRows`, and `hammockMapPath`
from `Sheaf.CategoryTheory.HammockInfinityLocalization`, and they do not use its theorem. The
landed `lem-coef-dk-cofibrant-localization-comparison` module uses the same primitives the same
way without citing that node.
