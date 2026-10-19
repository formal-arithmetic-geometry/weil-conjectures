## Worker report

The module `Sheaf.CategoryTheory.Localization.FixedHammockGraphHomotopyInvariance`
states `CategoryTheory.FixedHammockGraph.fixed_hammock_graph_homotopy_invariance`.
This is its only postponed theorem. All helper definitions, wrappers, restrictions,
and category instances have real data. No new DAG statement, dependency module,
or statement correction is included.

The conclusion presents the canonical bisimplicial diagrams by degreewise bijections
with their ordinary zigzag nerves and full operator equations. It asserts existence
of those presentations and of their comparison, with the comparison's full arrow
formula and the required diagonal weak equivalence. This is an explicit presentation
of the node's diagrams, not a hypothesis that such diagrams exist. Nothing is defined
by choosing one of these witnesses. Changing a presentation conjugates its operators
and comparison by the prescribed bijections; thus it gives the same rectangular
construction up to its unique presentation isomorphism. In particular the conclusion
does not substitute a map having merely the same endpoints or homotopy type.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Small common object set O | `{O : Type u}` |
| Simplicial categories A,B on O | `A B : EnrichedCategory SSet.{u} O`, using Mathlib's enriched identities, composition and axioms |
| Wide simplicial subcategories U,V | `U : Wide A`, `V : Wide B`; `Wide.hom` is a genuine mapping subcomplex, and `identities`/`composition` assert exactly closure under the two operations in every degree |
| Simplicial functor S | `EnrichedFunctor SSet (Objects A) (Objects B)`; `Objects` wraps the common carrier to keep the two enrichment instances distinct, with no change to any mapping simplicial set |
| S fixes objects | `hS : ∀ x : O, (S.obj ⟨x⟩).obj = x` |
| S sends U into V | `hUV` asserts membership in V for the image of every simplex in U, in every mapping set and degree |
| A(a,b) → B(a,b) weak equivalence for every pair | `hA`; `mappingMap` is exactly `S.map` with the endpoint transport forced by `hS` |
| U(a,b) → V(a,b) weak equivalence for every pair | `hU`; `markedMap` is the actual subtype restriction of `mappingMap`, using `hUV` |
| Finite word in + and −; all words permitted | `w : List Bool`; `word` sends true to `.forward` and false to `.backward` |
| Fixed endpoints x,y | `(x y : O)`; every grid uses the same endpoints |
| Ordinary category A_p | `Degree A p` with `degreeCategory`; homs are exactly `(A.Hom x y).obj p`, and identities/composites are evaluated enriched operations |
| U_p | `marked U p`, with multiplicativity from precisely the fields of `Wide` |
| q+1 rows, l horizontal columns, commuting rectangles | `Grid U w x y p q` is the q-simplex of the ordinary nerve of the recorded `RelativeZigzag.Diagram (marked U p) (word w) ⟨x⟩ ⟨y⟩`; its q+1 objects are rows and its q generating morphisms are vertical diagrams |
| Forward arrows unrestricted, backward arrows in U_p | The existing `RelativeZigzag.Horizontal` in `Diagram` imposes precisely these conditions for the two image letters |
| Vertical arrows down, in U_p, endpoint identities | The existing `RelativeZigzag.Hom` used by the nerve has components in `marked U p`, commuting squares, and its `left`/`right` identity-endpoint equations |
| Identity columns allowed; like-directed neighbors allowed; no reduction | `List Bool` has no alternation restriction; `Diagram` permits identity arrows; no quotient, deletion, composition of columns, or reduction predicate occurs |
| p direction applies simplicial operators | `Graph.operators` uses `(A.Hom x y).map a` in `GridImage`, on every horizontal and vertical arrow |
| q direction deletes/repeats rows, composing intervening vertical arrows | `b.unop.toOrderHom` selects rows; `GridImage` evaluates `s.map (homOfLE (r.monotone h))`, the vertical composite in the ordinary nerve, including identity composites |
| Bisimplicial identities and commutation of directions | `Graph.diagram` is a functor from the product simplex-op category, and its full action is fixed by `operators` |
| Empty word exists exactly for x=y | The dependency's empty `Diagram` is `ULift (PLift (⟨x⟩ = ⟨y⟩))`; its category has only the endpoint identity |
| Same construction for B,V | The second witness is `DB : Graph V w x y`, with the identical definitions |
| Comparison applies S to every arrow | The first conjunct in the conclusion uses `GridImage U V` with `mappingMap S hS` and the identity row map, in every bidegree |
| Weak equivalence on the actual diagonal | The second conjunct is `SSet.Enhanced.IsWeakHomotopyEquivalence (Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ) f)` |

`DiagramImage` fixes every vertex and every horizontal arrow. `GridImage` additionally
fixes every vertical component for all ordered pairs of rows, so together they determine
the map completely. `HEq` only expresses equality of arrows after the vertex equalities;
it does not discard an arrow equation. All universes and variables are explicitly bound.
One common universe contains the small object set and mapping sets; any two original
sizes fit by taking their maximum.

Dependencies read and used:

- `Sheaf.CategoryTheory.CoherentNerveComparison`,
  `CategoryTheory.coherent_nerve_comparison`, together with its public Mathlib
  `EnrichedCategory`/`EnrichedFunctor` simplicial-category convention and the public
  `SSet.Enhanced.IsWeakHomotopyEquivalence` from `EnhancedDiagramsCones`.
  The theorem here uses no Bergner fibrancy, cofibrancy, or equivalence-on-pi-zero hypothesis.
- `Sheaf.CategoryTheory.Localization.ZigzagHomotopyCalculus`,
  `CategoryTheory.RelativeZigzag.HasTwoSidedHomotopyCalculus` and its recorded helpers
  `Letter`, `Horizontal`, `Diagram`, `Vertex`, `objectAt`, `Hom`, `diagramCategory`.
  We use those ordinary categories and their Mathlib `nerve` directly; the calculus
  property itself is not assumed.
- Proof-only imports:
  `Sheaf.AlgebraicTopology.BisimplicialDiagonalEquivalence`,
  `SSet.bisimplicial_diagonal_equivalence`; and
  `Sheaf.AlgebraicTopology.KanQuillenRightProper`,
  `SSet.KanQuillen.right_proper_kan_quillen`.
- `lem-coef-two-sided-simplicial-grothendieck-invariance` has neither a Lean record
  nor a Mathlib match in the shared DAG. It is a proof dependency only; it is named
  in the full proof docstring and its import must be added when available.

Edge cases checked by reading the defining data: empty O makes endpoint instances
vacuous; the empty word is inhabited exactly for equal endpoints; a one-letter +
grid is the discrete nerve on A_p(x,y), and a one-letter − grid is the discrete
nerve on U_p(y,x). At q=0 there is one row, with no nontrivial vertical arrow.
Repeated rows use identity vertical composites. At p=0 all definitions still use
the same evaluated enriched operations. Empty mapping subcomplexes are allowed
between distinct objects; identity closure supplies all required diagonal identities.
Identity columns and repeated signs remain valid, including arbitrary word lengths.
There is no saturation, freeness, cofibrancy or two-out-of-three premise.

Source checked online: Dwyer–Kan, *Calculating simplicial localizations*, Definition
5.1 and Lemma 5.7, printed p.24, PDF p.8:
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-2.pdf .
Definition 5.1 identifies the fixed-type graph with the ordinary diagram-category
nerve; Lemma 5.7 gives the asserted diagonal comparison under the two local weak
-equivalence assumptions. The word here follows the dependency's left-to-right
convention, opposite to the printed order. No statement fault or dispute was found.

Searches, all via the prescribed `msearch.py Q05 <item>` unless noted:

- LeanFinder: “Weak equivalences on mapping simplicial sets and wide simplicial
  subcategories induce weak equivalences on fixed word zigzag diagram diagonal
  nerves”: 8 hits, consisting of `SimplicialNerve`, ordinary nerve, nerve adjunction
  and truncated homotopy-category declarations; no fixed-word comparison.
- LeanSearch: “Fixed word hammock graph weak equivalence of simplicial relative
  categories”: 8 hits on general `WeakEquivalence` wrappers and homotopy categories,
  none stating this comparison.
- Loogle: `"hammock"`: 0 hits.
- Mathlib grep: `hammock|[Ff]ixedWord|[Ss]implicialSubcategory`: 0 hits.
- `rg` over upstream `WeilConjectures` and shared `lean/Sheaf` for those expressions:
  the project contains reduced hammock localization and free-resolution comparisons,
  but no fixed-word bisimplicial comparison. Read the relevant definitions in
  `HammockInfinityLocalization.lean` and `DkCofibrantLocalizationComparison.lean`;
  they impose reduction and have different statements. They are not imported here.
- Upstream exact item-id search returned no hit. Shared DAG search for fixed-word
  graphs/wide simplicial subcategories found this node, its citers, and distinct
  reduced-hammock/Grothendieck nodes; no existing declaration supplies the statement.
- Read Mathlib `Enriched.Basic`, `Enriched.EnrichedCat`, `SimplicialCategory.Basic`,
  `SimplicialSet.Nerve`, `SimplicialSet.Monoidal`, and `ComposableArrows.Basic`.
  These supply the reused enrichment/nerve definitions, not this lemma.

Validation: `scompile.py Q05 lem-coef-fixed-hammock-graph-homotopy-invariance
lean/Sheaf/CategoryTheory/Localization/FixedHammockGraphHomotopyInvariance.lean`
passed both sandbox and library compilation with no errors or warnings (2.0 s and
2.3 s respectively). The theorem has the required `sorry` proof and a complete
six-step natural-language proof docstring. The node copy changes only `lean`.

## Earlier second reading (a previous round; superseded)

Pending the independent second worker. This worker has not claimed an independent reading.

## Second reading by Q05

Independent second reader, 2026-10-17. I opened the sandbox node and full module,
the two statement-dependency nodes and their source declarations, and the cited
Dwyer--Kan PDF. I read Definition 5.1 and Lemma 5.7 on printed p.24 (PDF p.8),
the size and local weak-equivalence conventions in 1.2, and Example 10.3 and
Propositions 10.4--10.5 on printed p.34. The source is
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-2.pdf .
There is no Stacks source for this item. Its source assumes a fixed arbitrary
object set and object-preserving simplicial functors; it does not assume Kan
mapping spaces, cofibrancy, saturation, or a calculus of fractions.

My object/hypothesis/conclusion checklist, in node order:

| Node item | Lean rendering and second-reader verdict |
| --- | --- |
| Small common object set O | `{O : Type u}`. Correct; no nonemptiness or finiteness instance. |
| Simplicial categories A and B on O | `(A B : EnrichedCategory SSet.{u} O)`. Correct: Mathlib's `Hom`, `id`, `comp`, and the enriched category laws give precisely the source's structure. |
| Wide simplicial subcategories U and V | `(U : Wide A) (V : Wide B)`. Correct: `hom` is a simplicial subcomplex on every pair, with degreewise identity and composition closure. It imposes no fullness or equivalence closure. |
| Simplicial functor S | `EnrichedFunctor SSet (Objects A) (Objects B)`. Correct: `objectsEnrichment` retains exactly each given enriched mapping object and its operations; the wrappers distinguish the two instances. Mathlib's `map_id` and `map_comp` are the required functor axioms. |
| S fixes objects | `hS : ∀ x, (S.obj ⟨x⟩).obj = x`. Correct. `mappingMap` is `S.map` followed by the equality transport forced by hS. |
| S sends U into V | `hUV`, for every pair and every simplex degree. Correct; `markedMap` is the actual subtype restriction, with naturality inherited from `mappingMap`. |
| Ambient mapping weak equivalences | `hA : ∀ x y, ... (mappingMap S hS x y)`. Correct. |
| Marked mapping weak equivalences | `hU : ∀ x y, ... (markedMap U V S hS hUV x y)`. Correct. The reused `SSet.Enhanced.IsWeakHomotopyEquivalence` tests realization path components and all positive based homotopy groups, as required. |
| Every finite sign word and every pair of endpoints | `(w : List Bool) (x y : O)`. Correct: true maps to `.forward`, false to `.backward`, and there is no alternation or positive-length condition. |
| The ordinary category A_p | `Degree A p` with `degreeCategory`. Correct: homs and the two operations are the corresponding degree evaluations of A. Its category-law proofs are structural, not new postponed results. |
| Rows and horizontal columns | `Grid U w x y p q` is the existing ordinary nerve of `RelativeZigzag.Diagram (marked U p) (word w) ⟨x⟩ ⟨y⟩`. Correct: a nerve q-simplex is a functor on `Fin (q.unop.len + 1)`, hence exactly q+1 rows. The recursive Diagram has one arrow per letter. |
| Forward arrows arbitrary, backward arrows in U_p | The dependency's `Horizontal` uses the ambient hom for `.forward` and the marked reverse hom subtype for `.backward`. Correct. No `.weakForward` is produced by `word`. |
| Downward marked vertical arrows and commuting squares | The dependency's `Hom.app`, `Hom.mem`, and `Hom.commutes`. Correct; I read `Square` for both directions and its recursive use in `Commutes`. |
| Identity endpoint vertical arrows | The dependency's `Hom.left` and `Hom.right`, with `endpoints` transports. Correct; these require actual endpoint identities, not merely marked endpoint maps. |
| Identity columns and adjacent equal directions permitted | `Diagram` has no reduction predicate, quotient, deletion or alternation test. Correct. |
| p-direction simplicial operators | `Graph.operators` uses `(A.Hom x y).map a` on every arrow via `GridImage`. Correct; the subcomplex closure retains the marked arrows. |
| q-direction deletion/repetition and vertical composition | `b.unop.toOrderHom` chooses the rows, and `s.map (homOfLE (r.monotone h))` chooses the intervening composite. Correct, including identities when two selected rows coincide. |
| Bisimplicial laws and commuting directions | `Graph.diagram` is a functor from the product of the two opposite simplex categories; `operators` specifies all its maps. Correct. |
| Empty word only for equal endpoints | The dependency's empty Diagram is `ULift (PLift (x = y))`; endpoint identities give the unique morphism when inhabited. Correct. |
| The same construction for (B,V) | `DB : Graph V w x y`, using the same definitions. Correct. |
| The comparison applies S to every arrow | The conclusion's universal `GridImage U V ... (OrderHom.id)` equation. Correct: it fixes every row vertex, every horizontal arrow recursively, and every vertical component for each ordered row pair. `HEq` expresses the necessary endpoint transport and does not omit any component. |
| Weak homotopy equivalence of the actual diagonals | `IsWeakHomotopyEquivalence (Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ) f)`. Correct: both simplex degrees become the same degree, and f is the fully characterized comparison above. |

The existential presentations in the conclusion are not extra hypotheses. Each
`Graph.simplices` is a bijection onto the full ordinary zigzag nerve, and the
operator equations fix its entire bisimplicial action. Two such presentations
are conjugate by those bijections, so the existence assertion states the
specified construction and its specified map up to its uniquely determined
presentation isomorphism. It cannot be satisfied by omitting rectangles or by
choosing an unrelated weak equivalence. No definition selects data from the
postponed theorem. All helper data are explicit; its only `sorry` is the theorem
for this DAG node. I found no additional mathematical premise in the signature.

Dependency audit: I read `RelativeZigzag.Letter`, `Horizontal`, `Square`,
`Diagram`, `Vertex`, `objectAt`, `endpoints`, `Vertical`, `Commutes`, `Hom`,
and `diagramCategory` in the recorded ZigzagHomotopyCalculus module, rather
than inferring their meanings from their names. I also read the recorded
CoherentNerveComparison module's enrichment and weak-equivalence conventions,
Mathlib Enriched.Basic's actual EnrichedCategory/EnrichedFunctor fields, and
Mathlib SimplicialSet.Nerve's definition and face/degeneracy formulas. The
calculus-of-fractions property and Bergner model hypotheses are not assumed
here. The two recorded proof-only modules are imported; the Grothendieck
proof dependency still has no Lean record in the shared DAG. No new node,
dependency module, or statement correction occurs, so no citer audit is needed.
No repair note exists for this item in coord/repair-notes.

Edge cases: empty O gives no endpoints and is covered vacuously; an empty word
and unequal endpoints give empty grids in every degree, while equal endpoints
give a point. The words [+] and [-] give the discrete degreewise nerves of
A(x,y) and U(y,x), respectively, so both local assumptions have their precise
base cases. At q=0 there is one row; at p=0 the same enrichment evaluation
applies. Empty off-diagonal mapping subcomplexes, repeated rows, identity
columns, and arbitrary runs of equal signs are allowed. Identity closure
provides only the required diagonal simplices. There is no numerical,
characteristic, ring, scheme, or zero-object parameter to restrict. The one
size u is the common sufficiently large universe used by the dependency's
small-category convention; finite diagrams stay in it. No extra universe
equality between independently supplied parameters is introduced, and every
variable and universe is explicitly bound (`autoImplicit false`).

Independent searches using different queries from the worker, through the
prescribed `msearch.py Q05 lem-coef-fixed-hammock-graph-homotopy-invariance`:

- LeanFinder: "Local weak equivalences of enriched categories preserve nerves
  of rectangular marked zigzag diagrams of prescribed shape". Eight results:
  ordinary nerve Segal, nerve-edge, and truncated nerve declarations; no match.
- LeanSearch: "The map on classifying spaces of fixed shape marked diagram
  categories is a weak homotopy equivalence for objectwise locally weakly
  equivalent simplicial categories". Eight results on generic weak equivalences
  and limits under category equivalences; no match.
- Loogle: `"SimplicialObject", "nerve"`. Twelve Cech nerve/conerve declarations;
  none is the fixed-word relative diagram construction or comparison.
- Grep: `zigzag|WideSubcategory|SimplicialSubcategory`. Twenty-five results on
  ordinary wide subcategories and connected-category zigzags. I opened Mathlib
  CategoryTheory.Widesubcategory: its ordinary `WideSubcategory` assumes an
  ordinary category and a multiplicative morphism property; it does not give
  simplicial mapping subcomplexes for an enriched category, so `Wide` is not a
  duplicate of that structure.
- Independent rg of upstream WeilConjectures and shared lean/Sheaf for hammock,
  fixed word/type, wide simplicial/enriched, and simplicial subcategory terms,
  plus DAG and upstream-name searches. I opened the reduced hammock structures
  in HammockInfinityLocalization and compared their quotient/reduction and
  simplicial-localization purpose. Those and the free-resolution comparison
  are distinct. The reusable ordinary fixed-word Diagram is used directly.
  No existing theorem or existing enriched wide-subcategory definition matched.

Docstrings and record: every declaration names its source and this blueprint id.
The theorem docstring follows all six node proof steps: products and coproducts,
rectangular nerve and base cases, endpoint variances, four Grothendieck joins,
simultaneous induction, and identification of S on every arrow. I checked the
four variances and joins against the source's reversed printed word convention.
The node differs from the shared base only in `lean`; its `lean.statement` is
verbatim the theorem signature. No hypothesis, conclusion, definition, or
source correction was needed. I left the correct Lean and node unchanged and
added this independent reading to the report.

Validation: the required scompile.py invocation compiled the delivered file
both as a sandbox module and at its intended library path, cleanly, in 1.6 s
and 1.7 s respectively. No errors or warnings. The dry-run and delivery results
are recorded below after their execution.

Delivery validation: `deliver2.py Q05
lem-coef-fixed-hammock-graph-homotopy-invariance --no-push` printed
`OK (dry run): commit 3360f61512 passes the preflight and compiles; nothing pushed`.

## Maintainer review fix (2026-10-17)

H4 repair by the maintainer's reviewer; the mathematics of the delivery is unchanged.
`def-coef-simplicial-hammock-pair` landed on newtargets-dag at 2026-10-16 20:06 UTC,
six minutes before this delivery, as `Sheaf.CategoryTheory.SimplicialHammockPair`.
It carries the same notions that the delivery defined privately: simplicial categories
(`CoherentNerve.SCat`), wide simplicial subcategories (`WideSimplicialSubcategory`),
the degree categories `A_p` (`SimplicialHammockDegree`), their marked arrows
(`WideSimplicialSubcategory.degree`), and the degreewise functors of `S` and of the
simplicial operators (`simplicialHammockDegreeFunctor`, `simplicialHammockDegreeOperator`).
The citer `lem-coef-hammock-pair-homotopy-invariance` is stated on these declarations.
The fixed module drops `Degree`, `degreeCategory`, `Wide`, `marked`,
`markedMultiplicative`, `Objects`, `objectsEnrichment` and `mappingMap`, and states the
theorem on the landed declarations. Object fixing uses the landed
`SimplicialHammockComparison` convention: `O ≃ A`, `O ≃ B`, and
`S.obj (objectA o) = objectB o`. `markedMap` is still the actual subtype restriction
of `S.map`. `GridImage` now takes the functor of degree categories that it applies
to every arrow. Every clause of the node and the edge-case analysis above still hold
verbatim. `nt_compile.py` compiles the fixed file cleanly, and `sorryAx` occurs only
in the theorem.
