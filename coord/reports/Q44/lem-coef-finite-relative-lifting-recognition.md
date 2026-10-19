## Worker report

Module: `Sheaf.AlgebraicTopology.FiniteRelativeLiftingRecognition`.
Main declaration: `SSet.Marked.Over.finite_relative_lifting_recognition`.
The only postponed theorem is this main declaration; its proof is `sorry` and its
source/proof docstring gives all five steps of the node. Two helper definitions
construct the node's own specified relative tests; neither has postponed data.
No node statement, dependency record or dependency list was changed.

Hypotheses and clauses, in node order:

- Small marked simplicial sets, maps, horns and the finite detector are the existing
  `SSet.Marked`, `flatMap`, `finalMarkedHorn`, `triangleMarkingMap`,
  `markedEquivalenceDetector`, and `flatToMarked`. The marked category already requires
  all degenerate edges marked. There is no second marking construction.
- Any small simplicial base is the explicit binder `(S : SSet.{u})`, with explicit
  universe `u`. The total marked map is `(X : SSet.Marked.Over S)`, the existing
  abbreviation for `CategoryTheory.Over (sharp S)`. Thus its underlying marked set is
  `X.left` and its marked map to the sharp base is `X.hom`.
- The family's definition is `finiteRelativeGenerators S`. Its first supremum uses
  `0 < i.val` and `i.val < n`, hence exactly the inner horns of type (i). The index
  `b : Δ[n] ⟶ S` includes every codomain base map. The second supremum uses
  `finalMarkedHorn n` in dimension `n + 1`, including the important dimension-one
  case. Again every `b : Δ[n + 1] ⟶ S` is included. The third summand is exactly
  `triangleMarkingMap`, with every `b : Δ[2] ⟶ S`.
- The fourth summand is the actual `flatToMarked markedEquivalenceDetector`, indexed
  by every `s : S _⦋0⦌`, with codomain base map `SSet.const s`. The helper
  `finiteTestOver` assigns its domain the composite map. Since the detector map is
  underlying identity, both of these base maps are constant at that same vertex.
  No arbitrary-base detector or Kan-complex family (iv) was included.
- Condition (a) is `(finiteRelativeGenerators S).rlp (toBase X)`. Mathlib's `rlp`
  quantifies over every generator and all commutative lifting squares. These are in
  the slice category over `sharp S`, so every diagonal is marked and over `S`.
  `toBase X` is the existing map to the terminal slice object, with left map `X.hom`.
- Condition (b) is the existing `IsNaturallyFibrant false X`. Unfolding gives
  `relativeFibration false X.hom.val` and, for every edge, membership in `X.left.marking`
  iff `IsDistinguishedEdge false X.hom.val e`. The latter reduces to the recorded
  final-horn Cartesian predicate `Enhanced.IsCartesianEdge`. `relativeFibration false`
  is inner fibrancy and Cartesian edge lifts with prescribed target over every base
  edge, for arbitrary simplicial sets. It does not require quasicategories.
- The outer `↔` is precisely the equivalence (a) iff (b). There are no quasicategory,
  model-category, fibrancy-of-base, nonempty or dimension hypotheses.

Dependency declarations read and reused:

- `Sheaf.AlgebraicTopology.MarkedAnodyneLiftingCalculus`:
  `SSet.Marked.flatToMarked`, `finalMarkedHorn`, `triangleMarkingMap`,
  `markedEquivalenceDetector`, and `marked_anodyne_lifting_calculus`; the existing
  category, minimal/full markings and horn inclusions are available through it.
- `Sheaf.AlgebraicTopology.RelativeMarkedAnodyneCalculus`:
  `SSet.Marked.Over.relative_marked_anodyne_calculus`; its imported
  `Sheaf.CategoryTheory.MarkedRelativeCartesianModel` supplies the exact existing
  `Over`, `relativeFibration`, `IsDistinguishedEdge`, `IsNaturallyFibrant`, and
  `toBase` used here. The full signatures and their docstrings were read.
- Proof imports: `Sheaf.AlgebraicTopology.FiniteMarkedFibrancyCriterion`
  (`SSet.Marked.finite_marked_fibrancy_criterion`) and
  `Sheaf.AlgebraicTopology.MarkedTriangleCancellation`
  (`SSet.Marked.marked_triangle_cancellation`). These are ordinary, non-public imports.
- Mathlib `CategoryTheory.MorphismProperty.ofHoms` and `rlp`,
  `CategoryTheory.Over.mk`/`homMk`, and `SSet.const` implement the relative family
  and lifting quantifiers directly.

Edge-case checks (mathematical statement checks, not new Lean theorems):

- Empty base forces the total set empty. There are no codomain maps for the first
  three families and no vertices for the detector. Both conditions are vacuous;
  neither binder excludes this case.
- Empty total space over an arbitrary base is allowed: the nonempty test domains
  have no top map, and the prescribed-target lift condition has no targets.
- Over the point, all base maps are constant, so the family is exactly the finite
  point criterion; condition (b) says quasicategory with equivalences marked.
- In dimension one, `finalMarkedHorn 0` includes the final vertex and marks the
  lifted edge. Omitting it would lose prescribed-target Cartesian lifts; it is present.
- For the identity over `Δ[1]`, the full marking satisfies both conditions; the flat
  marking fails the dimension-one lift for the nondegenerate base edge. Thus the
  theorem does not accept an underspecified natural marking.
- Identity over any simplicial base, including a non-quasicategory, has all edges
  Cartesian and satisfies the tests with the full marking. No quasi hypothesis is
  introduced by using `relativeFibration` instead of the quasi-only API.
- The inner-horn inequalities exclude invalid dimensions automatically; the final
  horn family starts at dimension one. Every object and base map retains universe `u`.

Searches for an existing declaration (2026-10-17; wrapper logs in searches.jsonl):

- `msearch.py ... leanfinder "Finite relative marked horn lifting and equivalence
  detectors recognize cartesian fibrations with precisely cartesian edges marked"`:
  eight hits, on unmarked Kan fibrations, quasicategories/Segal conditions and ordinary
  fibered categories. No matching marked relative theorem.
- `msearch.py ... loogle "SSet.Marked, HasLiftingProperty"`: zero hits, unknown
  identifier `SSet.Marked`. This service has no matching marked namespace indexed.
- `msearch.py ... grep
  "finiteRelative|finite_relative|relative.*lifting.*recognition|CartesianFibration"
  AlgebraicTopology`: zero Mathlib hits.
- `msearch.py ... leansearch "Finite marked horn lifting tests over an arbitrary
  simplicial base recognize cartesian fibrations with exactly cartesian edges marked"`:
  eight hits, ordinary Cartesian functors and unmarked Kan fibration results only.
- `rg` with the finite-relative/recognition regex and the item id in the upstream
  `WeilConjectures` tree and side `lean/Sheaf`: no exact declaration. Literal
  `grep -rn` for the item id upstream also found none. The proposed declaration and
  helper names were searched in `dag/lean_names_upstream.json`, both source trees,
  and side Lean; no collision. Inspection of the marked modules found reusable
  underlying generators and the arbitrary-base predicate, but no relative finite family.

Source verification: HTT Proposition the project server(1), printed pp.158–159, opened at
https://people.math.harvard.edu/~lurie/papers/HTT.pdf (the IAS URL timed out).
The source uses arbitrary base maps on types (1)–(3), constant detector maps indexed
by vertices, and identifies the output's marking with Cartesian edges. The Lean
family follows that distinction exactly. No statement fault or dispute found.

Validation: prescribed `scompile.py Q44 lem-coef-finite-relative-lifting-recognition`
compiled both sandbox and library views cleanly (1.6 s and 1.9 s), with no errors
or warnings. Delivery dry run result is recorded below when complete.

Dry run: `deliver2.py Q44 lem-coef-finite-relative-lifting-recognition --no-push`
printed `OK (dry run): commit 9e40030f26 compiles and passes the preflight except
for the second reading, which the second reader writes; nothing pushed.`
The independent second reading remains for the assigned second reader.

## Second reading by Q44

Independent second reading, 2026-10-17. I opened the repository node, sandbox node,
Lean module, both statement-dependency nodes and their recorded declarations, and
the actual definitions those declarations export. The statement agrees with the
node clause by clause. No statement correction, new node or dependency repair is
needed; the Lean and node records are unchanged by this reading.

Source check: I independently opened Lurie's HTT at
https://people.math.harvard.edu/~lurie/papers/HTT.pdf, Proposition the project server, proof
of (1), printed pp.158-159 (PDF pages 175-176, zero-based). The source starts
with an arbitrary simplicial set S. It uses types (1)-(3) over S and the finite
marked detector at each vertex with constant base maps. Its recognition argument
establishes inner fibrancy, marked Cartesian lifts with specified target, and
then equality of the marking with the Cartesian edges. Remark the project server gives
the converse lifting property for the natural marking. There is no ambient
quasicategory or relative model structure hypothesis to add. This source is HTT,
not a Stacks result; the node explicitly records that no Stacks tag states it.

My object/hypothesis/conclusion checklist, with its Lean rendering and verdict:

1. Small marked simplicial sets, preserving maps, and the specified four finite
   test shapes: `SSet.Marked`, `flatMap (horn n i).ι`, `finalMarkedHorn n`,
   `triangleMarkingMap`, and `flatToMarked markedEquivalenceDetector` are the
   existing declarations from `MarkedAnodyneLiftingCalculus` and its imports.
   I read their definitions: minimal markings contain degeneracies; the final
   simplex marks just degeneracies and its final edge; the triangle source marks
   exactly the two consecutive edges and degeneracies; the detector is the
   coequalizer imposing the two face/degeneracy equations, with just the specified
   additional edge marked. Verdict: the node's objects, not substitutes.
2. Any small base S: `(S : SSet.{u})`, with `universe u` explicitly bound.
   No hypothesis or typeclass on S occurs. Verdict: exact.
3. Any small marked map p:(X,M) -> S-sharp: `(X : Over S)`, where the imported
   abbreviation is `CategoryTheory.Over (sharp S)`. Thus X.left is the marked
   total space, X.left.marking is M, and X.hom is p; the sharp base imposes no
   condition on the image of marked edges. Verdict: exact, without a hidden
   quasicategory instance.
4. J_S, first three families with every codomain map to S:
   `finiteRelativeGenerators S` takes a supremum over n, i and the inequalities
   `0 < i.val`, `i.val < n` for inner horns, followed by all `finalMarkedHorn n`
   and `triangleMarkingMap`. Each `ofHoms` is indexed by *every* simplicial map
   from the appropriate standard simplex to S. `finiteTestOver i b` equips the
   source with the composite i followed by b and the target with b. Its actual
   arrow is `CategoryTheory.Over.homMk i rfl`, so it retains the specified base
   map. Verdict: exactly types (i)-(iii), with the correct quantifier order.
5. J_S, detector only at each vertex s: the last `ofHoms` is indexed by
   `s : S _⦋0⦌` and uses `SSet.const s`. Since `flatToMarked` has underlying
   identity, the composite source map is constant at that same s. There is no
   unrestricted detector base map and no family (iv). Verdict: exact.
6. Condition (a), every commuting square has a marked diagonal over S:
   `(finiteRelativeGenerators S).rlp (toBase X)`. I read Mathlib's `rlp`: it
   quantifies over every left arrow in the morphism property and asserts
   `HasLiftingProperty`. All these arrows are in the same marked slice.
   `toBase X` has left arrow X.hom and target the identity of sharp S; a lower
   arrow into this terminal slice object is uniquely the test's base map.
   Hence a slice lifting square is exactly the node's lifting square for p,
   and its diagonal is marked and over S. Verdict: exact, not merely an
   unmarked or a base-forgetting lifting property.
7. Condition (b), underlying Cartesian fibration and M exactly Cartesian:
   `IsNaturallyFibrant false X` expands to `relativeFibration false X.hom.val`
   and `∀ e, e ∈ X.left.marking ↔ IsDistinguishedEdge false X.hom.val e`.
   I read the exported definitions in `MarkedRelativeCartesianModel`:
   `relativeFibration false` is `InnerFibration` and, for every target x and
   every base edge alpha with target p(x), an edge e with target x, image
   alpha, and the distinguished-edge property. With `false`, that property is
   `Enhanced.IsCartesianEdge` via Yoneda. I opened `InfinityFibrations` too:
   the latter is the final-horn condition in every dimension at least two,
   over the specified base simplex, with no quasicategory assumptions.
   Verdict: exactly both clauses of (b), for arbitrary bases.
8. Equivalence and exclusions: the theorem's outer `↔` is (a) iff (b).
   Its only object binders are S and X; neither the theorem nor the reused
   predicate assumes a model structure, nonemptiness, a finite base, or
   quasicategories of total space or base. Verdict: exact.

Dependency signatures checked independently: the recorded
`marked_anodyne_lifting_calculus` supplies the point lifting recognition and
marked-anodyne generator facts; `relative_marked_anodyne_calculus` supplies its
arbitrary-base lifting equivalence, existence of the natural marking, and
pullback marking equality. The latter publicly imports the actual slice and
arbitrary-base predicates used here, so these are available without importing
or assuming a model structure. I also read `finite_marked_fibrancy_criterion`
(the finite family over a point, not over arbitrary S) and
`marked_triangle_cancellation` (marking the remaining first edge of the
final two-horn) in the ordinary proof imports. Neither is an existing version
of the present theorem. There are no new definition nodes or dependency modules
in this delivery to audit under H12/H13.

Edge cases independently checked:

- Empty S: the existence of X -> S forces X empty. The generator index types
  of base maps and vertices are empty, so lifting and natural fibrancy are
  vacuous. No nonempty binder excludes this case.
- Empty X over any S: all generator domains are nonempty, so there are no top
  maps in lifting squares. The lift-existence predicate has no target x.
- S a point: the base maps are the unique constant maps and the statement
  specializes to the existing finite point criterion.
- Dimensions zero and one: inner horns occur only for 0 < i < n, hence start
  at n = 2. The final family is indexed as `finalMarkedHorn n` of dimension
  n+1; n=0 is the required {1} -> Delta[1] test, not omitted. It produces a
  lift with prescribed target, rather than prescribed source.
- Identity of Delta[1]: full marking satisfies the conditions; minimal marking
  fails the final one-dimensional test on the nondegenerate base edge. Identity
  over a non-quasicategory base is also covered, with all edges Cartesian.
- Universes: u is arbitrary, both S and X are small in it, as are all the test
  shapes and map index types. No extra universe equality or lower test universe
  restricts the node. No coefficient ring, characteristic, scheme or numerical
  parameter occurs here, so those unrelated edge cases do not apply.

Independent searches (2026-10-17; wrapper searches append to searches.jsonl):

- LeanFinder: "A marked simplicial set over S lifts finite inner horns final
  marked horns triangles and a constant equivalence detector iff it is naturally
  marked Cartesian". Eight hits: unmarked Kan generators, KanComplex,
  Quasicategory, strict Segal structures; no relative marked criterion.
- LeanSearch: "Finite marked simplicial lifting tests over arbitrary base
  recognize precisely Cartesian fibrations with Cartesian edges marked".
  Eight hits: ordinary category fiberedness and unmarked simplicial lifting;
  no marked criterion.
- Loogle: `SSet, Quasicategory` reported an unknown unqualified identifier
  `Quasicategory`; no usable match. The successful LeanFinder search above is
  the independent Loogle-or-LeanFinder search.
- `rg` on Mathlib/AlgebraicTopology, all upstream WeilConjectures, and the
  project's lean/Sheaf with `finiteRelative`, `finiteTestOver`, the theorem
  name, finite/lifting/cartesian variants, and relative/generator variants.
  No existing family or theorem matched. The same exact names and blueprint id
  were absent from dag/lean_names_upstream.json and upstream/project Lean.
  I opened the nearby `FiniteMarkedFibrancyCriterion` and
  `MarkedSaturationPerfectEquivalences`: they concern the point, not arbitrary
  S. `RelativeMarkedAnodyneCalculus` tests all marked-anodyne maps, not this
  finite family with the constant detector restriction. Thus none replaces
  this declaration. The helpers only assemble this node's tests using the
  existing marked objects and Mathlib's slice, not private replacement notions.

H5/H6/H8/H9 audit: both helper definitions contain actual data with no sorry;
only the main named theorem is postponed with `by sorry`. I compared its five
proof paragraphs to the five DAG proof steps: inner/final horns; the two fiber
identifications; comparison triangle and cancellation; converse types (i)-(iii);
and converse constant detector. All steps and their dependencies are present.
Every declaration and module docstring carries the source and blueprint id;
all lines fit 100 columns. The single universe and every object are explicitly
bound (`autoImplicit false`). A direct extraction confirms lean.statement is
verbatim the theorem signature; the node differs from the repository only in
its lean field. The two public imports serve the statement and the two ordinary
imports serve exactly the proof dependencies.

Mismatches and changes: none found in the statement, definitions, dependency use,
source interpretation or documentation. I preserved the correct Lean and node
and appended this independent review to the report. Required recompilation and
delivery validation are recorded below.

Second-reader validation: prescribed scompile.py compiled the only delivered module
in sandbox and library views cleanly (2.0 s and 1.9 s), with no errors or warnings.
The complete independent-review delivery then passed deliver2.py --no-push:
`OK (dry run): commit 89317c8f93 passes the preflight and compiles; nothing pushed`.
No Lean or node changes were needed after these checks.
