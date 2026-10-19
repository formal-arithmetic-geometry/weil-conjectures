## Worker report

The module `lean/Sheaf/CategoryTheory/ArrowMorphismSquare.lean` states
`SSet.Enhanced.arrow_morphism_square`, with one `sorry`, and constructs its concrete
square, composition-span and relative path models. The node copy changes only `lean`.
All auxiliary declarations belong to this arrow-square construction; no other DAG
statement is restated and no definition selects unconstrained data.

Sources read: Kerodon Theorem the project server (06BZ), whose displayed square is a pullback in
`Fun(Arr(D)^op × Arr(D), Spaces)` after specializing both input functors to the identity;
and Kerodon Subsection 4.6.8 (01PF), especially Notation the project server, Corollary the project server,
Construction the project server and the unitality/associativity discussion. The node's seven-step
triangulation proof is reproduced in the theorem docstring. The comparison's two
triangle coordinates and constant diagonal path are specified, rather than supplied
as arbitrary weak equivalences. The universal-family formulation is a presentation
of the coherent naturality clause, not a hypothesis on the quasicategory.

Hypotheses and clauses, in order:

* The arbitrary quasicategory is `D : SSet.{u}` with `[Quasicategory D]`. The theorem
  binds `u` explicitly and uses the recorded `SSet.Enhanced` conventions throughout.
  There is no nonemptiness, small-cardinality or strict-category restriction.
* `Arr(D)` is the existing internal hom `(ihom Δ[1]).obj D`. Its quasicategory
  instance is the imported Mathlib internal-hom instance. The arbitrary arrows `u,v`
  are its zero-simplices. They are not assumed to be equivalences.
* Their source and target vertices are the two recorded `evaluation Δ[1] D` maps
  applied to `u,v`. Thus all four vertices in the node are explicit in the span
  structure, the cross term, and the endpoint formula.
* The point clause starts with the recorded right-pinched
  `mappingSpace ((ihom Δ[1]).obj D) u v`: the chosen family from
  `right_pinch_comparison` is the canonical pinch, uniquely determined by its prism
  formula after the monomorphic arrow inclusion. The isomorphism `i` to
  `arrowSquareFamily (const u) (const v)` is likewise constrained by its full square
  coordinate. Composing it with the canonical comparison is asserted to be a weak
  homotopy equivalence to the Kan path model. This states an equivalence of spaces,
  without demanding a strictly natural choice of inverse.
* `ArrowSquareCompositionSpan D u v true` resolves postcomposition by `v`. Its
  domain `arrowSquareLeg ... true` consists of triangles with edge 12 fixed at `v`
  and vertex 0 fixed at `d0`. Its `free` leg, specified to be edge 01, is a weak
  equivalence to `arrowMappingSpace D d0 e0`. Its `long` leg is specified to be
  edge 02 into `arrowMappingSpace D d0 e1`. Inverting the free leg gives `a ↦ va`.
* The `false` span resolves precomposition by `u`: edge 01 is fixed at `u`, vertex
  2 is fixed at `e1`, its weak-equivalence free leg is edge 12 into
  `arrowMappingSpace D d1 e1`, and its long leg is edge 02 into the same cross term.
  Inverting the free leg gives `b ↦ bu`. Both maps in each span are characterized
  by equality after the arrow-space inclusions. No unrelated map is a hypothesis.
* `ArrowSquareSpanPresentation D u v` identifies the path model with the literal
  iterated pullback
  `pullback (pullback.snd P.long (evaluation Δ[1] C 0) ≫ evaluation Δ[1] C 1) Q.long`,
  where `C` is the unpinched cross mapping space `arrowMappingSpace D d0 e1`.
  This is exactly the stipulated `P ×_{C,ev0} Fun(Δ[1],C) ×_{ev1,C} Q`.
  Its three equations retain both whole triangle coordinates and the whole path.
  Natural pinch comparisons on the three endpoint mapping spaces identify these
  composition spans with the right-pinched cospan in the node.
* The eight equations of `arrowSquarePathFamily` fix the upper triangle's edge and
  vertex, the lower triangle's edge and vertex, then require the path's source to
  be the upper long edge `va`, its target to be the lower long edge `bu`, and both
  endpoint families to be constant along that path. Operators act on every
  coordinate. Consequently the construction retains all higher simplices and does
  not replace compatibility paths by equality of homotopy classes.
* The joint projection is `arrowSquarePathEndpoints`: upper edge 01 and lower
  edge 12. The theorem's final equality identifies its composite with the
  right-pinched weak equivalence with the product of `mappingSpaceMap` of source
  and target evaluation, followed by their specified pinch inclusions. This is a
  single equation for the joint projection, stronger as a presentation than two
  unspecified pointwise identifications, with exactly the two requested factors.
* Naturality in both arrows is retained by `arrowSquareFamily U V` and
  `arrowSquarePathFamily U V` for every simplicial parameter `T` and the entire
  arrows `U,V : T ⟶ Arr(D)`. `ArrowSquareRelativeEquivalence` specifies an inverse
  and both simplicial homotopies over the same parameter. In particular the
  universal pair of arrows, with all their squares and higher transformations,
  is included; the comparison commutes with the parameter projection. It is not
  merely a choice of equivalence separately on objects. Triangle restrictions
  and constant diagonal paths commute with faces, degeneracies and restrictions
  of composable-square families. Thus the corresponding coherently varying Hom
  correspondence, and its pre/postcomposition, are retained.
* The next universal clause explicitly makes the canonical family strictly
  natural under every parameter map `h` and simplicial functor `f : D ⟶ E`.
  The ambient maps postcompose both triangles and the entire path by `f` and
  pull all coordinates along `h`. The equality is tested on any map of square
  families with these prescribed coordinates; because the family inclusions are
  monomorphisms these coordinates uniquely determine that map. Identity, arbitrary
  restrictions, degeneracies and higher simplices are included. No compatibility
  data are dropped when the parameter or the quasicategory changes.

Dependency declarations read and used:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`: full definitions/docstrings of
  `mappingSpace`, `mappingSpaceMap`, `evaluation`, `constantDiagrams`,
  `IsWeakHomotopyEquivalence`, `diagramVertex`, `commaSubcomplex`, `comma`,
  `coneCategory` and the space conventions. In particular the entire initial face
  is fixed in `mappingSpace`, and the endpoint restrictions are whole simplices.
* `Sheaf.CategoryTheory.RightPinchComparison`: `arrowEndpoints`,
  `arrowMappingSpace`, `arrowMappingSpaceInclusion`, `rightPinchPrism` and
  `right_pinch_comparison`. The latter's full signature/docstring specifies the
  canonical map degreewise, its inverse homotopies and naturality.
* The proof imports of the stated proof dependencies are
  `Sheaf.Paper.TrivialKanHomotopyEquivalence` (`exists_section_homotopy_equivalence`),
  `Sheaf.AlgebraicTopology.KanQuillenRightProper` (`right_proper_kan_quillen`),
  `Sheaf.CategoryTheory.InvertiblePrismExtension` (`invertible_prism_extension`) and
  `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`
  (`enhanced_functor_cone_calculus`); their signatures/docstrings were read.
* Mathlib's
  `AlgebraicTopology/SimplicialSet/AnodyneExtensions/Inner/PushoutProduct.lean`,
  lines 103–109 and 140–155, supplies
  `SSet.innerAnodyneExtensions_pushoutObjObjι'` and the internal-hom quasicategory
  instance. It is public because the latter is also used in the public statement.
* At inspection time the spine and isofibration-exponentiation proof nodes had no
  Lean binding. They are cited in the proof docstring and are not restated here.
  They are proof prerequisites, not missing statement prerequisites.

Edge cases checked: empty `D` makes the point clause vacuous; empty `T` has empty
source and target families and their unique inverse. A point quasicategory gives
contractible models. In an ordinary nerve every compatibility path with fixed
endpoint components is constant, and the two triangles are exactly the ordinary
commutative-square equation `va = bu`. Identity arrows, zero/one-dimensional
simplices and all degeneracies are included. Mapping spaces may be empty: no
inhabitance is assumed and weak equivalence includes the component condition.
Distinct parallel arrows and nontrivial paths in a Kan quasicategory are retained
by the internal path coordinate, rather than equated. All constructions remain in
`SSet.{u}` for arbitrary `u`; there is no universe equality between unrelated inputs.

Searches executed (all through the prescribed wrapper where applicable):

* LeanFinder: "Mapping spaces in a quasicategory of arrows are homotopy pullbacks
  of endpoint mapping spaces". Eight hits were truncated-quasicategory
  left/right homotopy and homotopy-category declarations, not the space formula.
* Loogle: `"Quasicategory", "Arrow"`. Zero hits.
* Mathlib grep: `mappingSpace|homotopyPullback|arrowMorphism` in
  `AlgebraicTopology`. Zero hits through `msearch.py`.
* LeanSearch: "A morphism space between two arrows in a quasicategory is a homotopy
  pullback of their endpoint morphism spaces". Eight hits included ordinary
  `CategoryTheory.Arrow.homMk`, `homMk'`, categorical pullbacks, image maps,
  truncated Hom and abstract bifibrant maps. Read `Comma/Arrow.lean` lines 31–46
  and 165–189: these require an equality in an ordinary category and do not state
  the coherent mapping-space formula.
* `rg` of `WeilConjectures/` for the node id, `arrowMorphism` and `mappingSpace`
  returned no matching declaration; the exact node-id check in
  `dag/lean_names_upstream.json` returned none.
* `rg` of `lean/Sheaf` found the pinch API, cone calculus and source-attachment
  path-pullback helper. The latter belongs to a downstream construction, so its
  module is not imported. The present theorem writes the pullback expression
  directly; it does not introduce a duplicate generic homotopy-pullback definition.
  Exact searches for the new declaration names in Mathlib, upstream and side Lean
  found no collisions. Other square/arrow hits concerned ordinary categories or
  unrelated base-change arrows.

No statement dispute, statement correction, new definition node, or dependency
repair is required. The only postponed theorem is this item's theorem. The one
module is compiled through `scompile.py`; the final dry-run result is recorded below.

Validation: `scompile.py Q22 lem-coef-infinity-arrow-morphism-square
lean/Sheaf/CategoryTheory/ArrowMorphismSquare.lean` succeeded for both the isolated
sandbox module (4.2 seconds) and the intended library module (4.6 seconds), without
errors or warnings. Static inspection confirms only the `lean` node field changed,
its recorded signature is verbatim, all 15 explicit declarations are listed, no
line exceeds 100 characters, and the only `sorry` is the main theorem's proof.
The current blueprint's `prop-coef-integral-exceptional-adjoint` statement/proof and
`sk-prop-sf-biduality-general` unit were also read; no unit or target is changed.

`deliver2.py Q22 lem-coef-infinity-arrow-morphism-square --no-push` printed
`OK (dry run)` for commit `481316e147`: compilation and preflight passed, with the
second reading explicitly deferred to the independent reader. Nothing was pushed.

## Second reading by Q22

Independent reading completed 2026-10-17. I read the sandbox node and all 15
explicit declarations, the recorded enhanced-diagram and pinch-comparison dependency
nodes and their actual modules, and the proof-dependency signatures. No released
stage-2 repair note exists for this item. There is no `statement_change`, new
node, or dependency module in this delivery.

Source check: the source is Kerodon, not the Stacks tag with the same identifier.
I opened [06BZ](https://kerodon.net/tag/06BZ),
[01PF](https://kerodon.net/tag/01PF), and
[01L5](https://kerodon.net/tag/01L5) independently. The first asserts a pullback
of Hom functors in the functor infinity category, so it supplies naturality,
not just a calculation on components. The identity-functor specialization is
applicable to any quasicategory. The second describes composition through
fixed-vertex triangles and the inverse of the consecutive-edge equivalence;
it imposes no strict composition choice. The third identifies the pinched and
unpinched Kan models. There are no hidden finiteness, nonemptiness, ordinary
category, or invertibility assumptions on either arrow. The available source
is online; its missing archive is already recorded in the node's source place.

My object/hypothesis/conclusion inventory and its Lean rendering follow. Each
verdict concerns the final, restored signature, which remains byte-for-byte
identical to the first worker's recorded signature.

1. **Any quasicategory D.** The binders `D : SSet.{u}` and `[Quasicategory D]`
   introduce precisely this object and hypothesis. The common universe is
   arbitrary. Verdict: matches; neither Kan fibrancy of D nor nonemptiness is
   assumed.
2. **The arrow quasicategory and two arbitrary arrows.** `(ihom Δ[1]).obj D`
   is the dependency's actual internal functor simplicial set, and `u v` are its
   degree-zero simplices. Mathlib's `instQuasicategoryObjIhom` supplies the needed
   instance without a new hypothesis. Verdict: matches, including noninvertible
   arrows.
3. **Four endpoint objects.** The expressions
   `(evaluation Δ[1] D (stdSimplex.obj₀Equiv.symm i)).app _ u` and the same
   expressions for `v`, for `i = 0,1`, are `d0,d1,e0,e1` in order. I checked
   `evaluation` against its restriction definition, rather than its name.
   Verdict: matches.
4. **The specified source mapping space.** The point equivalence starts with
   `mappingSpace ((ihom Δ[1]).obj D) u v`. This is the dependency's right-pinched
   object, with the entire initial face constant. The chosen map from
   `right_pinch_comparison` is uniquely pinned by `rightPinchPrism` after its
   monomorphic inclusion. The isomorphism `i` is pinned by its full square
   coordinate. Verdict: matches; no arbitrary comparison map is assumed.
5. **The first factor and postcomposition map.** In
   `ArrowSquareCompositionSpan D u v true`, `free` lands in the unpinched
   `Map(d0,e0)` and is a weak equivalence; `long` lands in `Map(d0,e1)`.
   `free_eq` fixes edge 01, `long_eq` fixes edge 02, and `arrowSquareLeg`
   fixes edge 12 to `v` and vertex 0 to `d0`. Thus the span represents exactly
   `a ↦ va` under the composition convention of 01PF. Verdict: matches.
6. **The second factor and precomposition map.** With `upper = false`, the
   same structure has `free` in `Map(d1,e1)` and `long` in `Map(d0,e1)`;
   edge 01 is `u`, vertex 2 is `e1`, and the free edge is 12. This represents
   `b ↦ bu`. Both maps are determined after the existing inclusions, so they
   cannot be unrelated maps with the same types. Verdict: matches.
7. **The homotopy pullback and its whole path.**
   `ArrowSquareSpanPresentation D u v` identifies the target with the literal
   iterated pullback using `P.long`, `evaluation ... 0`, `evaluation ... 1`, and
   `Q.long`. Its three equations preserve both triangle coordinates and the
   entire path. The eight conditions in `arrowSquarePathFamily` say the path
   starts at the upper long edge and ends at the lower long edge; both of its
   vertex families stay constant. Since they hold on entire simplices, this
   is the internal path object of the cross mapping space, with higher simplices
   retained. Replacing the domains of the two composition spans through `free`
   gives exactly the node's cospan. The existing natural pinch family identifies
   all three endpoint mapping spaces with their right-pinched conventions.
   Verdict: matches the stipulated path orientation `va` to `bu` and the stated
   model of the homotopy pullback.
8. **An equivalence of spaces.** The point clause asserts `KanComplex` of the
   target and `IsWeakHomotopyEquivalence` of the specified composite from the
   right-pinched source. `ArrowSquareRelativeEquivalence` also gives an inverse
   and both simplicial homotopies. These are a concrete presentation of the
   equivalence, not extra hypotheses on D. Verdict: matches the space convention.
9. **Joint endpoint projection.** `arrowSquarePathEndpoints` selects upper edge
   01 and lower edge 12, in this order. The final equation identifies the
   composite with `lift` of the two `mappingSpaceMap (evaluation ...)` maps,
   each followed by its canonical pinch and inclusion. All these are the actual
   recorded dependency declarations. The equality supplies the requested
   coherent compatibility using canonical representatives. Verdict: matches
   both factors jointly, without swapping them or discarding their maps.
10. **Naturality in both arrows and coherent composition.** The comparison is
    a single family `c` over every simplicial parameter `T`, for entire arrow
    families `U,V : T ⟶ Arr(D)`, and is specified after the family inclusion by
    restriction to the two triangles and the constant diagonal path. The inverse
    homotopies in `ArrowSquareRelativeEquivalence` remain over that same parameter.
    Taking arbitrary simplices includes squares and their higher transformations;
    the square restrictions and the composition spans use the same face and
    degeneracy maps, including composable-square families. No natural choice of
    inverse or strict composition operation is asserted. Verdict: matches the
    coherent naturality clause rather than only its objectwise values.
11. **Naturality under simplicial functors.** The next universal clause covers
    every `f : D ⟶ E`, every parameter map `h : T ⟶ T'`, and any square-family
    map `x` with the prescribed coordinates. `arrowSquareAmbientMap` and
    `arrowSquarePathAmbientMap` postcompose each coordinate by `f` and apply `h`
    to the parameter. The resulting equality is strict for this canonical
    restriction construction, hence supplies the node's coherent naturality.
    Verdict: matches, including identity functors and parameter restrictions.

I initially questioned whether the span-presentation and Kan clauses were added
conclusions, and temporarily tested their removal, together with replacing the
strict naturality equality by a homotopy. That would omit the identification of
the two composition maps and would weaken the canonical-family presentation.
I restored every such edit. The final Lean source and signature are unchanged.

One bookkeeping mismatch remains from the worker's delivery: the signature uses
`arrowMappingSpace`, its inclusion, and the uniquely characterized family supplied
by `right_pinch_comparison`, but its node was only listed in `proof_deps`.
I added the already landed `lem-coef-infinity-pinch-comparison` to `stmt_deps`
under brief-stage2 §5's authorization to add landed nodes, and updated `lean.date`
and `lean.note`. This adds no hypothesis and changes no mathematical statement.
The worker's earlier assertions that only `lean` changed are superseded by this
explicit dependency repair. There is no dependency-module repair to review.

Edge cases: empty D has no arrows and the point clause is vacuous; for empty T
both parameter families are empty. The terminal quasicategory gives contractible
models. In an ordinary nerve the mapping spaces are discrete and the triangles
and path give exactly `va = bu`. Empty mapping spaces remain allowed; the
component-bijection condition in the recorded weak equivalence prevents a false
empty-to-nonempty equivalence. Identity arrows, degenerate simplices, and all
higher degrees are retained. A Kan quasicategory with nonconstant paths keeps
that entire path coordinate. There is no index set, scheme, characteristic,
cohomological degree, or zero-object assumption in this node. Arbitrary `u`
covers all sizes in a fixed sufficiently large universe as required by the
dependency, with no extra relation between independent universes.

Independent searches, using different wording from the worker:

- LeanFinder via `msearch.py`: "Hom functor on the interval functor infinity
  category preserves the fiber product of endpoint mapping spaces and
  compositions". Eight results concern simplicial thickenings of linear orders
  and ordinary Cech nerves. I opened `SimplicialThickening.compFunctor` and its
  enriched Hom instance; these do not compute Hom in the arrow quasicategory.
- Loogle via `msearch.py`: `"SSet", "pullback"`. Six results concern skeletal
  pullback squares, finiteness, and internal-Hom lifting properties. The last
  are prerequisites, not the natural arrow-Hom equivalence.
- LeanSearch via `msearch.py`: "Coherent transformations between edges of an
  infinity category are pairs of endpoint maps with a homotopy between
  composites". Eight results concern truncated edge homotopies, ordinary joins,
  and ordinary categorical pullbacks. I also opened `CommaMorphism`, `Arrow.homMk`
  and `homMk'`: their ordinary-category commutativity equality is not this
  statement about arbitrary quasicategories and whole mapping spaces.
- Prescribed Mathlib grep for `oriented.*fiber|mapping.*square|Hom.*oriented`
  in AlgebraicTopology: no hits. Independent `rg` over Mathlib, upstream
  `WeilConjectures`, project `lean/Sheaf`, and the upstream name map used
  oriented fiber, interval mapping, commutative square, homotopy pullback,
  and arrow/mapping combinations. The existing pinch and generic path-pullback
  declarations were inspected; they are used directly or as a pullback expression,
  not copied. No existing theorem or duplicate square construction was found.

Standards: every declaration has its source and blueprint docstring; the main
statement's seven proof steps match the node, including all stated proof imports.
The spine and isofibration-exponentiation proof nodes remain without a Lean
binding and are not required to type this statement. The internal-hom and inner
pushout-product instances/lemmas were read in their actual Mathlib source.
All definitions contain concrete data, and their structure/naturality proof
fields contain no postponed proof. There is exactly one `sorry`, the main
item theorem. There are no private notions, local notation or local instances.
Every universe and variable is bound, all lines fit 100 characters, and
`lean.statement` equals the final file signature byte for byte.

Final validation after the second reading: prescribed `scompile.py` succeeded for
both sandbox and library forms (5.2 s and 6.0 s), without errors or warnings.
`deliver2.py Q22 lem-coef-infinity-arrow-morphism-square --no-push` printed
`OK (dry run)` at `1e0ad961fe`; server preflight and compilation passed. The
final delivery below includes this validation record and the complete second reading.
