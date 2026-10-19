## Worker report

The delivery states `SSet.Enhanced.cartesianFibration_baseChange_pushout` in
`Sheaf.CategoryTheory.CartesianFibrationBaseChangePushout`. Its proof is exactly `sorry`.
There are no new definitions, axioms, helper theorems, or statement corrections.
The natural-language statement, proof and proof dependencies are unchanged. The statement
dependencies gain four already landed interfaces used to express its existing notions.

### Hypotheses and clauses

- Infinity categories and universe convention: `CatInfinity.{u}` is the existing
  core-restricted coherent nerve of all `u`-small quasicategories, formed in universe
  `u + 1`. The single explicit universe `u` can be any containing universe for the
  displayed categories. The finite square has type `SuspensionComparison.square.{u + 1}`.
  This does not equate an independently prescribed object and morphism universe.
  `CompleteAlgebroid` is imported for the node's recorded conventions; the statement
  has no algebroid or coefficient-object hypothesis.
- Original coherent square: evaluate `α` at interval endpoint `1`. A simplicial map
  from `Δ[1] × Δ[1]` to Cat infinity retains its diagonal, both triangles and their
  coherence. The original `A,B,C,D` are its values at `(0,0),(1,0),(0,1),(1,1)`.
  Neither leg nor any other arrow of this square has a fibration hypothesis.
- The square is a pushout: `c : SuspensionComparison.SquareCocone (...)` fixes the
  apex to its `(1,1)` value and fixes its entire contraction cylinder. `hpushout` is
  `IsColimiting (SuspensionComparison.boundary (...) false) c.cocone`. The boundary
  deletes precisely the terminal corner, leaving the original span. `IsColimiting`
  means initiality of this particular coherent cocone, not mere existence of some
  colimit with an unrelated apex or maps.
- Given Cartesian fibration `p:E → D`: `p : CatInfinity _⦋1⦌` is the actual functor
  `catInfinityArrow p`. Its endpoints are `catInfinityObject (CatInfinity.δ 1 p)`
  and `catInfinityObject (CatInfinity.δ 0 p)`. `hp` uses `cartesianFibration` with
  the endpoint quasicategory proofs extracted from those Cat-infinity vertices.
  This predicate explicitly includes `InnerFibration` and a Cartesian lift of every
  base edge with each prescribed target. Its final-horn edge test is the equivalent
  rendering of the statement's mapping-space Cartesian-edge condition: apply the
  existing cocartesian mapping criterion to the opposite functor, then the natural
  pinch and triangle-composition comparisons. This equivalence is precisely step 1
  of the unchanged proof, not an added mathematical assumption or a change in lifts.
- The base-change square, with its specified maps: `α` is a coherent transformation
  from the endpoint-0 square to the endpoint-1 square. `hbaseChange` is the existing
  `IsDescentCartesianTransformation α`, which asserts that each naturality square
  is an intrinsic pullback by `SquareCone` and `IsLimiting`. These conditions describe
  the construction of the base-change cube; they are not additional conditions on
  the original diagram. Every vertex of the square has an arrow to `(1,1)`. Its
  naturality pullback therefore identifies the corresponding endpoint-0 object
  with the endpoint-1 object pulled back along the apex arrow. Thus these are exactly
  `A ×_D E`, `B ×_D E`, `C ×_D E`, and `E`, coherently with all displayed maps.
  Conversely the base-change square gives this cartesian transformation, since
  pullbacks compose. This formulation quantifies over all representatives and
  does not replace the canonical construction by an arbitrary map.
- `hapex` fixes the entire terminal component of `α` to `diagramVertex
  (SSet.yonedaEquiv.symm p)`. It consequently identifies the source apex with `E`
  and the target apex with `D`; these are not independently chosen equivalent
  categories without a comparison to the specified fibration.
- Conclusion: there exists `c' : SquareCocone (α ≫ evaluation ... 0)` with
  `IsColimiting (boundary (...) false) c'.cocone`. Both the apex and whole cocone
  path are fixed by the source square through `SquareCocone`. This is the pushout
  assertion for exactly the base-change square. No strict degreewise pullback or
  ordinary-category pushout has been substituted for an intrinsic construction.

### Dependency declarations used

The original two dependency records were opened, including their recorded signatures
and docstrings. The four additional nodes already have landed Lean records; their
source interfaces were also opened. No dependency record needs repair.

- `def-coef-complete-algebroid`: `Sheaf.CategoryTheory.CompleteAlgebroid`,
  `SSet.Enhanced.Algebroid.completeCategory`; imports the node's infinity-category
  and universe conventions. No algebroid construction is needed by this lemma.
- `def-coef-infinity-fibrations`:
  `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`, publicly reexporting
  `SSet.Enhanced.cartesianFibration`, `IsCartesianEdge` and `SSet.InnerFibration`
  from `InfinityFibrations`. The newer arbitrary-base cocartesian predicate does
  not remove the original Cartesian-fibration interface used here.
- Added `def-cbc-enhanced-cartesian-fibration`:
  `Sheaf.CategoryTheory.EnhancedCartesianFibration`, `SSet.Enhanced.CatInfinity`,
  with quasicategory objects and mapping cores in its full degreewise construction.
- Added `lem-coef-cat-infinity-opposite-involution`:
  `Sheaf.CategoryTheory.CatInfinityOppositeInvolution`, `catInfinityObject` and
  `catInfinityArrow`. These extract the existing objects and functor of a coherent
  nerve edge directly; the opposite-involution theorem is not assumed.
- Added `lem-coef-suspension-square-comparison`:
  `Sheaf.CategoryTheory.SuspensionSquareComparison`, `SuspensionComparison.square`,
  `corner`, `boundary`, `SquareCone`, `SquareCocone`. Their apex and path equations
  prevent substituting an unrelated cone or cocone.
- Added `lem-coef-cartesian-colimit-descent-criterion`:
  `Sheaf.CategoryTheory.CartesianColimitDescentCriterion`,
  `IsDescentCartesianTransformation` and `IsDescentCartesianArrow`. Only these
  definitions specify the base-change cube; no presentability, universal-colimit,
  descent, or gluing hypothesis of that module's theorem is used or assumed.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`, transitively reexported by the
  preceding interfaces: `diagramVertex`, `evaluation`, `IsLimiting`, `IsColimiting`.

All recorded proof-dependency modules are imported without `public`, unless already
publicly imported for their statement interfaces. The one exception is
`lem-coef-degreewise-cartesian-pullback-cat-infinity`, whose Lean record is still null:
there is no recorded module to import. It remains cited in the unchanged proof plan
and in the theorem docstring's canonical degreewise-pullback comparison steps.
The additions were checked transitively against both statement and proof edges:
none has a dependency path back to this item, so no import or DAG cycle is introduced.

### Edge cases checked

`p = id_D`: the transformation is an equivalence of squares and the conclusion is
invariance of the original pushout. `E` empty: every pulled-back category is empty;
Cartesian lifts are vacuous for the empty total space, and the empty square is a
pushout. `A` empty: this is preservation of a coproduct, including empty summands.
`D` terminal: the pullback square is the product of the original square with `E`.
No nonemptiness or nonzero-object hypothesis appears. Degenerate arrows of the index
square are included in `IsDescentCartesianTransformation`, but their squares are
identity pullbacks, so they impose no further restriction. The two original span
legs remain arbitrary; neither is silently required to be mono or an isofibration.
A chosen coherent base-change representative supplies `α`; the pullback universal
property identifies any two such representatives, retaining the actual maps.

### Searches and source checks

Searches were run through the prescribed `msearch.py` for this group and item:

- LeanFinder: `Base change along a Cartesian fibration preserves coherent pushouts
  of infinity categories`. Eight hits concern ordinary fibered categories,
  parametrized pushouts, preservation by ordinary functors, and stability of a
  lifting property or model-category fibrations. No exact infinity-categorical
  pushout-preservation statement.
- LeanSearch: `Cartesian fibrations preserve pushouts under base change in infinity
  categories`. Eight hits concern ordinary Cartesian functors, stable morphism
  properties and model-category fibrations, not the coherent-colimit theorem.
- Loogle: `IsPushout, pullback`. No hits; the service reports unknown identifier
  `IsPushout`. This query is recorded as unsuccessful search syntax, not evidence
  that the relevant ordinary Mathlib interface is absent.
- Mathlib grep: `cartesian.*[Pp]ushout|[Pp]ushout.*cartesian` under `CategoryTheory`.
  Six ordinary-category hits, including arrow-category monoidal structures and
  bicartesian squares. Read `LocallyCartesianClosed/ExponentiableMorphism.lean`
  for its right-adjoint-to-ordinary-base-change signature: it is not this theorem.
- `rg` in the entire upstream `WeilConjectures` for the exact item id and for
  Cartesian/pullback/pushout combinations: no exact declaration. The broad hits
  concern ordinary scheme gluing and affine transition limits.
- `rg` in `lean/Sheaf` for Cartesian/pullback/pushout combinations and for the chosen
  declaration name, plus `dag/lean_names_upstream.json`: no exact statement.
  Related `CartesianFibrationPullback` proves a componentwise Cartesian-edge
  criterion, `InfinityFunctorPushout` gives the functor-category restriction
  equivalence, and `CartesianColimitDescentCriterion` provides generic predicates
  and a conditional descent criterion. None is this pushout base-change theorem.

The node's HTT source and all seven proof steps were read. The IAS PDF fetch timed
out, so no claim is made that a fresh online source reading succeeded. The statement
requires no source-based correction. The resolved stage-1 repair note was read:
its required proof split has already landed, and this delivery retains that proof
and the source statement verbatim. The old Q38 and Q25 deliveries were DAG splits,
not existing Lean statements. The initially empty sandbox contained only dispatcher
markers, so there was no interrupted delivery mutation to repeat.

No `STATEMENT-DISPUTED` issue was found.

### Validation

The prescribed `scompile.py` file-only compile succeeded with no errors or warnings
on the declaration. The final delivery dry run recompiles the delivered file and
runs the maintainer's server preflight. No global build or direct Git operation was run.

## Second reading by NH

Independent maintainer second reading of immutable delivery 3049313c80f3baea009576df5384156c84f84997, 2026-10-17.


I started with `packet.md`, then read the immutable module, item JSON, all six
statement-dependency JSON records, and report under `snapshot/`. I read
`check-brief2.md` in full, the stage-2 brief, delivery-errors H1–H13, and the relevant
project conventions. Context declarations were read in the permitted read-only
NH clone; the immutable delivery files themselves were read from `snapshot/`.
The resolved repair note is a stage-1 re-split requirement, not a withdrawn stage-2
binding. The item retains its seven-step route, including the extracted degreewise
pullback comparison and ordinary-localization citation. There is no new
`statement_change` requiring a citer audit.

### Source and statement inventory

I successfully opened the actual IAS HTT PDF, rather than relying on the worker's
unsuccessful fetch. Source locations:
https://www.math.ias.edu/~lurie/papers/HTT.pdf,
Proposition 2.4.1.8 (printed p. 118), Proposition 2.4.4.3 (printed pp. 131–132),
Proposition 3.3.1.3 and Corollary 3.3.1.4 (printed pp. 205–206), and §4.2.4
(printed pp. 257–260).
The first pair identifies the horn and mapping-space edge conditions. The second
pair supplies equivalence invariance under Cartesian base change and the Joyal
homotopy-pullback comparison even with arbitrary simplicial bases. The theorem
under review is their pushout consequence via a monomorphism pushout model, not a
claim that arbitrary base change preserves all Cat-infinity pushouts. Section 4.2.4
provides the coherent/homotopy-colimit comparison context; the delivered proof plan
correctly avoids treating the Joyal model as a simplicial model category.

The object/hypothesis/conclusion correspondence is as follows.

1. **Infinity categories and size.** `CatInfinity.{u}` has actual `u`-small
   quasicategories as objects and cores of functor simplicial sets as mapping spaces;
   it lives in simplicial universe `u + 1`. The index `square.{u + 1}` lives in that
   containing universe. The universe `u` is arbitrary and may contain all five
   categories, as the node explicitly permits. No independent site, coefficient,
   object, or morphism universes have been equated. No finiteness or presentability
   hypothesis is imposed on these categories.
2. **Original coherent square A,B,C,D.** The endpoint-1 evaluation of `α` is a map
   `Δ[1] × Δ[1] → CatInfinity`, including its diagonal and both triangles. Its four
   corners are the four original categories. In `SuspensionComparison`, `puncture
   false` removes exactly `(1,1)`, leaving the span. There is no condition on the
   original square's arrows.
3. **Specified pushout.** `c : SquareCocone (...)` fixes its apex at corner `(1,1)`
   and fixes its entire path by `path_eq = conePath`. `hpushout` makes this cocone
   initial in the actual coherent cocone category. Thus it asserts the pushout of
   this square, not the existence of an unrelated pushout with the same vertices.
4. **Given functor p:E→D.** `p : CatInfinity _⦋1⦌` is a coherent-nerve edge and
   `catInfinityArrow p` extracts its actual endpoint functor. `δ 1` is its source,
   `δ 0` its target. The two explicit quasicategory proofs in `hp` come from those
   vertices' defining properties; they add no assumption.
5. **Cartesian hypothesis.** The body of `cartesianFibration` is `InnerFibration`
   together with a final-horn Cartesian lift of every base edge for every prescribed
   target. Its endpoint equations have the required direction. `IsCartesianEdge`
   tests every final outer horn in dimensions at least two and its last edge.
   The node's mapping-space characterization is equivalent, as verified against
   HTT 2.4.4.3 and the existing cocartesian mapping criterion under opposition.
   The `hp` binder neither drops the inner-fibration condition nor assumes that
   all edges are Cartesian.
6. **Canonical base-change square.** `α` is a coherent transformation from the
   endpoint-0 square to the endpoint-1 square. `hapex` identifies its whole terminal
   component with the Yoneda map of the specified edge `p`. The body of
   `IsDescentCartesianTransformation` requires every edge's naturality square to
   have the existing limiting `SquareCone`, retaining its complete coherent path.
   Applying it to each arrow from a vertex to `(1,1)` identifies the endpoint-0
   corners with `A ×_D E`, `B ×_D E`, `C ×_D E`, and E, including the induced maps.
   The additional naturality squares follow from pullback pasting. Conversely an
   intrinsic base-change diagram supplies this coherent transformation. Quantifying
   over these representatives is an equivalent universal-property formulation,
   not a hypothesis that substitutes an arbitrary comparison map for base change.
7. **Conclusion.** The existential `c'` is a `SquareCocone` of exactly the
   endpoint-0 square. Its apex and full path are fixed, and `IsColimiting` asserts
   its initiality. Thus the complete displayed base-change square is a pushout.
   The existential supplies a representative of this specified cocone; it cannot
   select unrelated structure to make a weaker conclusion true.

### Dependency records and exact declarations

All six immutable statement dependency records and their statements were read.
I inspected the following actual source interfaces and their docstrings in
`/home/ubuntu/weil-newtargets-NH/lean/Sheaf/CategoryTheory/`:

- `CompleteAlgebroid.lean`: universe/convention import and the recorded
  `Algebroid.completeCategory`, with `IsComplete` and `completenessMap`. No
  algebroid, unit-section, or monoidal-coefficient assumption leaks into this item.
- `InfinityFibrationsOverSimplicialBases.lean`: reexports `InfinityFibrations.lean`.
  I read `IsCartesianEdge` and `cartesianFibration` at lines 61–93 in the latter,
  including their actual lifting and target equations. The record's newer
  `cocartesianFibrationOver` does not replace or invalidate this existing interface.
- `EnhancedCartesianFibration.lean`: `catInfinitySubcomplex` and `CatInfinity`
  (lines 97–116), restricting every mapping simplex to the functor core. This is
  not the unrestricted simplicial nerve with noninvertible transformations in
  its mapping spaces.
- `CatInfinityOppositeInvolution.lean`: `catInfinityObject`, `catInfinityThickEdge`,
  and `catInfinityArrow` (lines 45–70), extracting endpoints and the actual functor.
  The opposite-involution theorem is not assumed in the item's signature.
- `SuspensionSquareComparison.lean`: `square`, `corner`, `puncture`, `sweep`,
  `boundary`, `conePath`, `SquareCone`, and `SquareCocone` (lines 42–121).
  Its unrelated pointed-category theorem contributes no pointedness hypothesis.
- `CartesianColimitDescentCriterion.lean`: `IsDescentCartesianArrow` and
  `IsDescentCartesianTransformation` (lines 54–69). Only these actual pullback
  predicates are used; the descent theorem's presentability, universal-colimit,
  finite-limit and gluing hypotheses are not imported as assumptions.

I also read `EnhancedDiagramsCones.lean`'s `diagramVertex`, `evaluation`, coherent
comma/cone/cocone constructions and `IsLimiting`/`IsColimiting` (lines 118–126,
239–279, 288–305), and the full signature and proof docstring of
`infinity_cocartesian_mapping_criterion`. These are existing constructions, not
private duplicates. The four added statement dependencies have landed records and
supply precisely the extra interfaces used, as permitted by §5. No dependency node
or module is being repaired by this delivery.

The proof-only imports correspond to the node's recorded proof dependencies, as
required by the stage-2 import convention. The still unstated
`lem-coef-degreewise-cartesian-pullback-cat-infinity` is a proof dependency in the
unchanged DAG proof, not an absent notion needed to type this statement. Nothing
in the delivered signature needs a new helper or an unstated DAG prerequisite.
There is therefore no reason to return for a missing helper, force universes
smaller, or wait on another item.

### Edge cases and one-definition check

I checked p the identity, E empty, A empty (coproduct square), D terminal (product
with E), and D empty (all categories mapping to it are empty). Empty summands,
empty total space, and degenerate index edges are included; there are no
`Nonempty`, zero-object, ring, characteristic, or degree restrictions. Degenerate
naturality squares are identity pullbacks. The square includes both coherence
triangles, and the fixed-cocone equations prevent losing their compatibility.

The worker records LeanFinder, LeanSearch, failed Loogle syntax, and grep searches
with specific outcomes; I do not count its failed Loogle query as evidence of
absence. I independently searched the permitted NH side sources, upstream
`WeilConjectures`, Mathlib `CategoryTheory`, and `dag/lean_names_upstream.json`,
using the item/declaration names and the alternative terms `exponentiable`,
`flat.*fibration`, `fibration.*colimit`, `base.change.*colimit`, and Cartesian/
pushout combinations. No exact existing declaration was found. I inspected
Mathlib `LocallyCartesianClosed/ExponentiableMorphism.lean:41–57`: it assumes an
ordinary slice right adjoint and does not prove this theorem about quasicategories.
The side `CartesianFibrationPullback` is an edge criterion, and
`LocalizationCartesianPullback` is a consumer about localization, not a duplicate.
The imported descent predicates are general predicates, not a second definition
of Cartesian base-change preservation.

### Mechanical gates and compiler evidence

- The only delivered module has one theorem, with proof exactly `by sorry` and no
  definitions, private notions, local instances, auxiliary axioms or local proofs.
- Module and theorem docstrings give the source and correct blueprint ID. The
  theorem docstring follows all seven node proof steps, including the arbitrary
  simplicial-set and coherent-cocone comparisons.
- `autoImplicit false` is set. All variables and the single universe are bound.
  Every line has length at most 100; namespace and import paths follow conventions.
- A direct extraction of the signature from `theorem` up to `:= by` is byte-for-byte
  equal to the immutable JSON `lean.statement` (checked by Python: `VERBATIM True`).
  The module, declaration, file, branch, group, date and existing=false fields agree.
- Reproduced the recorded file-only compile with:
  `python3 /home/ubuntu/weil-launcher-nt/scompile.py NH
  lem-coef-localization-cartesian-pullback-pushout
  snapshot/lean/Sheaf/CategoryTheory/CartesianFibrationBaseChangePushout.lean`.
  Exit code 0. The wrapper reported successful sandbox compilation (1.7 s) and
  library compilation at `Sheaf/CategoryTheory/CartesianFibrationBaseChangePushout.lean`
  (1.8 s), with no errors or warnings. Artifacts were in the wrapper's private
  `/dev/shm/nt-tmp/nt-local-compile-wzyrtrqf/.lbuild` overlay. The installed wrapper
  now dispatches to the server and confirms the library module there; this was
  the prescribed wrapper, not a direct SSH command or a global/local lake build.
- No pro-etale objects occur and no pro-etale substitute was used. No repository
  edits, Git mutations, delivery, merge, claim, live Lean writes, or global build
  were performed. The report-only correction does not alter the compiled file.

### Findings and disposition

The complete mathematical statement passes the hypothesis, conclusion, edge-case,
canonical-construction, universe, dependency and source checks. The sole finding
is the placeholder second-reading section (H11/report-content H1). The supplied
complete report replacement repairs it with this independent reading. The worker's
record of a failed source fetch remains as history; this review supplies the
successful source check. No substantive error or further repair is outstanding.
