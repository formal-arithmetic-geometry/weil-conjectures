## Worker report

Item: `lem-coef-infinity-relative-cone-equivalence`, group Q32, stage 2.
Module: `Sheaf.CategoryTheory.RelativeConeEquivalence`.
Main declaration: `SSet.Enhanced.relative_cone_equivalence`.

The only postponed proof is the main theorem, which states all four clauses and
all three limit duals as a conjunction of expanded, public predicates. Its
docstring gives the node's nine-step proof plan with the named prerequisites.
The nineteen definitions are helpers for this node's own assertion. Every helper
has real data; no object is chosen from an unproved existence theorem. The
mapping-space bundle uses the named dependency theorem only for its proof that
the already constructed mapping space is Kan.

The item statement is unchanged. Its statement dependencies gain the already
landed `lem-coef-infinity-isofibration-exponentiation`, whose exact source-fixed
`IsIsofibration` predicate is needed in clause (4), and
`lem-coef-infinity-slice-arrow-equivalence`, whose `rightVertexSlice` replaces
the downstream slice interface identified in the return. There are no new nodes,
dependency repairs, statement corrections, or disputed assertions.

### Hypotheses and clauses

* The fixed sufficiently large universe is `universe u`; every diagram, indexing
  simplicial set, quasicategory and join is in `SSet.{u}`. All variables are bound
  explicitly, and `autoImplicit` is false. The three independent universes of
  `enhanced_functor_cone_calculus` are explicitly instantiated at `u`, rather
  than allowing a universe metavariable to survive in the Kan-space bundle.
* Throughout, the functor and coherence notions are the dependency's
  `AreNaturallyEquivalent`, `IsFunctorEquivalence`, `IsEquivalenceEdge`, and
  right-pinched `mappingSpace`. The relative tests are exactly the dependency's
  `IsRelativeColimitDiagram` and `IsRelativeLimitDiagram`, including its path
  pullback model; no ordinary-category universal property replaces them.
* Clause (1) is `RelativeColimitNaturalInvariance`. `M : SSet.{u}` is arbitrary;
  only `D` and `B` carry `Quasicategory` hypotheses. `p : D ⟶ B` has no fibration
  hypothesis. `AreNaturallyEquivalent q q'` is the sole additional hypothesis,
  and the conclusion is the biconditional of their two relative-colimit tests.
* Clause (2) is `RelativeColimitIndexInvariance`. All four quasicategories, the
  inner fibration instance on `p`, and the index equivalence hypothesis on `e`
  are explicit. Its first conjunct quantifies over the prescribed `f` and `g`
  with `f ≫ p = rightJoinConeInclusion M ≫ g`. Both existential statements
  require the exact boundary, exact base and relative universality. On `L` they
  are `rightJoinConeInclusion L ≫ q = e ≫ f` and
  `q ≫ p = relativeRightConeMap e ≫ g`. `relativeRightConeMap` is the existing
  ordered-join functor on `(e, 𝟙 Δ[0])`, so it fixes the apex. The second conjunct
  gives the biconditional for every particular diagram on the right cone of M.
* Clause (3) is `RelativeColimitFinalEdge`. `IsTerminal M t` renders finality.
  The apex edge is literally `q.app _ (relativeRightTop M 0 t)`, where the top
  simplex is the ordered-join generator of `t` and the new vertex. Its
  `yonedaEquiv.symm` is tested by the dependency's horn-lifting
  `IsCocartesianEdge p`. The second conjunct assumes equivalence of precisely
  its image under `p.app` and concludes equivalence of the same edge in `D`.
* Clause (4) is `RelativeConeOppositeDuality`. `SSet.opFunctor` and `SSet.op`
  are Mathlib's precomposition with `SimplexCategory.rev`; the source was read
  and its operator is exactly `i ↦ (α i.rev).rev`. The existential `hOp`
  asserts quasicategory closure for every quasicategory; it is proof data, not
  an extra hypothesis. Preservation of isofibrations uses exactly
  `IsIsofibration p → IsIsofibration (opFunctor.map p)`.
* The mapping-space part is `RelativeOppositeMappingSpaces hOp`. Its `ε D x y`
  is an isomorphism in the dependency's existing `spaceWeakEquivalences.Q`
  localization from the Kan space `Map(D.op,x,y)` to `Map(D,y,x)`. Naturality
  is asserted as the commuting equality for every functor `f : D ⟶ E` and
  both transported endpoints, using the actual `mappingSpaceMap` on each side.
  No strict identification of opposite right-pinched models is asserted.
* The cone comparison in clause (4) is an existential family of isomorphisms
  `e M : (leftJoinCone M).op ≅ rightJoinCone M.op` satisfying
  `RelativeConeReversalFormula`. It fixes the whole pure base and apex, and
  sends each reversed `relativeLeftTop M n s` to `relativeRightTop M.op n s`.
  These mixed generators and their restrictions include every simplex, also
  repeated apex vertices. Thus the comparison cannot be an arbitrary
  isomorphism. For every `p` and every `q` on a left cone, the limit predicate
  is equivalent to the colimit predicate of
  `(e M).inv ≫ opFunctor.map q` over `opFunctor.map p`. The shape `M` is arbitrary
  and there is no fibration hypothesis in this part.
* The slice part is `RelativeOppositeSlices`. The first-vertex coslice is the
  real-data helper `firstVertexCoslice C c :=
  (rightVertexSlice C.op (opObjEquiv.symm c)).op`; the opposite over-slice is the
  existing `rightVertexSlice C.op (opObjEquiv.symm c)`. The comparison fixes the
  underlying `(n+1)`-simplex for every degree and every simplex. This records the
  entire remaining face and the whole canonical cone, since the face projections
  and canonical prism transformations are restrictions of that same stored
  simplex. It does not merely identify vertices.
* The final three conjuncts are `RelativeLimitNaturalInvariance`,
  `RelativeLimitIndexInvariance`, and `RelativeLimitInitialEdge`. These spell
  out the complete duals of (1)--(3), with left cones, exact base/boundary
  equalities, an initial indexing object, the actual apex-to-object edge,
  `IsCartesianEdge`, and the corresponding edge-equivalence implication.

### Dependency declarations used

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsEquivalenceEdge`,
  `AreNaturallyEquivalent`, `IsFunctorEquivalence`, `mappingSpace`,
  `mappingSpaceMap`, `IsTerminal`, `IsInitial`, `spaceWeakEquivalences`.
* `Sheaf.CategoryTheory.RelativeInfinityCone`: `rightJoinCone`, `leftJoinCone`,
  both cone inclusions, `IsRelativeColimitDiagram`, `IsRelativeLimitDiagram`.
* `Sheaf.CategoryTheory.InfinityFibrations`: `IsCocartesianEdge`,
  `IsCartesianEdge`; Mathlib's `SSet.InnerFibration` is used directly.
* `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`:
  `enhanced_functor_cone_calculus` supplies the Kan proof on the existing
  right-pinched mapping space; it is imported through the relative-cone module.
* `Sheaf.CategoryTheory.IsofibrationExponentiation`: `IsIsofibration`, including
  both quasicategory conditions and exact equivalence lifting at a fixed source.
* Existing join construction helpers, reexported by the relative-cone module:
  `orderedJoinFunctor`, `joinGenerator`, `orderedJoinInl`, `orderedJoinInr`,
  `joinAugmentation`. Empty simplices use the terminal augmentation.
* `Sheaf.CategoryTheory.SliceArrowEquivalence`: `rightVertexSlice` and its
  source-fixed endpoint convention are used for `(C^op)_{/c}`. The real-data
  helper `firstVertexCoslice` is the opposite of this existing slice. The old
  `KanMappingRestriction` import and `kanSlice` construction were removed: its
  theorem is downstream through `relative-kan-existence`, so importing it would
  close the cycle identified in the return. No theorem from that module is used.
* Mathlib `SSet.opFunctor`, `SSet.opObjEquiv`, `SSet.stdSimplex.opIso`, and
  `SimplexCategory.rev` supply the exact opposite construction. No second
  opposite operation is defined.

All already stated proof dependencies have their prescribed non-public imports:
JoyalModelStructure, KanMappingHomotopyInvariance, AnodyneCocones,
TrivialKanHomotopyEquivalence, TerminalAnodyne, InfinityMappingComposition,
SubdivisionFacePosetCalculus, ExInfinityFiniteProducts, RightPinchComparison.
The remaining already stated proof dependencies are public imports because the
statement uses their interfaces. No unstated proof dependency is replaced by an
extra theorem in this delivery.

### Edge cases

Checked the empty indexing simplicial set in (1) and the opposite comparison:
its cone is the point and the pure-apex equation still specifies the comparison.
No nonemptiness instance is introduced. An empty indexing quasicategory is
allowed in (2); an equivalence forces the matching empty shape, and the two
existential assertions keep the same prescribed maps. Clause (3) explicitly
supplies `t`, as the node requires, and therefore makes no accidental assertion
about a nonexistent final object. With a singleton index the constructed top
simplex is the unique indexing-object-to-apex edge. For `p = 𝟙`, the relative
testing squares are tautological but the conclusion still has exactly the
stated hypotheses; the edge implication then says that an equivalence is an
equivalence. For a map to a point, (3) gives the usual equivalence from the final
index value to its colimit. Cone-reversal generators include `n=0`, pure factors,
and degeneracies with repeated apex. Slice reversal imposes the full simplex
formula even for `n=0`, so it also checks both endpoints of slice objects.

### Searches and source checks

Searches were made through `msearch.py` as required. The tool's original receipts
are in its per-item `searches.jsonl`; a copy is retained in the sandbox.

* LeanFinder: "Relative universal colimit diagrams of quasicategories are
  invariant under natural equivalence and equivalence of indexing
  quasicategories, and opposite duality". Eight hits, all ordinary-category
  universal-colimit or cocone-equivalence statements, including
  `CategoryTheory.IsUniversalColimit.whiskerEquivalence_iff`. None treats these
  relative quasicategorical mapping-square tests.
* Loogle: `"Quasicategory", "colimit"`. Zero hits.
* Mathlib grep: `relative.?[Cc]olimit|[Ii]sofibration|[Ss]et.*[Oo]pposite`.
  Twenty-five displayed hits, largely ordinary algebraic opposites and imports;
  no statement of the current item.
* LeanSearch: "Opposite simplicial set reverses ordered simplicial joins and
  quasicategory mapping spaces". Eight hits, including the exact existing
  `SSet.op`, `SSet.opFunctor`, `SSet.op_map`, `SSet.opObjEquiv`, `SSet.op_δ` and
  `SSet.opEquivalence`. Read `SimplicialSet/Op.lean`,
  `SimplexCategory/Rev.lean`, and the opposite-simplex isomorphism in
  `SimplicialSet/StdSimplex.lean`. Reused these declarations.
* LeanSearch for simplicial slices/coslices with a fixed endpoint returned
  primitive horn, simplex-face and subcomplex declarations; Loogle
  `"SSet", "slice"` and grep `kanSlice|[Cc]oslice|[Ss]lice` in
  `AlgebraicTopology/Quasicategory` returned zero hits. The project grep found
  the existing `rightVertexSlice`; it is used through the landed slice-arrow
  dependency, while the downstream `kanSlice` helper is deliberately unused.
* `rg` of upstream `WeilConjectures` and `dag/lean_names_upstream.json` found no
  occurrence of the item's id or any proposed declaration name. `rg` of
  `lean/Sheaf` found the dependency notions but no existing statement of this
  item. `tools/blueprint_refs.py search opposite` and `search slice`, together
  with DAG searches for slice/coslice statements, found no independent
  opposite-duality theorem already giving this item.

Read the online primary sources [Kerodon 02X4](https://kerodon.net/tag/02X4),
[02XT](https://kerodon.net/tag/02XT), [02XV](https://kerodon.net/tag/02XV), and
[02KG](https://kerodon.net/tag/02KG). They supply respectively natural-equivalence
invariance, exact extension along a cofinal index map, the distinguished-edge
criterion, and the relative-limit convention. The node's use is the specified
index-equivalence specialization and its colimit/opposite dual. No source-based
statement correction was needed.

### Validation

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q32
lem-coef-infinity-relative-cone-equivalence
<the sandbox module>` passes for the module both as sandbox input and by its
library name. No errors or warnings. Every line is at most 100 characters.
The first check exposed a reducibility-sensitive left-join simplex cast and
independent universe arguments in a dependency theorem; both were repaired
without restricting any mathematical universe or adding hypotheses.

## Earlier second reading (a previous round; superseded)

I independently opened the item's repository node and sandbox node, the complete
Lean module, the four original statement-dependency records and their source
modules, and the added isofibration and slice-arrow dependency records and sources. There is no
repair note for this item, no `statement_change`, no new node and no dependency
module in this delivery. The source identifiers are Kerodon identifiers, not
Stacks tags: the node explicitly directs online reading and has no archived
Stacks `.tex` source. I read [02X4](https://kerodon.net/tag/02X4),
[02XT](https://kerodon.net/tag/02XT), [02XV](https://kerodon.net/tag/02XV),
[02KG](https://kerodon.net/tag/02KG), the surrounding
[7.1.6](https://kerodon.net/tag/02KF),
[02X1](https://kerodon.net/tag/02X1), [01TB](https://kerodon.net/tag/01TB),
and [4.6.5](https://kerodon.net/tag/01KW).
Their ambient hypothesis is a functor between quasicategories. Inner lifting
is required for strict existence and the edge criterion, but not for natural
invariance or opposite duality. The node deliberately specializes the source's
cofinal-map result to equivalences of quasicategorical indices; the Lean retains
that specialization. Source 02XV has apparent shape/name typographical slips
in its colimit bullet; the explicitly stated right cone in the node and Lean
agrees with its displayed distinguished right-cone edge.

My object/hypothesis/conclusion checklist, matched with the Lean:

1. **Common objects and universe.** `SSet.{u}`, `Quasicategory`,
   `AreNaturallyEquivalent`, `IsFunctorEquivalence`, `IsEquivalenceEdge`,
   `mappingSpace`, and `mappingSpaceMap` render the node's specified notions.
   I read their signatures and bodies in `EnhancedDiagramsCones`, rather than
   inferring their meaning from their names. In particular, equivalences have
   both inverse triangles, and mapping simplices have the entire initial face
   constant. `IsRelativeColimitDiagram` and `IsRelativeLimitDiagram` are the
   dependency's outgoing/incoming mapping-square tests for every comparison
   diagram. `homotopyPullbackComparison` uses the constant path in the existing
   path pullback. Verdict: exact objects, with no alternative universality test.
2. **Clause (1): arbitrary shape.** `RelativeColimitNaturalInvariance` binds
   `M D B : SSet.{u}` and only `[Quasicategory D] [Quasicategory B]`, then
   `p`, `q`, `q'`, and the natural-equivalence implication. Its consequent is
   the biconditional of the two relative-colimit predicates. Verdict: exact;
   neither an inner-fibration hypothesis nor a quasicategory hypothesis on `M`
   has slipped in.
3. **Clause (2): hypotheses.** `RelativeColimitIndexInvariance` binds four
   quasicategories, `p` with `[InnerFibration p]`, and `e : L ⟶ M` with
   `IsFunctorEquivalence e`. The prescribed maps are `f : M ⟶ D` and
   `g : rightJoinCone M ⟶ B`, with
   `f ≫ p = rightJoinConeInclusion M ≫ g`. Verdict: exact and in the right order.
4. **Clause (2): existence.** The first existential has the three clauses
   `rightJoinConeInclusion M ≫ q = f`, `q ≫ p = g`, and universality.
   The second has boundary `e ≫ f`, base `relativeRightConeMap e ≫ g`, and
   universality. `relativeRightConeMap` is the existing join bifunctor applied
   to `(e, 𝟙 Δ[0])`. Verdict: both directions preserve exactly prescribed
   maps, including the apex; no replacement by equivalent maps.
5. **Clause (2): each particular diagram.** The second conjunct separately
   quantifies over every `q` and asserts universality iff universality of
   `relativeRightConeMap e ≫ q`. Verdict: exact; not merely an existence result.
6. **Clause (3): final object and edge.** `RelativeColimitFinalEdge` binds
   `t : M _⦋0⦌`, `IsTerminal M t`, a particular `q`, and its universality.
   `relativeCoconeEdge q t` applies `q` to the join generator of `t` followed
   by the point. Reading `joinGenerator`, `orderedJoinFunctor` and the pure
   inclusions confirms its source is `q(t)` and its target the apex.
   `IsCocartesianEdge p (yonedaEquiv.symm ...)` uses the exact dependency's
   initial outer-horn condition with edge `{0,1}`. Verdict: exact.
7. **Clause (3): equivalence implication.** The second conjunct assumes
   `IsEquivalenceEdge B (p.app _ (relativeCoconeEdge q t))` and concludes
   `IsEquivalenceEdge D (relativeCoconeEdge q t)`. Verdict: exact same edge and
   its actual image, not an arbitrary equivalent edge.
8. **Clause (4): opposite operation and closure.** Mathlib `SSet.opFunctor`
   is precomposition with `SimplexCategory.rev`. I read `Op.lean` and `Rev.lean`:
   its operator is `(α i.rev).rev`, exactly the node's formula.
   `RelativeConeOppositeDuality` existentially asserts `hOp` for all
   quasicategories; the next conjunct preserves `IsIsofibration`. I read that
   predicate: it includes both quasicategory conditions, inner lifting, and
   exact lifting of an equivalence at a specified source. Verdict: exact;
   opposite closure is concluded, not assumed from the caller.
9. **Clause (4): mapping equivalences and naturality.**
   `RelativeOppositeMappingSpaces hOp` gives a family of isomorphisms from
   `Map(D.op,x,y)` to `Map(D,y,x)` in the existing weak-equivalence localization
   of Kan complexes. The naturality equation uses the actual induced
   `mappingSpaceMap` for every functor and both transported vertices.
   `relativeConeMappingObject` supplies Kan proof data from the recorded
   functor-cone calculus; the underlying mapping object is fully constructed.
   Verdict: exact to the dependency's convention of spaces up to weak homotopy
   equivalence; no false strict equality between the two pinch models.
10. **Clause (4): canonical cone comparison.** The family `e M` compares
    `(leftJoinCone M).op` and `rightJoinCone M.op`.
    `RelativeConeReversalFormula` fixes the whole base, the apex, and every
    apex-adjoined simplex. Every mixed simplex with repeated apex vertices is
    a restriction/degeneracy of one of these generators. Verdict: the asserted
    isomorphism is the canonical block reversal, not an unconstrained witness.
11. **Clause (4): limit/colimit equivalence.** For every arbitrary `M`,
    quasicategories `D B`, functor `p` and left-cone diagram `q`, the assertion is
    `IsRelativeLimitDiagram p q ↔ IsRelativeColimitDiagram (opFunctor.map p)
    ((e M).inv ≫ opFunctor.map q)`, with the opposite quasicategory proofs
    supplied by `hOp`. Verdict: correct direction of the comparison and exact
    quantification; no fibration condition or shape restriction added.
12. **Clause (4): complete slice reversal.** `RelativeOppositeSlices` uses
    the real-data `firstVertexCoslice C c :=
    (rightVertexSlice C.op (opObjEquiv.symm c)).op` and the existing
    `rightVertexSlice C.op (opObjEquiv.symm c)`. I read the full
    `SliceArrowEquivalence` source, including the endpoint and operator formulas.
    The asserted equality fixes the entire stored `(n+1)`-simplex in every degree;
    its remaining face and canonical prism are restrictions and are fixed too.
    Verdict: exact complete slices and canonical cones, not just vertex sets.
    The downstream `KanMappingRestriction` theorem is neither imported nor used,
    so the returned import cycle is removed.
13. **Dual (1).** `RelativeLimitNaturalInvariance` keeps arbitrary `M`, the
    same coherent-equivalence hypothesis and the biconditional on left cones.
    Verdict: exact full dual.
14. **Dual (2).** `RelativeLimitIndexInvariance` repeats both exact-existence
    clauses with left inclusions and `relativeLeftConeMap`, then the assertion
    for every particular left-cone diagram. Verdict: exact full dual, including
    the prescribed boundary and base.
15. **Dual (3).** `RelativeLimitInitialEdge` binds `IsInitial M t`, uses
    `relativeConeEdge q t` from the apex to `q(t)`, asserts the dependency's
    final outer-horn `IsCartesianEdge`, and gives the same image-equivalence
    implication. Verdict: exact full dual.

Edge cases checked independently: an empty `M` is allowed in (1), (4), and the
natural-invariance dual; its join cone is the point, and the pure-apex equation
still fixes reversal. Empty quasicategories are allowed as either index in (2);
there is no `Nonempty` binder or chosen index vertex. Clause (3) requires the
actual final/initial vertex and makes no claim when none exists. For `M = Δ[0]`
the displayed generator is the distinguished edge. Degree zero is explicitly
included in both cone and slice formulas; repeated apex vertices are retained.
For empty `D`, existence of a cone diagram already fails, so there is no hidden
inhabitation assertion. Mapping spaces may be empty, even with specified
endpoints. Taking `p` to be the identity or the map to a point recovers the
relative tautological case or the ordinary universal case respectively, with
unchanged hypotheses. Zero objects, schemes and coefficient characteristics do
not occur in this simplicial statement. A single arbitrary `universe u` is the
node's fixed sufficiently large universe and excludes no small shape in it;
there is no object/morphism-universe equation. Explicit universe arguments in
the Kan proof fix only theorem instantiation. All binders are explicit and
`autoImplicit` is false.

I made fresh searches with different wording through the prescribed wrapper:

* LeanSearch: `Quasicategorical cocone universality preserved by coherent
  isomorphisms and restriction along a categorical equivalence`. Eight hits,
  including `IsUniversalColimit.precompose_isIso`, `IsColimit.mapCoconeEquiv`
  and `IsUniversalColimit.whiskerEquivalence_iff`. Their returned signatures
  concern ordinary categories, so none is this relative-quasicategory theorem.
* Loogle: `"SSet.opFunctor"`. Five hits, including the actual opposite functor,
  its involution isomorphism and its degreewise map formula. Read and reused
  these; none states the relative cone or slice result.
* Mathlib grep: `cocone.*[Ee]quiv|[Oo]pposite.*[Ss]lice|[Rr]elative.*[Uu]niversal`.
  The displayed hits concern ordinary cocones or unrelated simplicial colimits.
  Direct `rg` in Mathlib's AlgebraicTopology tree, upstream `WeilConjectures`,
  project `lean/Sheaf`, and `dag/lean_names_upstream.json` checked the proposed
  names and the concepts `IsRelativeColimitDiagram`, `IsRelativeLimitDiagram`,
  opposite slice, and relative universality. The relevant project hits are the
  dependency definitions already used; upstream relative presentations are
  ordinary-category constructions. There is no exact existing statement and
  no duplicated helper definition.

Mismatch and repair: the mathematical statement, helpers, dependency interfaces,
and node signature need no correction. The import inventory omitted four
currently recorded proof-dependency modules. I added non-public imports of
`KanHomotopyPullbackInvariance`, `JoyalQuasicategoryCharacterizations`,
`SubdivisionLastVertexEquivalence`, and `KanRealizationSerre`, following
stage-2 rule 7. Original statement dependencies remain publicly available
through the existing public imports. The worker report's earlier import
inventory is superseded by this check. No node statement or theorem signature
changed. The extra `stmt_deps` entries are the already landed owners of
`IsIsofibration` and `rightVertexSlice`, which the main statement uses and §5 permits adding.

Every one of the nineteen helper definitions has real data or an explicit
logical predicate. There is one theorem and its whole proof is `sorry`.
All declaration docstrings identify the source and this blueprint id; the
main docstring follows all nine proof steps with their prerequisites. No
private declaration, file-local notation, additional assumption, or unbound
universe was introduced. The node's `lean.statement` remains verbatim equal
to the theorem signature. All source lines are at most 100 characters.

Validation after my import repair: the prescribed `scompile.py Q32
lem-coef-infinity-relative-cone-equivalence <module>` completed successfully
for both sandbox input and library-name compilation, with no errors or warnings.
The two needed overlay modules were individually compiled by the wrapper too.

## Repair of returned delivery

The returned H2/H4 defect was repaired by removing `KanMappingRestriction` and every
`kanSlice` reference. I added the landed `lem-coef-infinity-slice-arrow-equivalence`
to `stmt_deps`, imported `Sheaf.CategoryTheory.SliceArrowEquivalence`, and added the
real-data declaration `firstVertexCoslice`. It is defined as the opposite of
`rightVertexSlice C.op (opObjEquiv.symm c)`, while `RelativeOppositeSlices` uses
that `rightVertexSlice` directly for `(C^op)_{/c}`. The node lean record now lists
this helper and the new dependency, and its note records why the downstream module
cannot be reused. The cycle path `KanMappingRestriction → RelativeKanExistence →
RelativeConeEquivalence` is absent from the import graph.

The repaired module was compiled with `scompile.py`; it completed with no errors or
warnings.

### Repair retry validation

The retained repair was compared with the current shared DAG snapshot without Git
operations. The current base has no landed `RelativeConeEquivalence` module or Lean
record for this item. I refreshed the node from that base and retained only the
authorized `lean` and `stmt_deps` changes, thereby preserving its updated audit
metadata. The theorem signature and all mathematical clauses remain unchanged.

The first-vertex helper's docstring now spells out its degreewise meaning: an
`n`-simplex stores a simplex of `C` in degree `n+1` whose first vertex is `c`.
The operator is obtained by conjugating `appendLast` by order reversal, so it
fixes that first vertex. At degree zero these are the arrows with source `c`.
Taking the opposite twice recovers the upstream last-vertex slice. The existing
whole-simplex equation in `RelativeOppositeSlices` fixes the stored simplex
in every degree, including degeneracies, and thus its remaining face and cone.
This helper belongs to this item's own opposite-comparison assertion, as allowed
by §1(A)'s helper rule; no independent definition node or postponed theorem is needed.

Renewed searches: LeanSearch for "simplicial first vertex coslice opposite of the
last vertex slice" returned eight simplicial/cosimplicial-opposite and indexing
hits, none a fixed-first-vertex slice. Loogle `"SSet", "slice"` returned zero hits.
Project and DAG searches found the upstream `rightVertexSlice` and the downstream
`kanSlice`, but no reusable upstream first-vertex helper. The latter cannot be
reused because its owner depends on this item through `relative-kan-existence`.
The slice-arrow owner's statement and proof dependencies were checked; they do
not include either downstream node.

## Second reading by Q32

This is a fresh reading of the retained repair against the current shared node.
I opened the complete module, all six statement-dependency records and their
Lean interfaces, and the current nine-step proof. No repair note exists.
The sandbox changes no node field except lean and the two added statement
dependencies described above. There are no new nodes, dependency modules,
or statement corrections to review.

The source is Kerodon, explicitly not a Stacks tag or an archived Stacks tex file.
I read [02X4](https://kerodon.net/tag/02X4),
[02XT](https://kerodon.net/tag/02XT), [02XV](https://kerodon.net/tag/02XV),
[02KG](https://kerodon.net/tag/02KG), and the surrounding discussion
[02KF](https://kerodon.net/tag/02KF), including the opposite convention in
[02KH](https://kerodon.net/tag/02KH). The ambient objects are quasicategories.
Natural invariance and opposite duality require no fibration; exact extension
and the distinguished-edge assertion require an inner fibration. The node is
explicitly the indexing-equivalence specialization of the cofinality result.
The colimit bullet of 02XV has shape/name typographical slips; its displayed
right-cone edge and the dual first bullet determine the right-cone convention
used in the node and Lean. No source-based correction of the node is needed.

My object, hypothesis, and conclusion checklist follows. Every verdict is exact.

1. Fixed universe and objects: universe u and SSet.{u} throughout.
   Quasicategory is the existing horn predicate. I read the signatures and data
   for mappingSpace, mappingSpaceMap, AreNaturallyEquivalent,
   IsFunctorEquivalence, and IsEquivalenceEdge in EnhancedDiagramsCones.
   Natural equivalence is an equivalence edge of the actual internal hom;
   functor equivalence has both coherent inverse witnesses.
2. Cones and universality: rightJoinCone, leftJoinCone and their inclusions
   are the existing terminally augmented ordered joins. I read
   IsRelativeColimitDiagram and IsRelativeLimitDiagram: they test outgoing
   and incoming mapping squares, respectively, against every comparison
   diagram, using the constructed constant path into the recorded path
   pullback. EnhancedFunctorConeCalculus provides only the Kan proof for
   relativeConeMappingObject; its underlying space is constructed data.
3. Clause (1): RelativeColimitNaturalInvariance binds arbitrary M,
   quasicategories D B, arbitrary p, and two right-cone maps. The coherent
   natural-equivalence hypothesis implies exactly the universality iff.
   No inner-fibration or quasicategory condition on M is added.
4. Clause (2), hypotheses: RelativeColimitIndexInvariance binds four
   quasicategories, p with InnerFibration, and e with IsFunctorEquivalence.
   Its prescribed f and g satisfy exactly f ≫ p = inclusion ≫ g.
5. Clause (2), exact existence: the first existential requires boundary f,
   base g, and universality; the second requires boundary e ≫ f, base
   relativeRightConeMap e ≫ g, and universality. The induced map is the
   existing ordered join on (e, identity), fixing the new vertex.
   Both directions preserve the prescribed maps exactly.
6. Clause (2), individual diagrams: the separate second conjunct quantifies
   over every q and states universality iff universality after the induced
   cone map. The existence equivalence alone would not cover this clause.
7. Clause (3), edge: RelativeColimitFinalEdge binds the actual vertex t,
   IsTerminal M t, and a particular universal q. relativeCoconeEdge q t
   applies q to the ordered-join generator of t followed by the apex, hence
   has source q(t) and target q(*). Its yonedaEquiv.symm is tested by the
   dependency's IsCocartesianEdge, fixing the initial edge {0,1}.
8. Clause (3), equivalence: the second conjunct tests exactly the image
   p.app _ (relativeCoconeEdge q t), and concludes equivalence of the same
   edge in D. There is no substituted comparison edge.
9. Clause (4), opposite: I read Mathlib's opFunctor and SimplexCategory.rev.
   Their operator formula is (alpha i.rev).rev, exactly the node's formula.
   RelativeConeOppositeDuality concludes quasicategory closure as hOp and
   concludes preservation of IsIsofibration. I read that predicate in its
   owning module: both quasicategories, inner lifting, and exact equivalence
   lifting at every specified source are included.
10. Clause (4), mapping spaces: RelativeOppositeMappingSpaces hOp asserts
    isomorphisms in the existing localization of Kan spaces, from the mapping
    space in D.op at transported x,y to that in D at y,x. The equality for
    every functor uses the actual mappingSpaceMap and transported endpoints.
    This is precisely the dependency's weak-homotopy convention for spaces,
    without an incorrect equality of different pinched models.
11. Clause (4), canonical join reversal: RelativeConeReversalFormula fixes
    the whole base, pure apex, and each apex-adjoined simplex under
    (leftJoinCone M).op ≅ rightJoinCone M.op. Restrictions of these generators
    include all mixed simplices, including repeated apex vertices, fixing
    the canonical comparison rather than an arbitrary cone automorphism.
12. Clause (4), universality: for arbitrary M and p between quasicategories,
    the left-cone limit predicate is equivalent to the opposite colimit
    predicate at (e M).inv ≫ opFunctor.map q. The inverse is correctly
    directed; opposite quasicategory instances come from the concluded hOp.
    No fibration hypothesis or shape restriction is added.
13. Clause (4), complete slices: firstVertexCoslice C c is constructed as
    the opposite of the recorded rightVertexSlice C.op at endpoint c.
    I read the latter's full subtype and appendLast operator definitions.
    Reversal gives exactly first-vertex-fixed simplices of C with the first
    vertex prepended to every operator. RelativeOppositeSlices fixes the
    stored (n+1)-simplex in every degree, hence its entire remaining face
    and canonical cone. This is real data, not an arbitrary category
    equipped with an assumed comparison.
14. Dual (1): RelativeLimitNaturalInvariance keeps arbitrary shape,
    arbitrary p, coherent equivalence, and the full iff.
15. Dual (2): RelativeLimitIndexInvariance uses left cones and the real
    relativeLeftConeMap, retaining both exact existence and the assertion
    for every particular diagram with the same quantifier order.
16. Dual (3): RelativeLimitInitialEdge binds an initial vertex, constructs
    the apex-to-vertex edge, asserts the recorded final outer-horn
    IsCartesianEdge, and includes the precise image-equivalence implication.

Edge cases: empty indices are allowed in (1), (2), (4), and their duals.
Their cone is the point and the pure-apex clause still fixes reversal;
no nonemptiness instance occurs. Clause (3) assumes an actual terminal/initial
vertex, so selects nothing in an empty category. Empty target quasicategories
and empty mapping spaces are not excluded. Degree zero occurs in both join
and whole-slice formulas; a singleton index yields exactly the distinguished
edge, and degeneracies retain repeated apex vertices. Identity p and the map
to a point recover the relative identity and ordinary universal cases.
There are no schemes, rings, characteristics, or zero-object hypotheses.
One arbitrary universe u is precisely the node's fixed universe; there is
no extra equality between independent site universes. All variables are bound.

Independent searches used different wording from the worker:

* LeanFinder: "Invariance of relative universal cocones under coherent
  equivalence and reversal of simplices". Eight hits, including
  Cocones.precomposeEquivalence and Cocones.whiskeringEquivalence, whose
  signatures concern ordinary categories and do not state this item.
* Loogle: "Quasicategory", "opFunctor". Zero hits.
* Mathlib grep: colimit.*[Oo]pposite|[Cc]one.*[Ii]nvariance|firstVertexCoslice.
  The returned hits concern ordinary-category colimits and opposites.
* Direct rg in the named Mathlib AlgebraicTopology tree, upstream
  WeilConjectures, and project lean/Sheaf checked helper names, relative
  limits/colimits, and opposites. Only recorded dependency notions and
  downstream users occur. I read SimplicialSet/Op.lean and
  SimplexCategory/Rev.lean; their existing opposite is used directly.
  The downstream KanMappingRestriction cannot be imported: its node depends
  on this item through relative-kan-existence. No exact existing statement
  or reusable upstream first-vertex helper was found.

Mismatch and repair: the current proof dependency list now records
QuasicategoryInvertibleInterval and EquivalenceAnodyneFactorization, but
the module lacked their imports. I added both non-public imports. I also
made the original statement dependencies EnhancedDiagramsCones and
EnhancedFunctorConeCalculus direct public imports rather than relying on
transitive availability. The mathematical predicates, helper data, theorem
signature, and node statement are unchanged. An apparent duplicated doc-comment
in my initial display was only overlapping read ranges, not a file defect.

I checked every declaration's source/blueprint docstring and all nine
proof-plan steps. There are nineteen real-data/predicate helpers and one
theorem whose entire proof is sorry; no hollow data, extra postponed theorem,
file-local notation, private declaration, or unbound universe occurs.
Every Lean line is at most 100 columns. The node's lean.statement is
byte-identical to the signature before its proof.

The prescribed scompile.py already passed for the sandbox and library forms,
including the EquivalenceAnodyneFactorization overlay, with no errors or
warnings. Final compilation and delivery preflight are recorded below.
