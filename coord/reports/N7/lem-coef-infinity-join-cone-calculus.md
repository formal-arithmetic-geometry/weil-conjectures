## Worker report

The module `lean/Sheaf/CategoryTheory/InfinityJoinConeCalculus.lean` states
`SSet.Enhanced.infinity_join_cone_calculus`, with its sole proof `sorry`.
All helpers have constructed data. No other DAG statement is restated. The node's
mathematical statement is unchanged. Its `stmt_deps` gains four already landed
nodes whose constructions occur in the signature or its definitions, as permitted
by brief-stage2 §5 (STMT_DEPS MAY GAIN LANDED NODES).

The proof docstring gives all eight DAG proof steps. The library does not yet state
`lem-coef-infinity-cellular-natural-equivalence`,
`lem-coef-infinity-isofibration-base-change`, or
`lem-coef-infinity-isofibration-exponentiation`; these proof-only imports are
therefore omitted. They are not prerequisites for typing the statement.

Clause-by-clause correspondence:

| Node clause or hypothesis | Lean rendering |
| --- | --- |
| Any small simplicial set K and quasicategory E in a sufficiently large universe | `K E : SSet.{u}` and `[Quasicategory E]`, with explicit arbitrary universe `u`. Shapes and coefficient categories may be lifted to their common sufficiently large universe. No nonemptiness, finiteness or strict-Segal assumption occurs. |
| Left ordered join cone, with apex before K | Existing `orderedJoinFunctor.obj (Δ[0], K)`, `orderedJoinInl Δ[0] K`, and `orderedJoinInr Δ[0] K`. The terminally augmented convolution's pure and mixed simplex formula is documented in its owning module. No second join or second leftJoinCone definition is introduced. |
| Fat cone collapses K × {0}; boundary is K × {1} | `fatLeftJoinCone K` is the actual pushout of `K → Δ[0]` and `coneCylinderEnd K 0`; the cylinder end 1 is retained. |
| Natural collapse, splitting the initial zeros from the final ones | The existential family `κ` has conclusion `IsJoinConeCylinder K (κ K)`. That predicate fixes both pure ends and every mixed simplex: `coneSplitInterval a b`, `coneFinalBlock a b`, and `coneMixedSimplex K a b k`. Every nonconstant monotone interval simplex has exactly these two nonempty blocks; the end equations cover the two constant cases. Hence the cylinder map is uniquely prescribed, rather than an arbitrary comparison. |
| Collapse descends from fat cone | Family `d` has `pushout.inl ≫ d = orderedJoinInl` and `pushout.inr ≫ d = κ`. These jointly determine the pushout map, including empty K. |
| Fun(T_K,E) is the varying comma object | Family `i` is an actual simplicial isomorphism to `varyingCone K E`, characterized by its apex and entire coherent-arrow projections. `varyingCone` is the ordinary simplicial pullback of `constantDiagrams K E` along initial-end evaluation. Its objects are exactly `(x, λ:Δ_K x → F)` with unrestricted final endpoint F. |
| Comparison induced by precomposition with the collapse | Family `c` satisfies `c = pre(d).app E ≫ i.hom`, and its arrow projection equals the twice-curried cylinder family. These equations specify its actual construction. |
| Comparison is an equivalence | `IsFunctorEquivalence (c K E)` uses the dependency's quasi-inverse and coherent inverse-equation definition. |
| Comparison commutes with the joint vertex/boundary projection | `w : c K E ≫ varyingConeJoint K E = joinConeJoint K E`. The two joint maps have exactly the stated apex and whole boundary restrictions. |
| Every ordinary pullback along a quasicategory R → E × Fun(K,E) | Universal `(R : SSet.{u}) [Quasicategory R] (h : R ⟶ E ⊗ (ihom K).obj E)` and equivalence of `coneComparisonBaseChange ... w h`. The construction uses actual `pullback` and its canonical induced map. Symmetry of the two pullback factors identifies its convention with the displayed R-first convention. |
| Boundary, apex, or both fixed | These are specializations of that universal h, respectively from E × {F}, {x} × D, or Δ[0], exactly as in the DAG proof. No distinct specialization is assumed or omitted. |
| Every small product with the product joint projection | The universal product clause uses `α : Type u`, arbitrary `K E : α → SSet.{u}`, a quasicategory proof for every E a, categorical `Limits.Pi.map` for the comparisons and joint projections, and every h into the product base. There is no finite or inhabited-index restriction. |
| Two cone objects, including varying F and G | The final clause quantifies all `X Y : (varyingCone K E) _⦋0⦌`. Their x,y,F,G,λ,μ are the actual projections, not independent untyped edges. The quasicategory structure of `varyingCone` is asserted as a conclusion, not a hypothesis. |
| Mapping-space homotopy pullback | `coneMappingPath K E X Y` pulls back the existing `arrowSquarePathEndpoints` along `coneMappingEndpoints`. `ArrowSquareSpanPresentation D λ μ` explicitly identifies the existing two-triangle model with the literal path-space homotopy pullback of its canonical composition spans. Their free projections are weak equivalences, their long edges represent composition. Thus this is the full homotopy pullback, not the strict equation bλ = μΔa or a pullback of components. |
| Maps to the cross mapping space | `coneMappingEndpoints` sends a to the canonical pinch of `mappingSpaceMap (constantDiagrams K E) ... a`, and b to its canonical pinch; the upper fixed-leg triangle then has long edge μΔa and the lower triangle bλ. `ArrowSquareCompositionSpan.free_eq` and `.long_eq` from the existing owner specify those compositions. No unrelated map or strict composition is assumed. |
| Path orientation and factor order in the display | The reused arrow-square path model lists `(a,b)` and paths μΔa → bλ. Swapping the two product coordinates and reversing that path identifies it with the node's `(b,a)` and path bλ → μΔa. This is symmetry of the full space-valued homotopy pullback, including all higher simplices; the DAG proof step 7 explicitly makes the same reversal. |
| Equivalence on the prescribed mapping spaces | `v : mappingSpace (varyingCone K E) X Y ⟶ coneMappingPath K E X Y` is a weak homotopy equivalence in the dependency's realization-based sense. Its triangle projection is specified by the canonical pinch `conePointPinch`, the uniquely specified fixed-endpoint isomorphism `j`, and the relative comparison q. |
| Actual projection to Map_D(F,G) | `v ≫ pullback.snd = lift (mappingSpaceMap apex X Y) (mappingSpaceMap boundary X Y)`. After the second coordinate projection this is exactly `mappingSpaceMap (varyingConeBoundary K E) X Y`, with the prescribed right-pinched target. `coneMappingPathBoundary` names that projection. |
| Naturality in K and E | The collapse family satisfies the explicit shape-map equation. The c-naturality clause universally takes f:L→K and g:E→E′, supplies the uniquely specified comma map s, and gives the strict comparison equation with join restriction and postcomposition. All three comma projections are specified. |
| Naturality in both objects, with higher compatibility | Family q is defined for every simplicial parameter T and every U,V:T→varyingCone; `coneSquareFamily` fixes entire endpoint slices and `coneSquarePath` retains the same parameter, two arrows, two triangles and whole path. `IsConeSquarePathEquivalence` gives an inverse and both homotopies over T. `ConeSquarePathNaturality q` explicitly asserts naturality under every change of parameter and compatible ambient maps (including `Δ_K ≫ g = f ≫ Δ_L`), with all data and triangle projections. Universal families include coherent composable strings; their restrictions and degeneracies retain higher object compatibility. |
| Naturality of the mapping comparison with the boundary restriction | q preserves the actual boundary arrow in `coneSquareDataAmbient`; its naturality equation retains this coordinate. The point formula's v is characterized by this q and its actual two right-pinched endpoint maps. |

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.mappingSpace`,
  `mappingSpaceMap`, `evaluation`, `constantDiagrams`, `IsFunctorEquivalence`,
  `IsWeakHomotopyEquivalence`; Mathlib's `SSet`, `stdSimplex`, `Quasicategory`,
  tensor product, internal hom, ordinary simplicial pullback/pushout and products.
- `Sheaf.CategoryTheory.SimplicialCompositionSpine`:
  `SSet.Enhanced.simplicial_composition_spine`, its `multiarrowSpace`,
  `spineRestriction`, `SpineSectionFamily`, `spineComposition`, and
  `HasCoherentComposition` interfaces were read. This required dependency remains
  publicly imported as the coherent composition interface underlying the spans;
  independently chosen binary sections are never made part of the statement.
- `Sheaf.CategoryTheory.JoinSliceRightFibration`: `joinGenerator`,
  `orderedJoinInl`, `orderedJoinInr`, and their full docstrings/signatures.
  Its upstream `Sheaf.AlgebraicTopology.PushoutJoinSaturation` supplies
  `orderedJoinFunctor` and terminal `joinAugmentation`.
- `Sheaf.CategoryTheory.ArrowMorphismSquare`: `arrowSquarePathFamily`,
  `arrowSquarePathBase`, `arrowSquarePathEndpoints`, `arrowSquareRestriction`,
  `arrowSquareUpper`, `arrowSquarePathAmbientMap`, `ArrowSquareCompositionSpan`,
  `ArrowSquareSpanPresentation`, and `arrow_morphism_square`. The mixed mapping
  formula is built from these precise source-defined restrictions, not a private
  composition notion.
- `Sheaf.CategoryTheory.RightPinchComparison`: `arrowMappingSpace`,
  `arrowMappingSpaceInclusion`, and `right_pinch_comparison`. Choices made from
  that theorem are its uniquely prism-characterized pinch map; no arbitrary data
  are chosen from mere existence.
- `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`:
  `enhanced_functor_cone_calculus.{u,u,u}` supplies only the proved/proof-postponed
  quasicategory assertion for the already constructed internal hom. All three
  universe levels are explicit; no new closure theorem is stated here.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper` is privately imported for its
  already recorded proof dependency, as the stage requires.

Edge cases checked before and after drafting:

- K empty: the fat cone and ordered join are points; no mixed-simplex condition
  remains. The comparison, base-change assertion and point formula still type.
- K=Δ[0]: fat cone is the interval; the comma object is the arrow object with its
  source retained, and the mapping formula reduces to the existing arrow-square
  formula.
- In degree zero an interval simplex is constant; the two end equations cover it.
  In degree r>0 every nonconstant interval simplex has positive initial and final
  block sizes, hence occurs as r=a+b+1. Repeated apex and boundary vertices remain
  part of the normal-form generator, so no degeneracies are lost.
- Empty coefficient quasicategory and empty mapping spaces are allowed. No point,
  morphism, nonempty component, or inverse homotopy is required without its
  quantified source data.
- The empty product is allowed (`α` unrestricted); there is no use of Finset,
  Fintype, finite products only, or Nonempty α.
- Base change permits all quasicategories R and all h; identity h recovers the
  original comparison, and constant h gives simultaneous endpoint fibers.
- Universes are explicitly bound with `autoImplicit false`. No equality of
  unrelated site universes and no strict ordinary-category replacement occurs.

Searches (performed before writing):

- `msearch.py ... leanfinder`: "Join cones in a quasicategory are equivalent to
  coherent comma categories and mapping spaces are homotopy pullbacks".
  Eight results: ordinary nerve quasicategory, ordinary Over-category cone
  equivalences and strict-Segal extension declarations. None states this node.
- `msearch.py ... loogle`: "SSet, join, cone". No match; join unknown identifier.
- `msearch.py ... grep`: "join|Join|fatCone|FatCone|homotopyPullback" under
  AlgebraicTopology. Twenty-five unrelated join-text/adjunction/model-category
  hits; no fat-cone comparison.
- `msearch.py ... leansearch`: "An infinity category left join cone and fat cone
  yield equivalent functor categories with varying boundary mapping spaces".
  Eight ordinary category cone, categorical join and final-functor results;
  none is the coherent varying-boundary assertion.
- `rg` in Mathlib SimplicialSet for join/Join found no ordered simplicial join.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for
  `fatCone|fatJoin|FatJoin|leftCone|LeftCone|orderedJoin|join_cone|homotopyPullback`
  found the existing join implementation, join inclusions, `RelativeInfinityCone`
  and `SourceAttachmentGluing`; no statement equivalent to this item.
- `grep -rn 'lem-coef-infinity-join-cone-calculus'` in upstream WeilConjectures
  returned no match. No upstream declaration binds this blueprint item.
- The read-only DAG traversal found a dependency path from
  `def-coef-infinity-relative-cone` through `lem-coef-infinity-source-gluing`
  back to this item. Consequently the downstream `leftJoinCone` alias and named
  homotopy-pullback helper are not imported. This module uses the existing ordered
  join expression and the existing arrow-square path model directly; it creates
  no second left-join notion or homotopy-pullback definition. The four added
  landed statement dependencies have no dependency path back to this item.

Sources opened online: [Kerodon 05YH](https://kerodon.net/tag/05YH),
[01KG](https://kerodon.net/tag/01KG), and [03PM](https://kerodon.net/tag/03PM).
The comparison, joint isofibration and ordinary pullback claims agree with those
sources. The varying-boundary computation uses the already recorded interval
arrow-square foundation, exactly as the node's source qualification requires.

Validation: `scompile.py N7 lem-coef-infinity-join-cone-calculus
lean/Sheaf/CategoryTheory/InfinityJoinConeCalculus.lean` passed both the sandbox
and declared-library-module checks, without errors or warnings. The file has
one theorem, with `sorry`; helper data contain no `sorry`. No statement dispute,
statement correction, new node or dependency module is needed.

Additional exact-name search in `dag/lean_names_upstream.json`, upstream
WeilConjectures and Mathlib AlgebraicTopology for `infinity_join_cone_calculus`,
`IsJoinConeCylinder`, `coneMappingPath`, and `varyingCone` found no collisions.

Self-check of the generalized naturality interface added its explicit
constant-diagram square `constantDiagrams K E ≫ g = f ≫ constantDiagrams L E′`.
The intended shape restriction/postcomposition maps satisfy precisely this square;
it prevents unrelated ambient maps from entering the stronger family interface.

Also opened [Cisinski CatLR](https://cisinski.app.uni-regensburg.de/CatLR.pdf),
4.2.1--4.2.3 (printed pp.144--146, PDF pp.159--161) and the proof of 7.4.11
(printed pp.364--365), and [Kerodon 06BZ](https://kerodon.net/tag/06BZ).
Cisinski's initial/final-block collapse is exactly `coneMixedSimplex`, with X a
point. Kerodon 06BZ describes the Hom pullback as an equivalence of functors on
both objects, matching the parameterized naturality interface here.

## Second reading by N7

I independently opened the node statement, its source qualification, the sandbox module,
and each recorded statement dependency. The item-by-item verdict is:

1. The node's small simplicial set `K` and quasicategory `E` in one sufficiently large
   universe are rendered by `K E : SSet.{u}` and `[Quasicategory E]`; no finiteness,
   nonemptiness, characteristic, or extra algebraic hypothesis is present.
2. The left join `K^{\\triangleleft}` and its apex/boundary inclusions are rendered by
   `orderedJoinFunctor.obj (Δ[0], K)`, `orderedJoinInl Δ[0] K`, and
   `orderedJoinInr Δ[0] K`, using the recorded ordered-join dependency.
3. The fat cone `T_K` is the actual pushout `fatLeftJoinCone K` of the zero cylinder end;
   the retained copy of `K` is the one end of `coneCylinderEnd K 1`.
4. The collapse and its naturality are rendered by the family `κ`, the predicate
   `IsJoinConeCylinder` (both pure ends and every mixed simplex), and the explicit
   equation `(f ⊗ₘ 𝟙 Δ[1]) ≫ κ L = κ K ≫ orderedJoinFunctor.map (𝟙 Δ[0], f)`.
5. Descent through the fat-cone pushout is rendered by `d` and its two `pushout.inl` /
   `pushout.inr` equations. This covers the empty `K` case.
6. The functor-category comparison is rendered by the isomorphism `i` to `varyingCone`,
   with its apex and full coherent arrow projections specified. The comparison `c` is
   explicitly `MonoidalClosed.pre (d K) ≫ (i K E).hom` and its arrow equation is stated.
7. Equivalence and strict compatibility with the joint vertex/boundary projection are
   rendered by `IsFunctorEquivalence (c K E)` and `w : c K E ≫ varyingConeJoint =
   joinConeJoint`.
8. Every ordinary simplicial pullback over a quasicategory `R` is rendered by the
   universal `R` and `h` clause using `coneComparisonBaseChange`; endpoint-fixed cases
   are its specializations, with no added assumptions.
9. The arbitrary small product clause is rendered by `α : Type u`, pointwise `K E`,
   `Limits.Pi.map`, and an unrestricted product-base map `h`; the empty product is
   allowed.
10. The mapping-space clause quantifies both actual cone objects `X Y`, asserts the
    quasicategory structure of `varyingCone`, and uses `coneMappingPath` together with
    `ArrowSquareSpanPresentation`. Its endpoint maps are the canonical pinch maps, so
    the full higher homotopy pullback is retained; it is not a strict equality or a
    pullback of homotopy classes. The reported `(a,b)` versus `(b,a)` order is exactly
    the symmetry/reversal of the existing arrow-square path model.
11. Naturality in the shape, ambient quasicategory, and both cone objects is rendered by
    the explicit `s` equations, `ConeSquarePathNaturality`, and the parameterized `q`;
    the latter retains endpoint slices, triangles, paths, and both relative homotopies.

I found no mismatch between the node and Lean and made no statement correction. The
only changes relative to the base node are the recorded `lean` field and its four
landed statement dependencies, all of which are used by the signature. The dependency
modules were checked at their declarations: the ordered join, arrow-square path and
span presentation, pinch comparison, and functor-cone quasicategory calculus are the
same notions cited by this module; no private duplicate is introduced.

Edge cases rechecked: `K = ∅`, `K = Δ[0]`, degree zero and mixed interval simplices,
empty mapping spaces, empty product index, identity/base-change maps, and all stated
universes. The source places (Cisinski 4.2.1--4.2.3 and Kerodon 05YH, 01KG, 03PM,
06BZ) agree with the collapse, joint projection, base-change, and varying-boundary
clauses. The Mathlib, upstream, and project searches recorded above found no existing
statement or declaration. Recompilation with `scompile.py` passed sandbox and library
checks with only the intended theorem `sorry`.
