## Worker report

NF states `lem-coef-cone-apex-cocone-space-comparison` in
`Sheaf.CategoryTheory.ConeApexCoconeSpaceComparison`, namespace
`SSet.Enhanced.ConeApex`. The sole mathematical theorem is
`cone_apex_cocone_space_comparison`; its proof is `sorry` and its docstring follows
all eight proof steps. No definition contains `sorry`, a choice from an unspecified
existence theorem, or an arbitrary replacement for a canonical map.

The node statement is unchanged. The additional statement dependencies are already
landed owners of interfaces that appear in the signature: enhanced functor/cone
calculus, the right-pinch comparison, and coherent-cube invariance. No dependency
record is repaired and no new node is introduced. The structures in this module
package the comparison belonging to this node; their mathematical fields are
conclusions supplied by the theorem, never extra assumptions on its inputs.

### Hypotheses and objects

- Arbitrary small simplicial indexing sets are `K L : SSet.{u}`. Neither is assumed
  a quasicategory, a nerve, inhabited, finite, or nonempty.
- The fixed containing universe is the explicit universe `u`; `C D : SSet.{u}`
  have precisely `[Quasicategory C] [Quasicategory D]`.
- The target functor is any simplicial map `q : C ⟶ D`, with no fibration assumption.
- The diagram is any `c : rightJoinCone K ⟶ C`. Its base is the literal composite
  `rightJoinConeInclusion K ≫ c`; `apex c` is its value on the right pure-factor
  vertex, so the statement never has to choose a vertex of an empty space.
- `Contraction` specifies the ordered-block contraction, its two endpoints, fixed
  apex, compatibility with every shape map, and its boundary's exact
  `bluntSharpCylinderSimplex` formula. `eta H c` is its actual curry. Its restriction
  to `K` is the induced coherent cocone gamma; `CompositionModel.source/target`
  specify the endpoints. The boundary normalization identifies it with the cocone
  obtained from the given sharp cone, not a freely chosen transformation.
- Vertices `W : C _⦋0⦌` are universally quantified in `Comparisons`, and in the
  Kan/equivalence conclusions of `CompositionModel` and `Model`. The lower apex is
  exactly `q.app _ W`.

### Conclusions, clause by clause

1. The strict sharp apex fibers are exactly
   `(calculusFiber (joinCoconeProjection d) W).toSSet`, using the dependency's
   all-simplex strict fiber, not a homotopy fiber. `CompositionModel.kanSharp`
   asserts Kan for both the whole and base diagrams; the global family of models
   applies equally to their images in `D`.
2. `Model.sharpRow` is the displayed restriction row. `sharp_formula` prescribes
   precomposition of the entire sharp extension by the induced join inclusion;
   `sharp_over` preserves the apex. `NaturalMap.sharp_left/sharp_right` prescribe
   postcomposition by `q` and shape restriction in every degree. `RowMap.comm`
   supplies strict commutation, and `RowMap.square` takes precisely the strict
   apex fibers with the canonical constant commutation homotopy.
3. The second displayed square is represented by the canonical span of composition
   triangles. For an edge `e : d → Delta(x)`, `triangles x e` contains an actual
   retained arrow `alpha : x → W` and a whole triangle in `Fun(L,C)`. Its `01` edge
   is exactly `e`, its `12` edge is exactly `Delta(alpha)`, and `triangleLong` is
   its `02` edge. Thus `Model.compositionRow`, with `e = gamma`, represents exactly
   `alpha ↦ Delta(alpha) gamma`, with the triangle specifying the composition
   homotopy. This is the triangle-span realization of the composition operation
   of the recorded `InfinityMappingComposition` interface; it imposes no strict
   choice of composition on right-pinched mapping spaces.
4. The left corner of that row has the equivalence span
   `mappingSpace C x W → arrowMappingSpace C x W ← triangle-fiber`.
   `apexPinch_formula` prescribes the first map by the existing right-pinch prism;
   `alpha_formula` prescribes the second by retaining the actual arrow. Their
   `*_weak` fields assert weak equivalence; both mapping models and the triangle
   fibers are Kan. The right corner has the canonical span
   `mappingSpace (Fun(L,C)) d (Delta W) → raw-cocone-fiber`, specified in every
   degree by `pinch_formula` and asserted weak by `pinch_weak`. Consequently the
   row has exactly the four mapping-space corners of the node, with the recorded
   mapping-space convention, through canonical weak-equivalence spans.
5. `Model.rawRow` uses the dependency's actual coherent cocone category.
   `sharpToRaw` uses the single global sharp-collapse comparison `cmp`, normalized
   by `IsJoinCoconeComparison`, all three collapse formulas, and
   `JoinCoconeComparisonNaturality`; `cmp_apex/cmp_weak` give its strict fiber
   equivalences. `apexEvaluation` is pinned by `apex_formula` to actual evaluation
   of the whole cocone path at the apex, and `apex_weak` asserts its equivalence.
   The whole-cone triangle retains the unit triangle at this same apex because
   `Contraction.apex` fixes it. Its `alpha` and long-edge projections therefore
   give the apex-evaluation corner equivalence through that retained triangle.
6. The equivalence of entire squares is the three-cube zigzag in `Comparisons`:
   sharp to raw, whole-cone triangles to raw, and whole-cone triangles to base
   composition triangles. `whole_weak` and `restriction_weak` assert the remaining
   left-corner equivalences. `triangle_raw` identifies the restricted long edge
   with the literal cocone restriction; `triangle_formula` retains the triangles
   themselves, not just their components.
7. Each `SquareComparison` has an actual `KanCoherentCube`, its four normalized
   corner maps, specified constant side homotopies in these strictly commuting
   models, the existing `CoherentPathModelComparison`, its weak equivalence, and
   a homotopy between the two comparison arrows. Thus the assertion compares the
   full path-space pullback comparison maps, not merely truth values of the
   homotopy-pullback predicate. The triangle coordinates retain the displayed
   composition homotopies when these squares are read through the canonical
   pinch spans.
8. Naturality in `q` and any `j : L ⟶ K` is simultaneous in `NaturalMap`, with
   `c' = coneMap(j) ≫ c ≫ q`. Its sharp, raw, whole-triangle and base-triangle maps
   are specified on every simplex, including the retained arrow, both triangle
   edges and the long edge. All four maps and the zigzag comparisons lie over the
   entire apex categories `C → D` before fibers are taken. This is coherent
   postcomposition in `W`: higher simplices of the variable-apex arrow/cocone
   categories and their triangle parameters remain in the data. It is not only a
   family of naturality statements on vertices. The coordinate formulas also
   force identity and composite target/shape maps to agree, so the specialization
   `j = identity` is the node's target-functor square and `q = identity` is its
   arbitrary-shape restriction comparison.
9. There are no colimit, initiality, terminality, fibration or nonemptiness
   hypotheses. All auxiliary Kan and weak-equivalence facts occur as conclusions
   of the existential model, rather than assumptions needed to use the theorem.

### Dependency declarations read and used

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.mappingSpace`,
  `mappingSpaceMap`, `diagramVertex`, `constantDiagrams`, `evaluation`,
  `commaSubcomplex`, `comma`, `coconeCategory`, `IsWeakHomotopyEquivalence`.
- `Sheaf.CategoryTheory.RelativeInfinityCone`: `rightJoinCone`,
  `rightJoinConeInclusion`, `homotopyPullbackComparison` and its endpoint convention.
- `Sheaf.CategoryTheory.JoinSliceCoconeComparison`: `JoinCoconeSimplex`,
  `joinCocone`, `joinCoconeProjection`, `IsJoinCoconeComparison`,
  `JoinCoconeComparisonNaturality`, `JoinCoconeFiberComparison`,
  `join_slice_cocone_comparison`. The existing ordered/blunt join and its collapse
  cylinder formula are reused through that module's public imports.
- `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`: `calculusFiber`,
  `calculusApex`, `calculusCommaArrow`, `enhanced_functor_cone_calculus`.
- `Sheaf.CategoryTheory.RightPinchComparison`: `arrowMappingSpace`,
  `arrowMappingSpaceInclusion`, `rightPinchPrism`, `right_pinch_comparison`.
- `Sheaf.CategoryTheory.InfinityKanHomotopyCoherentCubeInvariance`:
  `KanCubeSquare`, `KanCoherentCube`, `kan_homotopy_coherent_cube_invariance`.
  The reused `CoherentPathModelComparison` is the interface exposed by its imports.
- The proof imports also retain `AnodyneCocones`, `ConeMonoRightAnodyne`,
  `InfinityHomBifunctorFunctoriality`, and `InfinityMappingComposition`, matching
  every already-stated proof dependency. Their declarations and docstrings were
  read; the theorem docstring explains their role step by step.

### Edge cases and source check

For `K = empty`, the whole cone is a point; the base functor category is a point.
The triangle span over that base still retains the apex arrow, and both rows are
maps to a contractible point. No choice of a base vertex is made. For `K = Delta[0]`,
the diagram is a single arrow; the retained triangle has exactly its ordinary
composition orientation `01`, `12`, `02`. Identity functors and identity shape maps
satisfy the same formulas. Empty individual mapping/cocone fibers are permitted:
no inhabitant is chosen. An empty ambient `C` admits no given right-cone diagram,
so the universal statement handles that case without an extra hypothesis.

Read the current unit record `sk-prop-sf-biduality-general` and the sole citer
`lem-coef-operadic-colimit-active-join-boundary` (its mapping-space translation in
proof steps 2--3). The unchanged node supports the same use: the entire comparison
arrow is preserved, so homotopy-pullback tests can be transported. No citer edit.

Read HA Definition the project server and Remark the project server, printed pp. 318--319 (September 18,
2017 PDF), and Kerodon 01PF and 046J online. The node is the agent-written bridge
from sharp join restrictions to composition, not a direct quotation of HA.
Sources: https://people.math.harvard.edu/~lurie/papers/HA.pdf ;
https://kerodon.net/tag/01PF ; https://kerodon.net/tag/046J .
WANTED: archival copies of these HA, HTT and Kerodon source places in literature/,
as already requested in the stage-1 proof-origin record.
No statement dispute or node fault was found.

### Searches

All remote searches used the prescribed `msearch.py NF <item>` wrapper. Results
were recorded in the sandbox `searches.jsonl`.

- LeanFinder: "For a simplicial right cone diagram in a quasicategory the apex
  evaluation equivalence identifies restriction of cocones with composition
  naturally in a functor". Eight hits, including ordinary
  `CategoryTheory.WithInitial.coconeEquiv` and strict-Segal Kan extension results;
  none states this coherent square comparison.
- Loogle: `SSet.Enhanced.joinCocone, SSet.Enhanced.mappingSpace`. No hits (project
  identifiers are outside that index).
- Grep: `cocone|coslice|anodyne` in `AlgebraicTopology/Quasicategory`. No hits.
- LeanSearch: "The sharp join coslice restriction square for a cone is equivalent
  to composition with its coherent cocone on Kan mapping spaces". Eight ordinary
  cocone/category hits, including cocone-morphism equations; no match.
- Direct `rg` in Mathlib, upstream `WeilConjectures`, shared `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: searched cocone/apex, cone contraction, mapping
  composition, sharp fibers and corresponding declaration names. Found and reused
  the existing cone, coherent comma, fiber, pinch, cube and composition interfaces;
  no existing theorem states the item's comparison. The upstream literal node-id
  search has no hits. The older `joinConeApex` is left-oriented and is not the
  right-cone apex used here. Existing fixed-vertex triangle fibers do not encode
  the required variable-apex triangle span over `C`, supplied as an owning helper.

### Validation

Every delivered Lean file is checked through the required `scompile.py` wrapper;
only the single-file compilation is requested. The delivery dry run then performs
server preflight and its own single-file compilation. Final results are recorded
below after those checks complete.

Final explicit `scompile.py` check: exit 0, no errors and no warnings, for both the
sandbox module and the final library-path module (22.6 s and 27.2 s respectively).

Delivery dry run: `deliver2.py NF lem-coef-cone-apex-cocone-space-comparison
--no-push` printed `OK (dry run)` for commit `fc4f3a48a6`: server preflight and
compilation both passed. The Lean source was unchanged after that check.


### Self-check of the retained repair

The resumed packet passed the prescribed initial `deliver2.py --no-push` check:
`OK (dry run)`, commit `aad04e84d4`; both sandbox and library-path compilations
passed. The saved mathematical work is retained as instructed.

Reopened the node, every statement dependency record and its public declaration
interfaces, and the entire delivered module. For the returned H3 point, the
conclusion now supplies `Comparisons F`: the sharp restriction square is connected
to the raw square, then through the whole-cone triangle square to the base
composition square by three `SquareComparison` records. Each fixes its four
corner maps, contains a `KanCoherentCube` with four weak equivalences, and supplies
`path_weak` and `comparison_homotopy`. The composition corner is the span from
`mappingSpace C (apex c) W` through the arrow model and the actual triangle fiber;
the other corner is identified by `base.pinch`. The triangle short edges are fixed
to gamma and Delta(alpha), and its long edge is `base.long`. Thus the conclusion
compares the displayed arrows and their specified composition data, rather than
only individual corner spaces or homotopy-pullback truth values. The sharp-to-raw
maps, right-pinch maps and apex evaluation are fixed by their coordinate formulas.

The theorem quantifies over arbitrary shape and target maps; maps are supplied
over the full apex categories before taking fibers. No colimit, fibration,
nonempty-shape or nonempty-fiber hypothesis occurs. The empty-shape, empty-fiber,
identity-target and identity-shape cases remain included. The original node
statement is unchanged. Checked that the recorded signature is verbatim, the only
postponed proof is the owning theorem, and all Lean lines meet the width limit.
This is the author's self-check; no independent-reader claim is made.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
