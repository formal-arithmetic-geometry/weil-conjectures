## Worker report

This is a stage-2 statement delivery, with one postponed theorem and real definitions in
`Sheaf.CategoryTheory.OperadicCollageSegalMappingBridge`. The earlier conclusion that Q111's
merge made this assignment stale was incorrect: that delivery was a stage-1 proof split.
The live node has no Lean record or stage-2 review. I read that node and Q111's report.

The item statement is unchanged. Its statement dependencies gain six already-landed owners
of the constructions used here, as permitted by brief-stage2 section 5 (STMT_DEPS MAY GAIN
LANDED NODES). No blueprint unit, target, source statement, or proof plan changes.

### Hypotheses and clauses

* Every universe is explicitly bound. `u` contains the simplicial sets, the objects and
  morphisms of the ordinary base. An ordinary small category with different original size
  bounds is represented in their common containing universe; no site-universe equality,
  local-smallness restriction, nonemptiness hypothesis, or finiteness of X is imposed.
* The nonnegative integer is `r : ℕ`, including zero. The existing
  `InertOperad.incidence r` is the nerve of the category of inert restrictions from `[r]`
  to arities zero and one. There are exactly r+1 vertex objects, r edge objects, and the
  two arrows from each edge restriction to its endpoint restrictions. It is the stated
  I_r, represented without making another definition of the incidence category.
* The first clause takes arbitrary `[Quasicategory X]`,
  `f : InertOperad.incidence r ⟶ X`, and `z : X _⦋0⦌`. Its source is the existing
  `constantTestSpace f z true`, namely
  `mappingSpace (Fun(K,X)) (diagramVertex (SSet.const z)) (diagramVertex f)`.
* `mappingFamily f z` is the actual pullback of `transportSourceTarget X z` along f.
  The latter is the source-fixed arrow left fibration. A fiber is the unpinched arrow
  space from z to f(a); its transition along an incidence arrow is actual coherent
  postcomposition. This is the existing Hom-transport presentation, and its comparison
  with right-pinched Map is the recorded right-pinch comparison. Thus `mappingLimit`
  uses the existing full `rfSectionSpace` of this family as the section model of the
  displayed homotopy limit. It uses no chosen apex from a mere existence theorem.
* The theorem supplies j with `PinchFormula` and the claimed weak equivalence for this
  incidence shape. PinchFormula fixes the entire arrow at every index, interval,
  parameter simplex, and simplicial operator: its uncurried value is the source
  right-pinched simplex precomposed by `rightPinchPrism`. It is not a mere assertion
  that two unrelated spaces happen to be equivalent. The generic family of maps and
  its generic normalization serve to specify the canonical construction; the
  weak-equivalence assertion is restricted to the incidence shapes of this node.
* For the second clause, `B : Type u`, `[SmallCategory B]`, and `p : X ⟶ nerve B`
  render the ordinary-nerve base. `[InnerFibration p]` is exactly the stated lifting
  hypothesis, without an isofibration or a Kan-fibration assumption on p.
* The entire cone is `q : InertOperad.incidenceCone r ⟶ X`, with boundary
  `InertOperad.incidenceInclusion r ≫ q` and apex the image of
  `ComposableArrows.mk₀ (AsSmall.up.obj WithInitial.star)`. The nerve obtained by
  adjoining an initial object is the left join cone on the nerve. It is an equivalent
  model of the coherent comma cone of def-cbc-enhanced-diagrams-cones, by the existing
  join-cone calculus, including fixed apex and boundary. This is a representation of
  the given coherent cone, not a restriction to strict naturality in X or a new
  hypothesis on that cone.
* `ConstantApexSquare p i q z a true` is the already-recorded canonical interpretation
  of the displayed mapping square: whole-cone mapping spaces map by apex evaluation
  to Map_X(z,x) and Map_B(pz,px), and by restriction to the boundary mapping spaces.
  The evaluation legs are weak equivalences. Inverting them in spaces is exactly
  postcomposition by the entire cone. This avoids selecting a strict composition on
  the right-pinched mapping-space model.
* The test explicitly quantifies `φ : mappingSpace (nerve B) (pz) (px) _⦋0⦌`.
  These vertices are the actual ordinary arrows pz → px. The theorem requires
  `Function.Bijective` of whole-base-cone apex evaluation and tests the unique base
  transformation b having that component φ. Therefore the test is never vacuous
  because of an unspecified or missing lift of φ.
* In the ordinary base, naturality of b forces its component at a boundary object α
  to be `p(lambda_α) ∘ φ`. Consequently the target base section is the image under j
  of the boundary restriction of b, with precisely those varying components. It is
  not the constant transformation Δφ and does not require pf to be constant.
* `relativeMappingLimit p f z b` is the homotopy fiber of the map of complete section
  spaces over the specified coherent base section. This is the section model of
  the homotopy limit of the POINTWISE homotopy fibers: expanding a simplex gives a
  section in the source mapping family and a path to b in every fiber, with one
  coherent path family over the whole index. Exponential adjunction commutes with
  the degreewise products, endpoint pullbacks and equalities defining sections.
  Thus these are literally the same data as sections of the fiberwise path pullback;
  no interchange with a strict fiber or product of only vertex data is substituted.
* `relativeComparison` is the actual restriction/j-induced map on homotopy fibers,
  formed with the existing `HomotopySegal.fiberMap`. It applies boundary restriction
  and j to the first coordinate and the same base map to the entire path coordinate.
  Its commutative-square proof uses the recorded `ConstantTestNaturality` and hj.
* The domain of that map is a whole-cone fiber. To identify it with the node's
  `Map_X^φ(z,x)`, the theorem ALSO supplies the apex-evaluation fiber leg e, requires
  `IsApexFiberComparison` on both coordinates in EVERY degree, and requires e to be
  a weak equivalence. Its target is literally the recorded `homotopyFiber` of
  `mappingSpaceMap p z x` at φ. This is the canonical relative comparison represented
  by a span with an equivalence on its left; its right leg is an equivalence exactly
  when the node's displayed map is. No arbitrary map or unnormalized equivalence is
  admitted as e.
* The final biconditional is the requested homotopy-pullback test, with both directions.
  `PostcompositionNaturality` is equality of complete maps under arbitrary p, while
  `RestrictionNaturality` specifies restriction on the complete arrow family in every
  degree. The all-simplex PinchFormula fixes the evaluations and coherent comparison
  uniquely. The cone maps are the existing apex/restriction composition spans; their
  naturality retains the whole cone, and relativeComparison applies those same maps
  also to the entire base path. There is no choice of unrelated equivalences for
  different cones or base functors.

### Recorded interfaces used

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `mappingSpace`, `diagramVertex`,
  `evaluation`, `homotopyFiber`, `IsWeakHomotopyEquivalence`, and the cone conventions.
* `Sheaf.CategoryTheory.RelativeInfinityCone`: `IsHomotopyPullbackSquare` and its
  canonical path-pullback convention, through ConstantApexSquare.
* `Sheaf.CategoryTheory.IsofibrationExponentiation`: `isofibration_exponentiation`
  and Mathlib `InnerFibration`; no stronger condition is assumed.
* `Sheaf.CategoryTheory.SpaceTransportClassification`: `transportSourceArrows`,
  `transportSourceTarget`, and the recorded Hom-transport interpretation of their fibers.
* `Sheaf.CategoryTheory.RightFibrationMorphismSpace`: `rfSectionSpace`; despite its
  historical prefix, this definition is the full section complex of any supplied map.
* `Sheaf.CategoryTheory.HomotopySegalSpace`: `SSet.HomotopySegal.fiberMap`, the existing
  canonical map on path-model homotopy fibers of a pointed commuting square.
* `Sheaf.CategoryTheory.RelativeConeConstantTest`: `constantTestSpace`, restriction,
  postcomposition, `ConstantApexSquare`, and `relative_cone_constant_test`'s full
  `ConstantTestNaturality` clause.
* `Sheaf.CategoryTheory.InertOperadColorReconstruction`: `InertOperad.Incidence`,
  `incidence`, `incidenceCone`, and `incidenceInclusion`.
* `Sheaf.CategoryTheory.InfinityPullbackComparison`: `pullbackConeMapsEval`, evaluation
  transported to the actual endpoint objects, rather than leaving endpoint equalities implicit.
* Stated proof dependencies are imported without public as required. The genuine proof
  prerequisite `lem-coef-infinity-constant-source-section-comparison` still has no Lean
  record, so it has no import to add. Its unrecorded theorem is not used as construction
  data: this module uses the already-published source-arrow family and section complex.

### Edge cases

For r=0 there is exactly one vertex and no edge; the source comparison is the ordinary
right-pinch comparison and the relative limit has one pointwise fiber. Empty individual
mapping spaces and homotopy fibers are allowed. If there are no base arrows pz → px,
there are no base-cone transformations either, by the bijective apex evaluation; both
fiber quantifiers are empty in exactly the same case. The total mapping spaces then
map to an empty base, so the pullback test has the expected empty-space interpretation.
Identity p and identity base arrows retain their actual path fibers; no strict-fiber
replacement is used. Nonconstant pf, including the [1] example in Q111's report, is
covered because the base section is the boundary of the entire base transformation b.
All new data-bearing definitions are pullbacks, internal-hom maps or compositions of
recorded constructions. The only new sorry is the full node theorem.

### Searches and source

I read the source node's complete statement, proof and three recorded statement
interfaces, then read the additional helper declarations and their source docstrings.
The source GH Definition A.3.1(2) and the mapping-cylinder discussion were opened at
https://arxiv.org/html/1312.3178v4. This is the relative Segal mapping calculation,
using HTT the project server--5 and the project server--3 as in the reviewed stage-1 split.

`msearch.py leanfinder`, query "mapping space from a constant coherent diagram is homotopy
limit of mapping spaces and relative mapping spaces detect homotopy pullback", returned
eight ordinary-category, glueing or model-category results, none the quasicategorical
statement. `msearch.py loogle`, query "SSet, CategoryTheory.Limits.IsPullback", was an
invalid-identifier query and is not evidence of absence. The valid replacement
"CategoryTheory.Limits.IsLimit" returned the ordinary-category IsLimit API, not the node.
`msearch.py leansearch`, query "mapping space from constant diagram homotopy limit mapping
spaces", returned eight ordinary-category constant-limit results, none the node; its exact
result is retained in searches.jsonl. The required
`msearch.py grep`, query "homotopyLimit|homotopy.limit|mappingSpace" in
AlgebraicTopology/Quasicategory, found no hits. Direct rg searches in Mathlib's
Quasicategory folder, the source WeilConjectures tree, and lean/Sheaf found no theorem
stating the complete node. The source-tree node-id search found no attachment. Project
searches did locate the already-recorded incidence, section, constant-test and fiber-map
constructions listed above; those are reused instead of defining private copies.

No statement is disputed. No node statement correction or new definition node is needed.

### Published dependency repair

No dependency module is delivered. Initial compilation exposed a missing
`noncomputable` annotation on `SpaceStraightening.Diagrams`. Q19 independently landed
that exact annotation repair in the published SpaceValuedStraightening module while
this item was being checked. This delivery reuses that published interface and removes
its redundant private repair.

### Validation

Final single-file compilation passed through `scompile.py Q29
lem-coef-operadic-collage-segal-mapping-bridge` with the delivered module as its only
file argument, against the published dependency repair. Both its sandbox and library
checks completed without errors or unexpected warnings. The node metadata signature
matches the file verbatim; every variable is explicitly bound; every Lean line has at
most 100 characters. The required `deliver2.py Q29 lem-coef-operadic-collage-segal-mapping-bridge
--no-push` dry run returned OK: commit 3fa6fc6d69 passed preflight and compilation;
nothing was pushed by that dry run. No live file, source
checkout, git command in the shared repository, or global build was used.

## Second reading by Q29

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
