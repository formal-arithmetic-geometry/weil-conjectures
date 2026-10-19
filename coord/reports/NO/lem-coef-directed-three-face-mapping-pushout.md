## Worker report

The module `Sheaf.CategoryTheory.DirectedThreeFaceMappingPushout` states
`SSet.DirectedThreeFace.directed_three_face_mapping_pushout`, with `sorry` as its only
postponed proof. It supplies a natural, fully normalized bar-diagram family and asserts
its homotopy-colimit comparison and all nonextreme actual face comparisons. The other
declarations are coordinate descriptions and interfaces belonging to this node. No new
independent notion, dependency repair, or statement correction is needed.

Hypothesis and clause correspondence:

- Small simplicial sets and the actual map K → H = Λ³₂ are `{K : SSet.{u}}` and
  `p : K ⟶ (horn 3 2).toSSet`. The single explicit universe `u` is arbitrary.
- `face p J` is `(stdSimplex.face J).preimage (p ≫ (horn 3 2).ι)`.
  Its underlying simplicial set is the degreewise pullback K_J, presented as a
  subcomplex of K. `IsFace` lists precisely the subsets of 012, 023, or 123.
  `QuasicategoricalFaces p` imposes `Quasicategory` on every nonempty such J,
  including vertices, edges, and the three triangles. It imposes no condition
  that K itself be a quasicategory.
- `faces p` rigidifies these inverse-image faces using the dependency's actual
  `SSet.Pinched.rigidification`. `fibre p i = (faces p).obj {i}` is A_i.
  `inclusion` is rigidification of the actual subcomplex inclusion.
  `edge p {i,j} hi hj a b` is M_ij on the actual images of the fibre objects.
  `extend` is the actual face-inclusion map on this mapping module, with only
  the object identifications forced by functoriality; it is not an inverse.
- Endpoint variables in the theorem are actual vertices
  `x : (face p {0}).toSSet _⦋0⦌` and `z : (face p {3}).toSSet _⦋0⦌`.
  They enter A_0 and A_3 using the dependency's canonical `Pinched.vertex`.
- `TwoWord` records a chain in the appropriate A_i and its chronological pair
  of endpoint mapping simplices. `ThreeWord` records the two independent
  chains in A_1,A_2 with factors M_01, M_12, M_23. Their operators use actual
  composition, restricting internal simplices and both chain directions.
  This is the total diagonal of the double bar, with no Fubini-order reversal.
- The data are explicitly tied to the dependency's derived coends:
  `leftModule` is its existing `coherentHomDiagram`; `RightModel` fixes the
  entire contravariant module by a simplicial-set value isomorphism and its
  enriched composition formula. `DerivedModels.two_iso` identifies each
  two-sided bar with `DerivedSpaceModule.bar`, and `two_formula` identifies
  every word. `middle_value`, `middle_left_action`, and `middle_right_action`
  fix M_12 with both actions. `extension` is the dependency's `LeftExtension`;
  `three_iso` and `three_formula`, using `flattenLeft`, identify R with the
  chronological iterated derived bar. These are presentations of the
  existing derived coends, not replacement definitions of that notion.
- The expanded diagram is
  P → P_123 ← R → Q_012 ← Q → D_023 ← D,
  where P = M01 ⊗^L_A1 M13,
  P_123 = M01 ⊗^L_A1 C[K123](−,z),
  Q = M02 ⊗^L_A2 M23,
  Q_012 = C[K012](x,−) ⊗^L_A2 M23,
  D_023 = C[K023](x,z), and D = M03.
  `Shape`, `Word`, and `BarDiagram` retain this exact finite diagram.
- `p_comparison`, `q_comparison`, `d_comparison` are the actual edge-13,
  edge-02, and edge-03 inclusions, on every simplex. `PushoutComparison`
  asserts that these three maps are weak homotopy equivalences. Inverting
  them in spaces identifies the expanded diagram with the specified span.
  Its left arrow is `to_p`, composition in 123; its right arrow is
  `to_q`, inverse of `q_comparison`, `to_d` (composition in 023), and inverse
  of `d_comparison`. Thus the right arrow first composes in 012 and then
  in 023, with precisely the full-edge inverses prescribed by the node.
- `cocone_formula` specifies every leg by actual enriched composition in
  the full inverse-image face. `comparison_formula` specifies the whole
  Bousfield–Kan homotopy-colimit map, including every chain simplex.
  `PushoutComparison` asserts weak homotopy equivalence of this comparison
  followed by `totalMap` into C[K](x,z). The full inverse-image face is K
  up to its canonical subcomplex isomorphism. The target endpoint objects
  are the images of x,z under the composites of actual inclusions; by
  rigidification functoriality and `Pinched.vertex_naturality` these are
  the canonical vertices of C[K].
- `BousfieldKan.BK Shape B.diagram` is the homotopy colimit of the expanded
  diagram of spaces. In the infinity category of spaces, the marked weak
  equivalences contract this to P ⨿^h_R D. This is a model for the genuine
  homotopy pushout with its coherent cocone, not an ordinary pushout in
  the homotopy category or a pushout of component sets. In particular the
  D cocone leg, by the normalized `d_comparison` and `cocone_formula`, is
  exactly the actual edge-03 inclusion, with its forced endpoint transports.
- `FaceComparisons p` uses the actual `Pinched.mappingMap (face p J).ι a b`.
  Its two label tests say i ≤ j and (i,j) ≠ (0,3). Vertices a,b of the face
  with those labels are exactly u ∈ K_i,v ∈ K_j regarded in K_J. Thus every
  face containing the endpoints is included. The tests retain i=j and do
  not assume i<j. There are no endpoint vertices in the empty face.
- `Family.naturality` applies to every actual map f over H, with no
  quasicategory hypothesis needed for the bar constructions. `faceMap`,
  `fibreMap`, `edgeMap`, `twoMap`, `threeMap`, `wordMap` are its actual
  degreewise maps. Its natural transformation is specified on every word,
  so is unique; identity and composition compatibilities follow from
  these exact formulas. The two additional equations retain the entire
  cocone and the comparison under `BousfieldKan.bkMap`. The face comparisons
  are natural maps by the recorded `Pinched.mappingMap` construction and
  the dependency's mapping-comparison naturality.
- No cocartesian lifts, enlargement of K, strict triangle-to-edge
  retractions, or equivalences of enlarged faces occur in the statement.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, together with Mathlib's `SSet`,
  `horn`, `stdSimplex.face`, `Quasicategory`, and subcomplex primitives.
- `Sheaf.CategoryTheory.CoherentNerveComparison` and its infrastructure:
  `CategoryTheory.CoherentNerve.SCat`, `hom`, and the simplicial enrichment.
  The coherent-nerve theorem supplies the background comparison, not an
  additional assumption on the input.
- `Sheaf.CategoryTheory.PinchedRigidificationResolution`:
  `SSet.Pinched.rigidification`, `vertex`, `mappingMap`, and
  `vertex_naturality`; read the final resolution theorem and its proof
  docstring, including actual-map naturality and full-edge comparisons.
- `Sheaf.CategoryTheory.DerivedSpaceModuleCoyoneda`:
  `Left`, `Right`, `bar`, `actLeft`, `actRight`, `column`, `row`,
  `LeftExtension`, `flattenLeft`; its `Statement` and final theorem explain
  the projective-coend comparison, homotopy invariance and chronological
  Fubini. `coherentHomDiagram` is the existing declaration from its public
  import `Sheaf.CategoryTheory.CoherentWeightLimitRecognition`.
- `Sheaf.AlgebraicTopology.BousfieldKanComparisonCalculus`:
  `BKObj`, `BK`, `bkMap`, with their chain formulas and functoriality.
  Added its already landed node `lem-coef-bousfield-kan-comparison-calculus`
  to stmt_deps to record the particular existing homotopy-colimit model.
- The stated proof dependencies `EnrichedCoend`, `KanQuillenRightProper`,
  `ModelCofibrantColimitComparison`, and `SimplicialProjectiveModelCalculus`
  are imported without `public`. The four currently unstated proof inputs
  (directed enriched amalgamation, triangular bar excision, extreme
  bimodule attachment, simplicial derived pushout mapping) have no recorded
  modules and hence no import is fabricated. They are needed for the
  postponed proof, not for writing this statement.

Edge cases checked before and after writing:

- Empty K or empty endpoint fibre: there are no endpoint vertices, and no
  nonemptiness assumption was introduced.
- Empty A_1: P and R are empty bars; the span reduces to D. Empty A_2:
  R and Q are empty; the pushout becomes the homotopy coproduct of P and D.
  The dependent sums of chains give exactly these empty cases.
- Zero-length chain simplices and degeneracies: the chain composite is the
  identity. The operators use actual module units, including repeated
  vertices; no positive-length restriction is present.
- Equal endpoint labels in the nonextreme comparisons and singleton faces:
  `FaceComparisons` tests ≤, not <, so all fibre endomorphism mapping spaces
  and identity cases are retained.
- K=Λ³₂: vertex categories are points, P,R,D are contractible. The expanded
  shape has a contractible interval nerve, agreeing with the contractible
  three-edge-square mapping object C[Λ³₂](0,3).
- Empty mapping simplicial sets are permitted throughout. There is no
  local Kan assumption on fibre or face rigidifications; all weak
  equivalences use the dependency's geometric-realization convention.

Searches made (2026-10-17):

- msearch.py LeanFinder, query “homotopy pushout of mapping spaces for
  coherent rigidification of three faces of a 3 horn”: eight hits, all
  horn-3 face-descendant/ordinary colimit declarations such as
  `SSet.horn₃₂.desc`; no enriched derived mapping-space formula.
- msearch.py LeanSearch, query “derived mapping space pushout for a
  simplicial category rigidification of a three horn”: eight hits,
  ordinary horn colimits and `Types.Pushout.cocone`; no match.
- msearch.py Loogle, query `SSet.horn₃₂.exists_desc`: one hit giving an
  ordinary morphism out of the horn from compatible faces, not this node.
- msearch.py grep, query `three.face|mapping.*pushout|pushout.*mapping`,
  Mathlib AlgebraicTopology: zero hits.
- rg of the source `WeilConjectures/` and the project's `lean/Sheaf/`,
  query `three.face|ThreeFace|directed_three|lem-coef-directed-three-face-mapping-pushout`:
  only unrelated three-face mentions and the consumer
  `CocartesianThreeHornFaceConservation` proof docstring; no declaration.
- rg of `dag/lean_names_upstream.json`, upstream `WeilConjectures/`, and
  project `lean/Sheaf/` for `DirectedThreeFace|directed_three_face_mapping_pushout`:
  no existing name. Inspected the related Bousfield–Kan, derived-space-module,
  pinched-rigidification, and coherent-weight modules and reused them.

Validation: scompile.py compiled the final module in sandbox and library modes
cleanly, with no warnings. All universes and variables are explicit. The sole
postponed theorem carries the complete nine-step DAG proof in its docstring.
The statement itself and its original four statement dependencies are unchanged;
the only additional dependency is the already landed BK model.

## Second reading by NO

Author's separate rereading, not an independent agent review; the dispatcher forbids
starting other agents, and the maintainer supplies the independent delivery review.
I reopened the node, all recorded dependency interfaces, and the completed file.
The face hypothesis includes all nonempty lower faces; there is no hypothesis on
K itself. P, R, D have the required chronological factors. The 123 contraction
retains the A_1 chain; the 012 contraction retains the A_2 chain, followed by the
023 contraction across the full-edge-02 inverse. The D leg is the actual inclusion.
The finite zigzag uses weak equivalences as inverses, never strict retractions.
Its BK homotopy-colimit map retains the whole coherent cocone. Nonextreme
comparisons include i=j and all containing faces. Naturality uses actual maps over
the horn, on every word, without choosing lifts.

During this reading I added `DerivedModels`: this explicitly identifies the
coordinate descriptions with the dependency's actual `DerivedSpaceModule.bar`
and `LeftExtension` rather than leaving the relationship implicit. Both enriched
actions of M_12, the right endpoint actions, and all Fubini word coordinates are
fixed. The rebuilt file compiled cleanly. No mathematical mismatch remains and
no statement is disputed. The use of the inherited operadic branch is exactly
how the source field of this auxiliary agent-formulated node identifies its
provenance; it is not presented as a quoted numbered theorem of HTT or as the
current blueprint unit's own statement.
