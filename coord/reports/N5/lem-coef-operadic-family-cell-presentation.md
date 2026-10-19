## Worker report

The module `Sheaf.CategoryTheory.OperadicFamilyCellPresentation` states
`SSet.Enhanced.Operadic.SourceCells.operadic_family_cell_presentation`, with one
postponed theorem proof. Its auxiliary declarations unpack the objects, three cell
types and ordering assertions of this node. They are definitions with real data,
not assumptions supplying a filtration, arbitrary equivalences, or a target extension.
The natural-language statement is corrected under §1(C) for the tail-stage ordering, completed output groups, and first-vertex source attachment; the DAG dependencies remain unchanged.

The recorded maintenance note is resolved stage 1, requesting the two hidden
arguments in old proof steps 7 and 8 be split without changing the statement. The
current node already cites the resulting `lem-coef-join-pullback-simplex-extension`
and `lem-coef-bipartite-cocartesian-simplex-extension`. Both modules are imported;
the theorem docstring follows the current thirteen steps, including those citations.
No withdrawn stage-2 binding was reused.

Hypotheses:

| Node hypothesis or object | Lean rendering |
| --- | --- |
| Fixed small simplicial universe | Explicit `universe u`; every simplicial set and index set is in that universe. No auto-bound variables. |
| `n ≥ 1` | `(n : ℕ) (hn : 1 ≤ n)`; no dimension-zero parameter simplex is substituted. |
| Small family over the product base | `F : Family (Δ[n] : SSet.{u})`, with the dependency's full product categorical fibration, fiber operads and product-relative Segal limits. The product projection is `lift F.operadicBase F.parameter`. |
| Space zero-fibers | First conjunct of `Hypotheses`: `KanComplex` of the arity-zero fiber of each actual parameter fiber, not of the whole operad. |
| Every parameter-edge correspondence constant over `[0]` | Second conjunct of `Hypotheses`: for every edge, a correspondence and a pullback square identifying it with that edge restriction; its operadic map commutes and `IsConstantOverZero C` holds. These are actual pullback restrictions, not arbitrary correspondences or unrelated fiber equivalences. The square is `IsPullback j C.parameter F.parameter e`. |
| Stationary inert lifts globally cocartesian | Last conjunct of `Hypotheses`: each fiberwise `IsMonoidalInertEdge` becomes `IsCocartesianEdge (lift F.operadicBase F.parameter)` after the fiber inclusion. The full product projection appears, not merely the parameter-fiber projection. |
| `A`, `P^-`, `P^+` | `source F`, `minus F`, `positive F`. Full subcomplexes on parameter zero or positive vertices equal the actual parameter fiber/face, because a simplex of `Δ[n]` is determined by its ordered vertices. `minus` is the literal horn preimage. |

Conclusion and clauses:

| Node clause | Lean rendering |
| --- | --- |
| An exhaustive well-ordered filtration of simplicial subsets | `Nonempty (Presentation F)`, with a small `Index`, a `LinearOrder` and well-founded strict order. `stage` takes values in `F.M.Subcomplex`. `first_le`, `start`, `monotone`, `exhaustive` specify its initial stage, order and union. |
| Limits are unions | `continuous` gives the supremum of all preceding stages at every noninitial stage without an immediate predecessor. |
| Successors are cell pushouts followed by monomorphic categorical equivalences | `successor` and `IsCellStep`; all cell labels occur at successors by `labels_are_successors`. `RelativeAttachment` uses the actual categorical `pushout` and a comparison `t`, with `Mono t` and precisely the homotopy-functor testing formula of the Joyal-model node. `t ≫ V.ι = pushout.desc ...` fixes the map into the family. |
| Preliminary replacement relative to the boundary | `RelativeAttachment` permits `B'`, `j : B' ⟶ B`, `c' : A ⟶ B'`, with `c' ≫ j = c`. `j` is mono and categorically equivalent. The identity replacement is allowed. The evaluation of the replacement is `j ≫ e`; the boundary is preserved literally. |
| Empty attachments / neutral comparison steps | `label j = none` alternative of `successor`; the canonical inclusion `Subcomplex.homOfLE (monotone h.le)` is a categorical equivalence. |
| Over `Δ^op × Δ[n]` | Every stage is a subset of `F.M`; every evaluation and pushout comparison has its composite into `F.M` fixed. The maps to the product base are therefore their composites with the original product projection, with no independent base map. |
| Type (a), active positive simplex with final color | `Cell.kind = .color`, `positive_seed`, `active`, `color_end`. `IsCellStep` uses `simplexAttachmentSlice (source F) c.simplex`, the existing strict pullback model of `A ×_P P_/σ`. Its map is join of its identity with `(boundary c.dimension).ι`. |
| Type (b), final arity zero, without an activity condition | `.zero`, `positive_seed`, `zero_end`. The same incoming join-boundary attachment is used; no `active` hypothesis is imposed on this case. |
| Incoming attaching evaluation | `IsIncomingEvaluation` prescribes the pure source factor, pure final simplex and, for every slice simplex, the entire stored extension map. In particular evaluation cannot be an arbitrary map with the correct vertices. |
| Type (c), whole-family `τ`, positive final parameter | `.output` and `positive_end`. Its `simplex` is a map into all of `F.M`, without activity or a positive-face restriction. Arbitrarily long initial source blocks are allowed. Its boundary map is `(boundary d).ι ⋆ 𝟙 L_τ`. |
| `L_τ` is the inert-extension quasicategory itself | `extensions F τ` is a subcomplex of the existing `coherentJoinCoslice τ`. Its simplices are actual join maps extending all of `τ`. `InertExtension` fixes the terminal block's whole parameter simplex, restricts its vertices to arities zero or one, and requires base-inert cross edges from the last vertex and base-inert edges inside that block. `IsBaseInert` deliberately imposes no cocartesianness. Membership quantifies over restrictions only to make closure under operators literal: the identity restriction recovers the stated condition, and the condition is preserved under every terminal-block restriction. |
| All source-to-tuple faces, no factorization through a color | `Cell.simplex` is unrestricted in the output case; `IsOutputEvaluation` prescribes the pure factor to be this entire simplex. There is no intermediate color or factorization datum. An edge from the source to a tuple remains an allowed new pure face. |
| Output evaluation including the full inert extension | `IsOutputEvaluation` fixes both pure factors and every coslice extension on `Δ[d] ⋆ Δ[a]`. This includes all coherent endpoint triangles and noninvertible maps between inert extensions. |
| Edge-and-endpoint incidence category `I_r` | Existing `InertOperad.Incidence r` and its nerve `incidence r`. Its objects are interval-inert maps from `[r]` to arities ≤1: the `r` intervals and `r+1` endpoints. Its only nonidentity arrows are the two interval endpoint arrows; adjacent intervals share a single endpoint object. No private incidence category is introduced. |
| Chosen fiberwise cocartesian inert lifts give `i` | `IsIncidenceDiagram`: `i` projects to the existing canonical incidence base; each last cross edge is globally cocartesian and lies over the precise labeled interval/vertex inclusion. |
| `L_τ` is a quasicategory | Explicit `Quasicategory (extensions F τ).toSSet` in the conclusion, for every whole simplex with positive final parameter and each specified final arity. |
| For every inner fibration of quasicategories and every diagram, left-cone restriction is a trivial Kan fibration | `ConeRestriction i`. A boundary-lifting problem for the displayed cone restriction is exactly a square from `pushoutJoin (boundary a).ι i` against `q`. Its source is `(∂Δ[a] ⋆ L_τ) ∪ (Δ[a] ⋆ N(I_r))`; the map on the pure `L_τ` factor is the arbitrary fixed diagram `f`. Thus `HasLiftingProperty` for every `a`, `E`, `D`, `q` is exactly the assertion with all boundaries and base maps fixed, not merely existence on objects. This is the boundary-inclusion RLP definition recorded by `def-weil-pbc-trivial-kan-fibration`. No categorical equivalence between `incidence r` and `extensions F τ` is asserted. |
| `d=0` cell adjoins the object after its incidence | The boundary is empty, and terminal augmentation makes `∂Δ[0] ⋆ L_τ = L_τ`. The attaching map `b` and pushout equation put that boundary into the preceding subset. |
| For `d>0` the final-vertex cone is old | It is a subcomplex of `∂Δ[d] ⋆ L_τ`; the whole latter map lands in the preceding subset by `RelativeAttachment`. |
| Output groups ordered by positive-tail image dimension | `tailRank`, `tail_order`. `tailRank` counts nonidentity adjacent arrows in the product nerve after the first positive vertex; it excludes every crossing edge out of a zero-parameter prefix. The corrected `tail_order` compares only `.output` cells, while incoming cells and incidence legs are placed where their boundaries require them. |
| Faces and inert associates have their attaching boundaries present | The map `b` in `RelativeAttachment` and the canonical evaluation equations fix every boundary simplex in the earlier stage. |
| Whole output simplices in increasing dimension at fixed tail stage | `output_dimension_order` compares actual `Cell.dimension` at equal `tailRank`. This includes every initial source block, not only the tail's dimension. |
| Limits before advancing to the next output tail stage | `completed_lower_tails` applies only when the current label is `.output`; it places every whole simplex at smaller tail rank, and every one of its inert extensions, in the preceding stage. Incoming color legs are therefore not forced into a preceding output group. |
| Vertex output cell and chosen legs precede positive-dimensional cells at that vertex | `vertex_before_output`; chosen legs occur in the same output join evaluation as the vertex. The entire final-vertex cone is also in each later output cell's attaching boundary. |
| `n=1`: colors, zero outputs, then tuple source cells at zero tail | `zero_tail_order` retains the color-before-noncolor and zero-before-output comparisons within rank zero. All arbitrary source prefixes with tuple-vertex tail have rank zero; the corrected `completed_lower_tails` includes every such simplex and extension before a later output tail stage. |
| Positive-dimensional type-(a) first-vertex source attachment already present | `incoming_source_present` uses only `simplexAttachmentComplex (source F) (const x)` for the first vertex. This is the earlier source attachment required by the corrected clause and does not include the new color cell's inert-extension closure. |
| `n>1`: new type-(a) simplex starts at parameter one; its source cone is in the horn | `higher_parameter_source`, with `¬ range simplex ≤ minus F` specifying a new simplex. The field fixes the parameter value and places `sourceConeWithInert` in `minus F`. |
| Every stationary inert color edge is selected or equivalent to a distinguished leg over the same base | `ColorLegsCovered` gives a triangle from a selected last cross edge to every globally cocartesian stationary base-inert edge into a color with that source. The remaining edge is an equivalence over the constant full-base vertex. Equality is included by a degenerate triangle. Positive sources are treated by the final universal conclusion; stationary edges at parameter zero are already in the initial horn. |
| All mixed source-prefix/noncolor-tail simplices covered by cells and comparisons | `exhaustive` covers every simplex, including those mixed simplices. Each substantive successor is exactly an evaluated incoming/output cell; the only other successors are the explicitly stated categorical equivalence comparisons. The corrected `completed_lower_tails` prevents advancing an output group without its lower-tail mixed simplices. |
| Source-only, no target extension or target colimits | The filtration depends only on `F`; there is no target functor or target-colimit hypothesis. `E`, `D` and `q` appear only inside the local universal cone-restriction test. |

Dependency declarations used:

* `Sheaf.CategoryTheory.OperadicCorrespondence`: `Family`, `Correspondence`,
  `IsConstantOverZero`, `IsActiveDiagram`, `fiberProjection`, `fiberInclusion`.
* `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `fullSubcomplex`,
  `IsEquivalenceEdge`, simplicial functor/mapping conventions. Its recorded
  `coneCategory` is the coherent comma construction, which is not substituted
  for the sharp join cone in this statement.
* `Sheaf.CategoryTheory.RelativeInfinityCone` and its public imports:
  `orderedJoinFunctor`, `orderedJoinInl`, `orderedJoinInr`.
* `Sheaf.AlgebraicTopology.JoyalModelStructure`: its precise homotopy-functor
  testing formula is used directly in `RelativeAttachment` and `successor`;
  no second categorical-equivalence predicate is defined. The Joyal node includes
  invariance under enlargement of the testing universe.
* `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`:
  `fiber`, `IsCocartesianEdge`, with Mathlib `InnerFibration`.
* `Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations`:
  `modelCategoryQuillen.I` is the boundary-inclusion family and its `.rlp` is
  exactly the lifting condition transposed in `ConeRestriction`.
* `Sheaf.CategoryTheory.InertOperadColorReconstruction`:
  `Incidence`, `incidence`, `incidenceBase`.
* `Sheaf.CategoryTheory.SimplexJoinAttachment`: `simplexAttachmentSlice`,
  `simplexAttachmentComplex`, reusing the already recorded join-slice construction.
* `Sheaf.CategoryTheory.RelativeCosliceLeftFibration`: `coherentJoinCoslice`,
  `coherentCosliceProjection`, the full stored `CoherentJoinSimplex.extension`.
* `Sheaf.CategoryTheory.BipartiteCocartesianSimplexExtension`:
  `lastVertexInclusion`, `joinZeroInterval` for actual last cross edges.
* All recorded proof-dependency modules with Lean bindings are imported, privately
  when used only by the future proof. The monomorphism boundary-cell dependency is
  a Mathlib leaf supplied by the simplicial skeleton/category-with-fibrations imports.

Edge cases checked before and after writing: `n=1` has initial horn the source
vertex; `n>1` contains the face `{0,1}` in the zero-missing-face horn. `d=0` uses
empty boundary and includes the pure new object. `d=1` output cells include the
new mixed edge itself and both endpoint cones. Arbitrarily long source prefixes
are not bounded. `r=0` incidence has its one endpoint and identity projection;
`r=1` includes an edge object and both endpoints. Empty source slices still have
the pure positive simplex in the augmented join. Empty zero-fibers are permitted
by `KanComplex`. At cone-boundary dimension zero the source of the pushout join
still includes the fixed entire diagram `L_τ`, so surjectivity is not forgotten.
Degenerate base edges are excluded from `tailRank`; nontrivial endomorphisms are
counted even if their endpoint objects coincide. No finiteness, nonemptiness,
activity, or color-factorization hypothesis is imposed on output simplices.

Searches (2026-10-17):

* `msearch.py ... leanfinder "operadic family outer horn source cell presentation inert incidence join filtration"`:
  eight hits, all ordinary horns and horn-colimit lemmas; no presentation theorem.
* `msearch.py ... loogle "SSet.Subcomplex, SSet.orderedJoinFunctor"`:
  zero hits; the latter name is unknown to the Mathlib service (it is project code).
* `msearch.py ... grep "operadic.*(cell|filtration)|familyCellPresentation"`:
  zero hits in Mathlib.
* `rg -n` on the same pattern and the exact item id in the upstream
  `WeilConjectures` and shared `lean/Sheaf` trees: no existing item theorem.
  Separate exact-id `grep -rn` in upstream also returned no match.
* Read the existing project join-attachment, coslice, incidence, correspondence,
  fibration and Joyal modules. Reused their constructions; no second join,
  incidence category, family, categorical-equivalence predicate, or fibration notion.
* Searched categorical-equivalence declarations project-wide, inspected the
  coherent-nerve and contravariant-slice variants, and kept the dependency's exact
  homotopy-functor testing formula inline instead of introducing another predicate.
* `tools/lean_names_upstream.py show` consulted the imported blueprint/docstring
  binding tables; no existing binding for this item was found by the exact-id search.

Source checked: HA PDF online, printed pp. 332--336 for the join attachment and
`F(m)` ordering, and the node's reviewed source-specific nonsymmetric refinement
of pp. 340--341. The full node's statement, thirteen proof steps, current review
and resolved repair note were read. No statement correction or disputed clause
is claimed in this delivery.

Validation: prescribed `scompile.py` compiles of the complete delivered module;
no error or warning (only the expected postponed theorem). Final dry-run and
push results are recorded by the delivery wrapper.

## Statement corrected

The old statement is the `old_statement` value in the node's `statement_change` record. It globally ordered every cell by `tailRank`, which fails in the identity family $N(\Delta^{\mathrm{op}})\times\Delta^1$: the rank-zero tuple output cell needs an incidence endpoint edge of rank one in its boundary. The source ordering in HA, Theorem the project server proof steps (2)--(3), orders completed output groups by tail stage and inserts incoming cells and incidence legs where their boundaries require them. The correction therefore restricts `tail_order` and `completed_lower_tails` to output groups. It also replaces the color first-vertex `sourceConeWithInert` requirement by the earlier `simplexAttachmentComplex` required by Lemma the project server.

The only citer is `lem-coef-operadic-correspondence-kan-filling` (holds true): it uses this node as a proof dependency and does not depend on the removed global rank comparison. No statement dependency changed.

## Second reading by N5

With the corrected node and module open, I re-rendered `tail_order`, `zero_tail_order`, `completed_lower_tails`, and `incoming_source_present`. In the identity family for $n=1$, output cells are compared by tail rank, while the rank-one endpoint leg may be inserted before the rank-zero tuple output; the zero-tail color/zero-output precedence remains exactly the stated one. For $n=2$, a positive type-(a) source attachment lies in the missing-zero-face horn and `incoming_source_present` asks only for the simplex attachment complex of its first vertex. Lower-tail completion is tested only at an output successor, so a lower-rank color-ended inert extension is not incorrectly required before its own incoming cell. The Lean fields and the corrected ordering paragraph agree clause by clause.
