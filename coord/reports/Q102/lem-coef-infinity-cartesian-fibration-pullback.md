## Worker report

The module `lean/Sheaf/CategoryTheory/CartesianFibrationPullback.lean` states
`SSet.Enhanced.cartesianFibration_pullback`. It uses one universe `u` and four
simplicial sets `S`, `E₀`, `E₁`, and `H`, each equipped with its stated
`Quasicategory` instance. The maps `q₀`, `q₁`, and `r` have the source and target
specified by the node, and `F₀` and `F₁` have the displayed comparison sources and
targets.

The hypotheses render the node clause by clause as follows:

* `(hq₀ : cartesianFibration q₀)` and `(hq₁ : cartesianFibration q₁)` are the two
  cartesian-fibration hypotheses.
* `(hr : InnerFibration r)` is the inner-fibration hypothesis on `r`.
* `hF₀ : F₀ ≫ r = q₀` and `hF₁ : F₁ ≫ r = q₁` render the two commutative triangles
  `rF_i = q_i`.
* `hpres₀` and `hpres₁` use
  `SSet.Enhanced.preservesCartesianEdges` and say respectively that `F₀` and `F₁`
  carry the corresponding cartesian edges to `r`-cartesian edges.
* `hiso : IsIsofibration F₁` is the existing project notion of an inner fibration
  lifting equivalence edges with prescribed source. Its quasicategory conjuncts
  are redundant with the four explicit quasicategory hypotheses, so no extra
  mathematical assumption is introduced.

The conclusion existentially binds `hP : Quasicategory (pullback F₀ F₁)` so that
Mathlib's typeclass-parameterized `cartesianFibration` can be applied explicitly.
It states that the degreewise pullback is a quasicategory and that its induced
map to `S`, namely `pullback.fst F₀ F₁ ≫ q₀`, is a cartesian fibration. The final
universal clause renders an edge of the pullback by its two projections and states
exactly the required iff: it is cartesian over `S` iff both projected edges are
cartesian for `q₀` and `q₁`.

The dependency declarations used are:

* `SSet.Enhanced.coneCategory` and its supporting declarations from
  `Sheaf.CategoryTheory.EnhancedDiagramsCones` (`def-cbc-enhanced-diagrams-cones`).
* `SSet.Enhanced.cartesianFibration`, `SSet.Enhanced.IsCartesianEdge`, and
  `SSet.Enhanced.preservesCartesianEdges` from
  `Sheaf.CategoryTheory.InfinityFibrations` (`def-coef-infinity-fibrations`).
* `SSet.Enhanced.IsIsofibration` from
  `Sheaf.CategoryTheory.IsofibrationExponentiation`, an already existing project
  declaration found by search; this is imported and reused rather than copied.
* `pullback`, `pullback.fst`, `pullback.snd`, `Quasicategory`, and
  `InnerFibration` are Mathlib simplicial-set/category-theory declarations.

Edge cases checked: the pullback is degreewise and remains meaningful when either
factor is empty; no nonemptiness of `S`, `E₀`, `E₁`, or `H` is assumed; identity
comparison maps and identity base maps are allowed; and the statement does not
exclude degenerate or zero-dimensional simplices. The universe is shared by all
simplicial sets, as required by the fixed-universe node.

Searches made before writing:

* `msearch.py Q102 ... leanfinder "A pullback of cartesian fibrations over a common base along a cartesian edge preserving isofibration is cartesian"`: returned only ordinary-category `HasFibers`/`IsPreFibered` and model-category hits; no match.
* `msearch.py Q102 ... leanfinder "Cartesian edges in a fiber product of infinity categories are exactly pairs of cartesian edges when one comparison functor is an isofibration"`: returned only ordinary-category/model-category results; no match.
* `msearch.py Q102 ... leansearch "Pullback of cartesian fibrations of quasicategories along an isofibration preserving cartesian edges"`: returned only ordinary pullback/fibration results; no match.
* `msearch.py Q102 ... loogle "SSet, Cartesian"`: zero hits.
* `msearch.py Q102 ... loogle "Quasicategory, pullback"`: zero hits.
* `msearch.py Q102 ... grep "[CartesianFf]ibration|[Ii]so[Ff]ibration" AlgebraicTopology`: no relevant hit.
* `rg` over `lean/Sheaf`, `WeilConjectures`, and Mathlib found no existing theorem for this
  strict pullback edge criterion, but found the reusable declaration
  `SSet.Enhanced.IsIsofibration` in `Sheaf.CategoryTheory.IsofibrationExponentiation`.

The source read was Kerodon Proposition the project server (Tag 02VV). Its hypotheses are
matched by the binders above, and its induced map is represented by the first
pullback projection followed by `q₀`; the pullback condition identifies this with
the corresponding `q₁` composite. The source's edge criterion is the final iff.

## Second reading by Q102

I independently read the node's statement and all six proof steps, the delivered
module, the two statement-dependency node records and their actual source
declarations. I also opened `IsIsofibration` in
`Sheaf.CategoryTheory.IsofibrationExponentiation`. The source is Kerodon,
Proposition the project server, https://kerodon.net/tag/02VV (not a Stacks tag); I read the
complete proposition and proof online. The proposition is self-contained: its
displayed diagram, inner/cartesian-fibration assumptions, preservation assumptions,
and isofibration assumption are explicit. There is no suppressed finiteness,
nonemptiness, coefficient, or characteristic assumption. The node specializes the
proposition to four quasicategories in a fixed universe, and the Lean states exactly
that node. No statement correction is needed or made.

My object/hypothesis/conclusion checklist is:

| Node item | Lean rendering and verdict |
| --- | --- |
| Four quasicategories in a fixed universe | `{S E₀ E₁ H : SSet.{u}}` and the four `Quasicategory` instances. Exact: Mathlib's class fills every inner horn, and `u` is arbitrary. |
| Two maps to the common base | `q₀ : E₀ ⟶ S`, `q₁ : E₁ ⟶ S`. Exact simplicial maps. |
| Inner fibration from the comparison object | `r : H ⟶ S` and `hr : InnerFibration r`. Exact: Mathlib's definition is right lifting against all inner horn inclusions, without an outer-horn requirement. |
| Two cartesian fibrations | `hq₀ : cartesianFibration q₀`, `hq₁ : cartesianFibration q₁`. Exact: the dependency definition includes inner lifting and cartesian lifts with prescribed target for every base edge. |
| Two comparison maps | `F₀ : E₀ ⟶ H`, `F₁ : E₁ ⟶ H`. Exact, with neither map assumed arbitrary over another base. |
| Commutative triangles | `hF₀ : F₀ ≫ r = q₀`, `hF₁ : F₁ ≫ r = q₁`. Exact equalities of simplicial maps in every degree, not homotopies. |
| Preservation of both cartesian-edge families | `hpres₀ : preservesCartesianEdges q₀ r F₀ hF₀` and the analogous `hpres₁`. Exact universal implications for all edges; I opened the dependency definition rather than relying on its name. |
| `F₁` is inner and lifts outgoing equivalences to equivalences with prescribed source and exact image | `hiso : IsIsofibration F₁`. Exact: its actual body has `InnerFibration F₁` and, for each source vertex and equivalence edge in `H`, an equivalence edge in `E₁` with that source and equal image. Its two quasicategory conjuncts repeat already stated assumptions and add none. The lifted target is unrestricted, as in the node. |
| Degreewise pullback `P = E₀ ×_H E₁` | Mathlib's `pullback F₀ F₁`. Exact: `SSet` is a functor category of types and its limits are computed pointwise; evaluation preserves limits. No homotopy pullback or alternate comma category is substituted. |
| Induced map `q : P → S` | `pullback.fst F₀ F₁ ≫ q₀`. Exact: the pullback condition and `hF₀`, `hF₁` identify it with `pullback.snd F₀ F₁ ≫ q₁`. A separate tautological equality conjunct is unnecessary. |
| `P` is a quasicategory | `∃ (hP : Quasicategory (pullback F₀ F₁)), ...`. Exact: this asserts the structure as a conclusion and supplies it to the next predicate; it is not an added hypothesis. |
| `q` is cartesian | `@cartesianFibration (pullback F₀ F₁) S (pullback.fst F₀ F₁ ≫ q₀) hP inferInstance`. Exact, using the same dependency definition as for `qᵢ`. |
| Every edge is cartesian iff both components are | `∀ e : Δ[1] ⟶ pullback F₀ F₁, IsCartesianEdge ... e ↔ IsCartesianEdge q₀ (e ≫ pullback.fst F₀ F₁) ∧ IsCartesianEdge q₁ (e ≫ pullback.snd F₀ F₁)`. Exact iff, both clauses, all edges, in the node's quantifier order. |

For the dependency audit, `def-cbc-enhanced-diagrams-cones` records
`Sheaf.CategoryTheory.EnhancedDiagramsCones`; I checked its real inverse-triangle
definition `IsEquivalenceEdge` used by `IsIsofibration`, and Mathlib's `SSet`,
`Quasicategory`, and functor-category limit interface. The module's main recorded
declaration `coneCategory` is not being mistaken for the pullback notion. For
`def-coef-infinity-fibrations`, I checked `IsCartesianEdge` (all final outer horns
in dimensions at least two with the designated last edge),
`cartesianFibration`, and `preservesCartesianEdges` in
`Sheaf.CategoryTheory.InfinityFibrations`. These are the recorded notions, with no
extra instances or universe equalities. Both dependency records are usable; no
new node or dependency module is needed. There are no new nodes, sibling modules,
or `statement_change` records in this delivery to audit.

Edge cases: empty simplicial sets and an empty pullback are permitted; the
cartesian-lift condition then quantifies over no target vertices, and the edge iff
over no edges. Empty `H` or `S` also causes no artificial inhabitation requirement.
Identity maps and degenerate edges are included. There is no index set, additive
zero object, scheme, coefficient ring, characteristic, or degree parameter to
restrict; dimension-zero vertices and every dimension-one edge, including
degeneracies, are covered by the definitions. All four objects and the pullback
live in the same arbitrary `u`, precisely the node's fixed-universe convention.
There is no hidden variable: `u` is declared and `autoImplicit` is false.

Independent duplicate searches, with wording different from the worker's:

- `msearch.py Q102 lem-coef-infinity-cartesian-fibration-pullback leanfinder
  "A fiber product of quasicategories over an inner fibration has cartesian projection and cartesian edges detected in both factors"`:
  ordinary `HasFibers`/`IsPreFibered`, finite simplicial pullbacks,
  `SSet.Quasicategory`, and general model-category base-change instances; no match.
- `msearch.py ... leansearch "Cartesian morphisms in a strict fiber product of infinity categories are detected by both projections when a comparison is an isofibration"`:
  only ordinary `CategoryTheory.Functor.IsCartesian` and fibered-category facts.
  I opened `Mathlib/CategoryTheory/FiberedCategory/Cartesian.lean`: these describe
  ordinary functors and unique ordinary morphism factorizations, not this statement.
- `msearch.py ... loogle '"SSet", "pullback"'`: six hits, concerning finite
  simplicial sets, skeletal cell complexes, and exponential-corner fibrations.
  None gives the cartesian-fibration or componentwise edge conclusion.
- Independent `rg` searches for `cartesian...pullback`, `pullback...cartesian`,
  `fiber.product`, `isofibration`, and `preservesCartesianEdges` across Mathlib,
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, and the project's
  `lean/Sheaf` found no duplicate theorem. I opened the nearby
  `isofibration_pullback_limit` (categorical-pullback mapping-space assertion),
  `relativeExponentialRestriction_innerFibration` (exponential restriction), and
  `cocartesian_categorical_base_change` (preservation of categorical equivalences):
  their signatures do not state this result. The source-name inventory
  `dag/lean_names_upstream.json` has no collision for this theorem or these helper
  predicates. The existing `IsIsofibration` is reused without a private copy.

Mismatches found and repaired:

1. H8: the original proof docstring merely restated the result and referred to the
   source proposition. It did not preserve the node's proof for stage 3. I replaced
   that summary with the six steps: strict inner-horn lifting; dual cancellation
   and comparison; transitivity via mapping-space criteria and pasting; exact
   adjustment of component lifts via the core Kan fibration; the fibration
   definition; and projection of the comparison triangle for the converse.
   Each non-elementary step names the corresponding DAG nodes, including the two
   proof dependencies that do not yet have recorded modules.
2. The module omitted the available proof-dependency imports required by stage-2
   rule 7. I added non-public imports of
   `InnerFibrationEquivalenceOuterHornLift`, `InfinityMappingComposition`,
   `InfinityCocartesianMappingCriterion`, and `CoreKanFibration` under
   `Sheaf.CategoryTheory`. The other two theorem proof dependencies,
   `lem-coef-infinity-cocartesian-composition-initiality` and
   `lem-coef-infinity-homotopy-pullback-pasting`, currently have no recorded Lean
   modules; they are named in the proof plan and cannot yet be imported.

No semantic mismatch was found. I kept the full theorem signature and node record
unchanged, verified `lean.statement` equals the signature verbatim, checked every
line is at most 100 characters, and confirmed there is just one theorem whose
entire proof remains `sorry`. There is no new definition, hollow data, local
notation, private declaration, or new proof. The prescribed `scompile.py Q102
lem-coef-infinity-cartesian-fibration-pullback
lean/Sheaf/CategoryTheory/CartesianFibrationPullback.lean`, run from the sandbox,
compiled both sandbox and library forms successfully in 1.3 seconds each, with
no warnings or errors.
