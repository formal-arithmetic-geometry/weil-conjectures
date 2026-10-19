## Worker report

The module `lean/Sheaf/CategoryTheory/ArrowJoinGeometry.lean` defines the source-restricted
arrow simplicial set, its inclusion and target evaluation, the restricted-slice source map,
and the canonical slice cocone.  `ArrowJoinGeometry` records the complete statement of
`lem-coef-infinity-arrow-join-geometry`; `arrow_join_geometry` asserts its existence with a
`sorry` proof for stage 3.  The module uses one universe `u`, simplicial sets throughout, and
requires only `[Quasicategory C]`.

The first fields render the full subcategory of arrows whose source satisfies `P`, its source
map `pi` (with the strict equation to initial-vertex evaluation), quasicategory structure, and
`SSet.Enhanced.cocartesianFibration` of target evaluation.  For each `c`, `psi c` has domain
`pullback (rightVertexSliceProjection C c) (fullSubcomplex C P).ι` and codomain the strict target fiber; the fields state
its `IsFunctorEquivalence`, the `sliceArrowPrism` formula degree by degree, and exact source
projection.  The `identity` map supplies identity arrows and `identity_final` states finality
via `IsTerminal` in each target fiber.

The relative join is `relativeJoin (arrowJoinTarget P) (𝟙 C)`, using target evaluation,
as in Kerodon 0302, proof paragraph beginning “Regarding K as an object”.  The fields `S_source`
and `S_target` render its two endpoint restrictions.  The edge `beta` has the two required
functor-category faces and `beta_formula` fixes the canonical composite from the identity-base relative join.
`beta_constant` uses `IsConstantTransformation`, equality with the degenerate identity edge
in the entire functor simplicial set (including all higher components).  `join_lift_interval` and `join_lift_base` state the
specified `(b,k_c)` interval/base restrictions through the two projections of
`relativeJoinSnd`; `T_formula` identifies the resulting map with the induced `delta star 1`
map.  The fields `j_join` and `j_cylinder` determine `j` by the two relative-join projections,
with the strict-fiber projection, join-block interval and constant simplex at `c`. This is
the recorded `relativeJoinFiberCone` construction, transported to the reversed fiber-factor
convention of `fiber`; no arbitrary cone map is substituted. The maps `j`, `j_slice`,
`gamma_plus`, and `gamma_minus` state the two cone comparisons.
Their face fields identify `T`, `i_C k_c`, and `j_c psi_c^{triangleright}`; apex fields use
`IsIdentityComponent`; the plus base field is the component `beta_a`; and the minus base field
factors through the source-restricted arrow inclusion with source identity, target `e`, and
source projection the degenerate identity edge (not merely its initial vertex).
Its last equality also specifies that target evaluation of the square is the slice
edge `((arrowJoinSliceVertexInclusion (fullSubcomplex C P) c).app _ a).val`.  Thus each hypothesis and clause in the node statement
has an explicit field in the structure.

Dependency declarations used are:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`, including `fullSubcomplex`, `evaluation`,
  `constantDiagrams`, `diagramVertex`, `IsFunctorEquivalence`, `IsTerminal`, and mapping-space
  primitives.
- `Sheaf.CategoryTheory.RelativeJoin`, including `relativeJoin`, its projections and
  inclusions, `relativeJoinMap`, `joinBlockParameter`, and the identity-base construction.
- `Sheaf.CategoryTheory.InfinityFibrations`, including `cocartesianFibration`.
- `Sheaf.CategoryTheory.SliceArrowEquivalence`, including `rightVertexSlice`,
  `rightVertexSliceProjection` and `sliceArrowPrism`. The restricted slice is Mathlib
  `Limits.pullback` of this entire-face projection and the full subcomplex inclusion; its
  two displayed maps are exactly the pullback projections, without a duplicate slice notion.
- `Sheaf.CategoryTheory.JoinSliceDiagramIsomorphisms`, including `rightConeExtension`.

I checked the empty subcategory `P = fun _ => False`, the empty simplicial set, `P = True`,
identity arrows and the terminal one-vertex simplicial set.  The strict fiber and finality
fields remain meaningful in empty cases, and no nonemptiness or repleteness hypothesis is
introduced.  The source and target endpoint orientations were checked against the `δ 1`
(source) and `δ 0` (target) conventions in the recorded fibration declaration.

Searches for existing notions and statements were made before writing:

- `msearch.py Q60 lem-coef-infinity-arrow-join-geometry leanfinder` for arrow-evaluation
  cocartesian fibrations and slice diagonal equivalences: only ordinary `CostructuredArrow`
  and nerve hits, no match.
- `msearch.py ... loogle "Quasicategory, KanExtension"` and `"Cocartesian"`: primitive
  inner-fibration or ordinary-category declarations only.
- `msearch.py ... grep "relative.?join|arrow.?correspondence|slice.?diagonal|gamma"`
  in Mathlib AlgebraicTopology and the project: no exact declaration.
- `rg` over `WeilConjectures/`, `lean/Sheaf/`, and `dag/nodes/` for the item id and
  `arrowJoinGeometry`: no existing statement or declaration.  The existing slice-arrow and
  join-cone modules were read and reused; they do not state the varying-source arrow geometry.

No statement correction, new definition node, dependency repair, or `STATEMENT-DISPUTED` flag
was needed.  The item node adds the two reviewed landed interfaces used directly for the vertex slice /
prism and the canonical cone. It does not depend on the downstream mapping-restriction theorem.

## Saved-packet self-check and repairs

The first prescribed dry run was started on the retained packet. While it waited for server
worktree capacity, I compared the saved fields with the current node and reopened Kerodon
0302 online (https://kerodon.net/tag/0302), especially the paragraphs defining the relative
join via target evaluation, the formula for beta, and the square defining gamma-minus.
The following mismatches in the saved Lean were repaired without changing the node statement:

- The main join used the source map. It now uses `arrowJoinTarget P` everywhere; the endpoint
  equation for `S_source` still uses source evaluation as the source requires.
- The old last square clause only fixed the initial vertex of `pi(q)`. It now fixes the
  entire edge to the degeneracy at the slice source and fixes target evaluation to the underlying slice edge.
- `IsConstantTransformation` previously imposed componentwise identities only. It now means
  equality of the entire edge with `sigma 0 (diagramVertex F)`.
- Added `beta_formula`, the canonical identity-relative-join formula, and `j_join` /
  `j_cylinder`, specifying both projections of the canonical fiber-cone map, so their data
  cannot be replaced by arbitrary maps with the same endpoints.
- Restored all currently recorded proof-dependency modules as ordinary imports (statement
  imports remain public), and copied the complete five-step DAG proof into the theorem's
  docstring, including the support filtration and gamma-minus simplex formulas.
- Refreshed the copied node from the shared current source before retaining only the `lean`
  record and the two permitted landed statement-dependency additions. The item statement,
  proof, source and all other current base fields are unchanged.

The first dry run reported a cycle through the added mapping-restriction dependency:
`arrow-join-geometry -> kan-mapping-restriction -> relative-kan-existence -> arrow-join-geometry`.
I removed that dependency and its import, and used the strict pullback of the already
recorded `rightVertexSliceProjection` along `A.ι` instead. This is precisely the node's
`A ×_C C_{/c}`, with Mathlib's real pullback data and no new chosen object. The helper maps
are now its two pullback projections. This preserves the exact full initial-face condition
in every degree, and removes the downstream dependency rather than waiting on it. The
initial preflight's signature mismatch was also fixed by ending the recorded signature
immediately before `:=`, as its parser requires. The third diagnostic, no second-reading
section, belongs to the separate second reader and is waived by the worker dry-run wrapper.

The final module, including all proof imports and the pullback repair, compiled cleanly
through `scompile.py`: sandbox 2.8 s, library module 3.6 s, no warnings or errors.
No node correction, new node, dependency module, or disputed statement is needed.

## Worker clause-by-clause self-check

The saved packet contained an earlier self-check claiming no mismatch.
That check is superseded by the explicit repairs above. This worker has checked the repaired
file against each node clause: `C` and `P` express exactly a full subcategory of a
quasicategory; `K_quasicategory`, `target_cocartesian`, `fiber_quasicategory` and
`slice_quasicategory` state the four structure assertions; `psi_equivalence`, `psi_prism`
and `psi_source` express the canonical equivalence over the source; `identity_final` fixes
the identity vertex and finality. `S_source`, `S_target`, `j_slice`, `beta_formula` and
`beta_constant` give the exact endpoint and normalization equations. `join_lift_interval`,
`join_lift_base`, `T_formula`, both gamma face pairs, both apex identity fields and both base
fields render every remaining cone-comparison clause. Empty and non-replete full subcategories
are allowed. This is the worker's self-check; the separate second reader must independently
read this repaired packet and write the required second-reading section before delivery.

The sole unstated proof prerequisite `lem-coef-simplicial-right-fibration-presentation`
has no recorded Lean module to import; it remains cited in the complete proof docstring.
All other recorded proof dependencies are imported; no import cycle was found.

## Second reading by Q60

I independently opened the current shared node, the delivered node and the complete
`ArrowJoinGeometry.lean`, then read the five statement-dependency nodes and the declarations
they record. The source is Kerodon, not Stacks: I read the proof of
[Proposition the project server](https://kerodon.net/tag/0302), in particular its arrow correspondence,
target-based relative join, beta, and both cone comparisons, and also opened
[0478](https://kerodon.net/tag/0478), [02VT](https://kerodon.net/tag/02VT), and
[02J2](https://kerodon.net/tag/02J2). The auxiliary lifting problem in 0302 is not a
hypothesis of this extracted geometry statement; its coefficient categories and
isofibration are not needed for these constructions. No statement correction is present
or needed, so there is no correction/citer audit to perform.

Here is my inventory of the node, matched to the actual Lean fields. Each verdict is PASS.

1. Objects and hypotheses: a small quasicategory `C` and an arbitrary full subcategory
   `A`. The theorem binds `{C : SSet.{u}} [Quasicategory C]` and
   `(P : C _⦋0⦌ → Prop)`; `A` is `(fullSubcomplex C P).toSSet`. The recorded
   `fullSubcomplex` tests every vertex of each simplex. No closure under equivalences,
   nonemptiness, finiteness, or additional structure is required.
2. `K` is the full subcategory of `Fun(Delta[1], C)` on arrows with source in `A`.
   `arrowJoinSubcategory P` applies that same `fullSubcomplex` to the internal hom,
   testing `evaluation ... 0`. `arrowJoinSubcategoryInclusion` is its actual inclusion.
3. Source `pi : K → A` and target `u : K → C`: the structure's `pi_source` fixes the
   entire source map after inclusion, and `arrowJoinTarget P` is inclusion followed
   by evaluation at vertex 1. The orientation agrees with source `δ 1`, target `δ 0`.
4. `K` is a quasicategory and `u` is cocartesian: `K_quasicategory` and
   `target_cocartesian` assert precisely these facts. I read `cocartesianFibration`:
   it includes inner lifting and cocartesian lifts at each prescribed source, and
   receives the asserted structure on `K` rather than requiring it as a hypothesis.
5. For every vertex `c`, the strict fiber is a quasicategory:
   `fiber_quasicategory c`. The recorded `fiber` orders the factors as
   `{c} ×_C K`; its `pullback.snd` is the projection to `K`. This is the same fiber
   as the node's `K ×_C {c}`, with its point coordinate retained.
6. `I_c = A ×_C C_{/c}`, with an entire initial-face condition: the actual domain
   is `pullback (rightVertexSliceProjection C c) (fullSubcomplex C P).ι`.
   The dependency's `rightVertexSlice` consists of degree `n+1` simplices ending at
   `c`, with `appendLast` operators, and its projection is the last face `δ (Fin.last _)`.
   Thus the pullback restricts the whole initial face, not just its first vertex.
   `slice_quasicategory c` gives the stated quasicategory assertion.
7. Canonical slice diagonal and equivalence: `psi c` has exactly the preceding
   domain and strict-fiber codomain, and `psi_equivalence c` uses the recorded
   quasi-inverse/coherent-natural-equivalence definition, not just an equivalence
   of homotopy categories. `psi_prism` fixes its value in every degree by
   `sliceArrowPrism n.unop.len`. I read that prism's definition: its indexing map
   sends `(0,j)` to `j` and `(1,j)` to the last vertex. The swapped factor order
   is the internal-hom convention. `psi_source` states exact equality over `A`.
8. Identities and finality: `identity_source` fixes `identity` to the constant-arrow
   map on all simplices. For every `a : A_0`, `identity_final a` provides the vertex
   above `a`, identifies its projection with `identity a`, and asserts `IsTerminal`
   in that fiber. I checked that `IsTerminal` means contractibility of every
   incoming right-pinched mapping space; it does not assert that `a` is final in `C`.
9. The join is `relativeJoin (arrowJoinTarget P) (𝟙 C)`, using target evaluation.
   The recorded relative join is the degreewise pullback with the split-simplex
   formula. `S`, `S_source`, and `S_target` give the required map and its two
   strict endpoint restrictions. `j_slice` gives `S j_c psi_c^triangle = k_c`.
10. The canonical cocone `k_c` is `arrowJoinSliceCocone A c`, using
    `rightConeExtension c` on the actual first pullback projection. I opened
    `IsRightConeExtension` and `existsUnique_rightConeExtension`: the apex and
    every top joined simplex prescribe the cone, including its value for empty
    input. This is not a choice of an unspecified extension.
11. Canonical `j_c`: `j_join` and `j_cylinder` fix both projections of `j c` to
    `(r star c)` and `(joinBlockParameter, const c)`. I compared them with the
    recorded `relativeJoinFiberCone` formula. They specify that construction for
    the reversed fiber-factor convention used by `fiber`; the two projections
    determine a map into this concrete pullback uniquely.
12. `delta star 1` and beta: `identity_join_compat` is the needed equality over `C`;
    `beta_formula` is the composite through `relativeJoinIdentityIso.inv` and
    `relativeJoinMap`, with the product braiding required by uncurrying.
    `beta_faces` fixes the prescribed endpoints. `beta_constant` uses equality
    with the degenerate identity edge of the entire functor simplicial set, so
    the higher components of `S beta` are constant too.
13. `b`, factorization of `(b,k_c)`, and `T_c`: `join_lift_interval` fixes `b` to
    `joinBlockParameter I_c Delta[0]`, and `join_lift_base` fixes the base
    coordinate to `k_c`. Together these state the prescribed factorization
    into `relativeJoin A.ι (𝟙 C)`. `T_formula` defines its composite with the
    induced relative-join map, rather than allowing an arbitrary `T`.
14. `T_c^+` and `T_c^-` are written out in `gamma_plus_faces` and
    `gamma_minus_faces`, respectively as `k_c ≫ relativeJoinInr ...` and
    `orderedJoinFunctor.map (psi c, 𝟙 Delta[0]) ≫ j c`. Both gamma values are
    genuine degree-one simplices of the full internal functor object, so all
    coherence data are retained. Their source is `T c` and their targets are
    the specified two cone diagrams.
15. Both apex components are identities: `gamma_plus_apex` and `gamma_minus_apex`
    evaluate at the actual right-cone inclusion of its unique apex.
    `IsIdentityComponent` compares the whole component edge to the corresponding
    degenerate edge. The target diagram at that apex is `i_C(c)` by the cone and
    `j_c` formulas already checked.
16. Plus base components: `gamma_plus_base` equates evaluation at every base
    vertex `e` with evaluation of beta at its source in `A`, exactly `beta_a`.
17. Minus base components: `gamma_minus_base` produces an actual edge
    `q : Delta[1] → K`, identifies its image under `i_K` with the component,
    fixes its source to `identity a` and its target to `psi_c(e)`, fixes the
    whole edge `pi(q)` to `σ 0 a`, and fixes target evaluation to the underlying
    slice edge `e`. Thus both vertical sides of the required square are fixed,
    not merely their endpoints. The existential `q` introduces no extra
    hypothesis and supplies precisely the component specified by the node.
18. Quantifier order and scope: the theorem asserts `Nonempty (ArrowJoinGeometry C P)`.
    Consequently the source map, identity map, `S`, and beta are selected together,
    followed by all vertex-indexed slice and cone data, with their shared equations.
    No limit, colimit, coefficient category, or lifting theorem is concluded.

Edge cases checked independently: if `P` is false, `K`, all its strict fibers, and
all restricted slices are empty, while each right cone retains its apex; there
are no identity-finality obligations over nonexistent vertices. If `C` is empty,
all clauses quantified over its vertices are vacuous and no inhabitance is
assumed. If `P` is true the unrestricted arrow category is recovered. A full
subcategory need not be replete. For a one-vertex terminal quasicategory the
identity/finality and constant component clauses have their expected values.
Degree zero is included by `n : SimplexCategoryᵒᵖ`, with the prism then giving the
original slice edge. There are no ring, characteristic, scheme, or numerical
parameters to restrict. All constructions stay in the single arbitrary universe
`u`, exactly the node's sufficiently large common-universe convention.

Independent searches used different concept queries from the worker:

- `msearch.py Q60 lem-coef-infinity-arrow-join-geometry leanfinder` with
  `restricted arrow quasicategory target evaluation cocartesian fibration slice
  diagonal relative join cone comparisons`: ordinary `CostructuredArrow` cone
  and ordinary fibered-category results, but no statement of this geometry.
- Loogle `SSet, Quasicategory` did not recognize the unqualified second identifier;
  the follow-up query `"SSet.Enhanced"` returned no matches. Neither is used as
  evidence of a positive match.
- The prescribed grep search for `source.*target.*fibration|slice.*prism|
  IsIdentityComponent|IsConstantTransformation` returned no existing match.
  Direct `rg` in Mathlib, upstream `WeilConjectures`, and shared `lean/Sheaf`
  confirmed no declarations named `arrowJoin*`, `ArrowJoinGeometry`,
  `arrow_join_geometry`, `IsConstantTransformation`, or `IsIdentityComponent`.
  Broader searches for oriented fibers, restricted arrows, slice diagonals and
  arrow correspondences found the reused slice modules and the distinct
  two-functor correspondence in `InfinityPointwiseAdjointCriterion`, which
  does not state the join/cone geometry. The upstream name table has no binding
  for this item. No duplicate notion requiring an existing attachment was found.

H4/H5/H6/H8/H9 checks: all helper definitions use actual existing simplicial
constructions or explicit equalities. The two dependency choices used for the
cone extension and join-block parameter come from uniqueness statements fixing
all their data. The main theorem is the sole postponed theorem in this file;
its proof remains `sorry`. Every declaration has the source/blueprint docstring,
and the theorem docstring contains all five DAG proof texts verbatim modulo
whitespace, including the support filtration and the gamma-minus formulas.
The recorded `lean.statement` is verbatim the signature before `:=`; all lines
are at most 100 characters and `autoImplicit` is false. The existing statement
dependencies have usable interfaces, so no new node or dependency repair is
needed. The only unstated proof prerequisite is the one already reported by
the worker; all recorded proof modules and Mathlib proof leaves are imported.

No further mismatch was found in the worker's repaired packet. I changed only
this report by adding the independent reading; the Lean and node were retained.
The required `scompile.py` check run from this sandbox compiled both the sandbox
probe (3.4 seconds) and the library module (3.7 seconds), with no diagnostics.
