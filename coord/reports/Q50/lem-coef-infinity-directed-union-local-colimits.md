## Worker report

The module `Sheaf.CategoryTheory.InfinityDirectedUnionLocalColimits` states
`SSet.Enhanced.infinity_directed_union_local_colimits`, with exactly one postponed theorem
and no proof other than `sorry`. Its seven helpers construct the directed-cover collage,
its canonical cell/inclusion maps, the predicate asserting the canonical cocone
comparison, and canonical postcomposition of coherent cocones. No data are chosen from an unproved existence theorem. No new DAG node or
dependency repair is needed. The item statement, proof and proof dependencies are unchanged.
The Q108 review is the stage-1 split, not an existing Lean binding; the sandbox initially
contained only dispatcher markers and the shared node had no `lean` record.

Source read: Lurie, Higher Topos Theory, online IAS PDF, Notation the project server, Remark the project server,
Proposition the project server, Remark the project server and Corollary the project server, printed pp. 248–253.
The proposition constructs an extension of the given local join cocones; its final clause
and the corollary give the two actual restriction maps. I used this restriction span,
rather than choosing an unrelated equivalence between cocone spaces. The module docstring
and theorem docstring give all seven steps of the node proof, including their named DAG
inputs, and the compatibility with postcomposition.

Hypotheses and clauses, with the node and Lean open:

- The small simplicial set is `K : SSet.{u}`. The ambient quasicategories are
  `SSet.{max u v}`, with independent `u` and `v`. The small shape, subsets, nerve and
  constructed collage are embedded by Mathlib's canonical degreewise
  `SSet.uliftFunctor.{v}`. All universes and variables are explicit and `autoImplicit`
  is false. There is no cardinality restriction on the ambient quasicategories and no
  forced equality between the shape and ambient universes.
- The small nonempty partially ordered set is `I : Type u`, `[PartialOrder I]`, `[Nonempty I]`.
  `hdir : ∀ s : Finset I, ∃ j : I, ∀ i ∈ s, i ≤ j` is exactly the upper-bound condition
  for every finite subset, including the empty subset.
- The simplicial subsets are `U : I → K.Subcomplex`. `hmono : Monotone U` expresses increasing
  inclusion and `hcover : iSup U = ⊤` expresses their degreewise union being `K`.
- The target and diagram are `E : SSet.{max u v}`, `[Quasicategory E]`,
  `p : SSet.uliftFunctor.{v}.obj K ⟶ E`. There is no
  colimit-existence assumption on `E`. The selected coherent cocones are the vertices
  `lam i : coconeCategory (SSet.uliftFunctor.{v}.map (U i).ι ≫ p)`, and `hlam` states `IsColimiting` for each one.
- `localUnionCell U n tau` is the canonical map
  `K_(tau(0)) ⋆ Delta[n] → K ⋆ N(I)`. `localUnionCollage U` is the supremum of its ranges
  and the two pure-factor ranges. For a monotone family its mixed simplices are exactly
  those whose lower block belongs to the subset of the first upper vertex: every such
  simplex is in its corresponding chain cell; every face of a chain cell still satisfies
  this condition by monotonicity. Both pure factors are retained, even for empty shapes.
- The existential `q` is an extension to this specified collage, with
  `SSet.uliftFunctor.{v}.map (localUnionShape U) ≫ q = p`. Its assembly is the actual restriction
  `SSet.uliftFunctor.{v}.map (localUnionIndex U) ≫ q` on the lifted nerve. The vertex equation fixes each vertex to the
  selected apex `(lam i).1.1`.
- The local right-cone maps are `localUnionCone U i`. The witnesses `μ i` are their entire
  induced coherent transformations, fixed by the equation on `rightJoinPrismSimplex` for
  every degree, every local simplex and every interval simplex. The prism is lifted
  degreewise; interval simplices in the two universes are canonically identified by
  `stdSimplex.objEquiv`, so the equation covers every ambient interval simplex. The equivalence edges
  `e i` identify these representatives with `lam i` in the fixed-base cocone category;
  their image under `gluingCoconeApex` is the degenerate edge at the chosen apex. Thus the
  prescribed cocones are retained up to coherent equivalence with the same apex, as the
  source's fixed-boundary, fixed-vertex join comparison requires. Strict equality to an
  arbitrary chosen fat cocone would impose an extra normalization and is not asserted.
  Mixed triangles and higher mixed simplices of `q` supply exactly the transition maps
  induced by restriction and all their coherences.
- `LocalUnionCoconeComparison U q` asserts weak homotopy equivalence of the two ACTUAL
  `mappingSpaceMap` restrictions, at every apex `t`. Their sources are the mapping spaces
  of `q` to the constant diagram; their targets are its restricted endpoints. Naturality
  of `constantDiagrams` identifies the second endpoints with the respective constant
  diagrams. Consequently their span is precisely the equivalence in the node. This is
  the standard representation of an equivalence of spaces by a span of weak equivalences;
  no arbitrary map or arbitrary inverse is substituted for restriction.
- Naturality in `t` and the leg formula are retained by this single span of restriction
  maps on entire coherent functor categories. Every simplex is precomposed with the
  specified shape/nerve inclusions. Restricting to `localUnionCone U i` yields the mixed
  triangles expressing composition with `μ i`, hence with `lam i` through `e i`. This
  encodes all compatible legs and their higher simplices, rather than only a bijection
  on components or a noncanonical existence of an equivalence for each `t`.
- The second part of `LocalUnionCoconeComparison` is the biconditional for `IsColimiting`
  on the two restrictions of every coherent collage cocone `μ`, using the actual
  `gluingCoconeRestrict` maps. Both have exactly `μ`'s apex. Together with the fixed-apex
  weak equivalences this gives the asserted criterion for corresponding cocones; every
  cocone class on either side is represented by the span, and equivalence does not change
  colimitingness.
- The final universal clause permits any quasicategory `E'` and simplicial functor `H`.
  `localUnionPostcomposeCocone H (lam i)` is a real construction of the canonical image
  cocone: its apex is `H.app _ (lam i).1.1`, and its arrow is obtained by both internal-hom
  maps of `H`. Naturality of evaluation and of constant diagrams supplies its two endpoint
  proofs. Only `IsColimiting` of these actual image cocones is assumed. There is no
  user-supplied comparison map, choice, or additional image-cocone data. The conclusion is
  the SAME comparison predicate for `q ≫ H`, using the same collage and inclusions.
  Its assembly is thus exactly `Hc`. Restriction and postcomposition commute in every
  simplicial degree; after inversion of the weak equivalences their comparison commutes
  up to coherent equivalence, as required.

Dependency declarations used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.mappingSpace`,
  `mappingSpaceMap`, `diagramVertex`, `constantDiagrams`, `IsWeakHomotopyEquivalence`,
  `IsEquivalenceEdge`, `coconeCategory` and `IsColimiting`. I read their full definitions
  and docstrings, including the right-pinched whole-initial-face and comma conventions.
- `Sheaf.AlgebraicTopology.PushoutJoinSaturation`: `SSet.Enhanced.orderedJoinFunctor`.
  The terminally augmented convolution is the ordered simplicial join. Its landed owner
  was added to `stmt_deps`. The pure-factor maps `orderedJoinInl` and `orderedJoinInr` are
  defined in `Sheaf.CategoryTheory.JoinSliceRightFibration`, publicly available through
  `RelativeInfinityCone`; I read both full convolution-generator formulas and docstrings.
- `Sheaf.CategoryTheory.RelativeInfinityCone`: `SSet.Enhanced.rightJoinCone`, the existing
  ordered right cone; its landed owner was added to `stmt_deps`.
- `Sheaf.CategoryTheory.CoconeRestrictionInitial`: `SSet.Enhanced.rightJoinPrismSimplex`,
  the canonical right-cone cylinder formula. Its landed owner was added to `stmt_deps`.
- `Sheaf.CategoryTheory.FinalIndexColimit`: `SSet.Enhanced.coconeHomotopy`, extracting the
  entire coherent transformation. Its landed owner was added to `stmt_deps`.
- `Sheaf.CategoryTheory.InfinityColimitGluing`: `SSet.Enhanced.gluingCoconeApex` and
  `gluingCoconeRestrict`, which fixes the apex and precomposes all coherent simplices.
  Its landed owner was added to `stmt_deps`.
- Mathlib: `SSet`, `SSet.Quasicategory`, `CategoryTheory.nerve`, `ComposableArrows.mk₀`,
  `SSet.Subcomplex.range/lift`, lattice suprema, `MonoidalClosed.pre`, and `yonedaEquiv`.
  Every new inclusion is an actual range lift with an explicit lattice-inclusion proof.

Already-stated proof inputs are imported non-publicly:
`Sheaf.CategoryTheory.InfinityJoinConeCalculus`,
`Sheaf.CategoryTheory.RelativeInitialBoundary`,
`Sheaf.AlgebraicTopology.AnodyneCocones`,
`Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`, and
`Mathlib.AlgebraicTopology.SimplicialSet.Skeleton` (the Mathlib match
`SSet.relativeCellComplexOfMono`). The three other proof inputs
`lem-coef-decomposition-local-colimit-cocones`, `lem-coef-join-slice-cocone-comparison`
and `lem-coef-directed-decomposition-right-anodyne` have no recorded Lean module;
they occur in the proof docstring but no nonexistent import was invented. The statement
does not depend on their unformalized theorem assertions.

Edge cases checked: a singleton index gives a local-colimit diagram and its cocone
comparison; `K = ∅` makes every `U i` empty and the collage just its pure indexing nerve,
with all chosen apices initial; an individual empty `U i` contributes the initial-object
right cone and its initial transitions; no nonemptiness is imposed on any `U i` or `K`.
Empty `E` cannot supply the stipulated local cocones since `I` is nonempty. The empty
finite subset in `hdir` has an upper bound. Chains with identities and degenerate simplices
are included in `localUnionCell`. No shape is required to be a quasicategory. A target
having just the stipulated local colimits satisfies every hypothesis; cocompleteness is
absent. No statement dispute or node correction remains.

Searches actually run using `msearch.py`, with logs in this sandbox's `searches.jsonl`:

- LeanFinder: "Coherent colimits of a diagram over a directed union of simplicial subsets
  assemble from chosen local colimits in a quasicategory". Eight hits, including
  `SSet.Subcomplex.MulticoequalizerDiagram.isColimit`, `SSet.horn.isColimit`, and
  `SSet.hasColimits`. Read `SubcomplexColimits.lean:51–77`: these are ordinary colimits
  in the category of simplicial sets, not colimits of diagrams inside a quasicategory.
- Loogle: `"colimit", "Subcomplex"`. Three hits, the two multicoequalizer declarations
  and preservation by `Subcomplex.toSSetFunctor`. None states this node.
- Grep: `directed.*colimit|colimit.*directed|union.*colimit` in Mathlib/AlgebraicTopology.
  Zero hits.
- LeanSearch: "Coherent cocones over a directed union of simplicial subdiagrams are cocones
  on their chosen local colimit diagram". Eight ordinary-category cocone/colimit hits;
  no coherent local-colimit comparison.
- Direct `rg` of the upstream `WeilConjectures` tree by the item id and directed-union
  vocabulary found no statement; the only directed-union text hit was a field-theory
  comment. Direct searches of `lean/Sheaf`, `dag/lean_names_upstream.json` and the relevant
  category modules found `DirectedCoverColimitAssembly`, which assumes all small colimits
  and asserts existence of a global colimit, so it is not this local-only comparison.
  `InfinityDirectedConeCover` concerns already-conical covering shapes, not chosen local
  colimits in an arbitrary target. I opened both modules and their full theorem signatures.
- Exact searches for the proposed declaration names in Mathlib, upstream and
  `lean/Sheaf` found none. The covering collage is constructed here rather than postulated;
  its helpers belong to this statement as permitted by the missing-helper instruction.

Validation of the resumed worker pass (2026-10-17 UTC): the entire module was read
against the current node and the source declarations of all six statement dependencies.
The three search methods were repeated and still found no existing statement.
The canonical postcomposition helper was also searched by concept in the category-theory
modules; no existing construction of image cocone vertices was found.
`scompile.py Q50 lem-coef-infinity-directed-union-local-colimits` compiled both the
sandbox file (2.5 seconds) and its named-library form (2.6 seconds) cleanly, with
no unexpected warnings. All variables are explicit; no Lean line exceeds 100 characters.
The node's `lean.statement` was checked verbatim against the theorem signature and its
date refreshed to 2026-10-17 UTC. No mathematical statement correction or dependency
repair was needed. The additional `stmt_deps` are the already-landed owners listed above.

The required `deliver2.py --no-push` dry run is the final validation. The independent
second-reading section belongs to the next worker and has not been written here;
no delivery is pushed by this worker.

## Second reading by Q50

I independently read the sandbox node and complete module against HTT Notation
the project server, Remark the project server, Proposition the project server, Proposition the project server,
Remark the project server and Corollary the project server, printed pp. 248--253, in the sandbox's
HTT PDF/text. This is a quasicategorical result, not a Stacks ordinary-category
colimit lemma. The section's standing data are a simplicial set K, an ordinary
category I and a functor to simplicial sets over K. Remark the project server specializes
these to the monotone directed cover in this node. The source assumes neither
cocompleteness nor nonempty indexing subsets. Proposition the project server preserves
specified join cocones and gives the first restriction; the corollary gives the
second restriction. The present node expresses the resulting fixed-apex coherent
cocone comparison and its compatibility with functors.

My object/hypothesis/conclusion inventory and its Lean match follows. Every item
passes; I found no mismatch requiring a Lean or mathematical node change.

1. Small simplicial set K: `K : SSet.{u}`. No inner-horn or nonemptiness
   hypothesis is imposed on the shape. The family consists of actual simplicial
   subsets, `U : I → K.Subcomplex`, rather than arbitrary subcategories or a
   vertex-only cover.
2. Small nonempty partially ordered index with finite upper bounds:
   `I : Type u`, `[PartialOrder I]`, `[Nonempty I]`, and
   `hdir : ∀ s : Finset I, ∃ j : I, ∀ i ∈ s, i ≤ j`. This includes the empty
   finite subset; the explicit nonempty instance repeats the node's assumption
   and permits the ordinary nerve API. The index and shape inhabit the same
   small universe as required by the project convention.
3. Increasing family with union K: `hmono : Monotone U` and
   `hcover : iSup U = ⊤`. Suprema of subcomplexes are degreewise unions, so this
   covers all simplices, not just vertices. Monotonicity also supplies the
   compatible transition inclusions.
4. Arbitrary quasicategory and diagram: `E : SSet.{max u v}`,
   `[Quasicategory E]`, and `p : SSet.uliftFunctor.{v}.obj K ⟶ E`.
   Mathlib's `uliftFunctor` is degreewise ULift. It changes the encoding of the
   small shape, not its simplices or operators. Independent `u v` permit a
   containing ambient universe; there is no local smallness or colimit-existence
   instance. Both targets of H use the fixed sufficiently large ambient universe
   of the dependency convention.
5. A chosen colimiting cocone for every restricted diagram: `lam i` is a vertex
   of `coconeCategory (SSet.uliftFunctor.{v}.map (U i).ι ≫ p)`, and `hlam i`
   asserts `IsColimiting` of precisely that cocone. Reading the owning
   `EnhancedDiagramsCones` definitions confirms that this is the full coherent
   comma cocone, and colimiting means initial therein. No alternate notion of
   colimit is substituted.
6. Coherent assembly with the chosen vertices: the existential map `q` extends
   p on `localUnionShape U`; its restriction along `localUnionIndex U` is c on
   the lifted nerve. The following vertex equation gives exactly `(lam i).1.1`.
   I checked `localUnionCell`, `localUnionCollage` and their three inclusion
   maps: they use the actual ordered join, ranges and their lattice supremum.
   For a monotone family, a mixed simplex in a cell has lower simplex in
   U(tau(0)); if an operator deletes the first upper vertex, monotonicity puts
   it in the later subset. Conversely each allowed mixed simplex is in the
   cell of its own upper chain. The separate pure factors include every pure
   simplex. This is exactly the subset-case K_F of HTT the project server.
7. Transitions induced by restriction of the prescribed cocones, with all higher
   coherences: `localUnionCone U i` is the zero-dimensional cell. The existential
   `μ i` has exactly the chosen apex, and the prism equation fixes its entire
   transformation in every degree. `e i` has source μ_i, target lam_i, is an
   equivalence edge, and projects under `gluingCoconeApex` to the degenerate
   edge at the chosen apex. This is the fixed-base, fixed-apex identification
   needed when passing between join and coherent comma cocones. Mixed triangles
   and longer simplices of q give the transition compositions and their higher
   compatibilities. The condition does not identify only the local vertices.
8. Equivalence of the two full spaces of t-valued cocones, natural in t, with
   the specified composition-of-legs formula: the first half of
   `LocalUnionCoconeComparison U q` tests both canonical `mappingSpaceMap`
   restrictions, for every vertex t. Their common source is the space from q
   to the constant diagram on the collage; their targets restrict q and the
   constant diagram to K and N(I). The extension equation identifies the first
   restricted diagram with p, and naturality of `constantDiagrams` identifies
   the endpoints with the appropriate constants. Thus the equivalence is the
   actual span of weak equivalences, not an arbitrary objectwise equivalence.
   The maps are restriction on whole functor simplicial sets, retaining coherent
   apex naturality. Restriction to each local cone gives the mixed triangles
   identifying its leg on p with its leg on c composed with μ_i, hence lam_i
   through e_i. The whole simplicial q supplies these identifications coherently.
9. Colimiting if and only if the corresponding cocone is colimiting: the second
   half of `LocalUnionCoconeComparison` quantifies over every collage cocone μ
   and compares `IsColimiting` of its two actual `gluingCoconeRestrict` images.
   The maps preserve μ's apex. The preceding fixed-apex equivalences represent
   every cocone class on either side and fix which classes correspond, so this
   is the asserted criterion, including both directions and possible absence
   of global colimits. No global cocone is assumed to exist.
10. Functor compatibility for any coherent H preserving the chosen local
    cocones: the final universal clause takes a quasicategory E' and an actual
    simplicial map H, assumes `IsColimiting` only for
    `localUnionPostcomposeCocone H (lam i)`, and asserts the same comparison for
    `q ≫ H`. I read that helper's body: it maps the apex and full transformation
    using the two internal-hom maps, with endpoint proofs from evaluation and
    constants. It chooses no cocone or inverse from existence. The same q,
    shape/index maps and collage are used before and after H, so the assembly
    is Hc and the restrictions commute with postcomposition degreewise. Their
    equivalence span therefore gives precisely the required coherent
    compatibility. No arbitrary image-cocone data are supplied as hypotheses.

Dependency reading: I opened the node statements and recorded signatures of
all six statement dependencies, and the definitions used from their modules.
`orderedJoinFunctor` is the terminally augmented convolution with the ordered
block normal form; `orderedJoinInl/Inr` use its pure-block generators.
`rightJoinCone` is that join with Delta[0]. `rightJoinPrismSimplex` retains the
initial interval-zero block and collapses the interval-one block to the apex.
`coconeHomotopy` uncurries the given cocone's transformation.
`gluingCoconeApex` and `gluingCoconeRestrict` are the actual projection and
precomposition maps. The item imports their owning dependency modules through
the published public-import chain. I also checked the current records of all
proof dependencies: the three modules reported absent by the worker remain
unrecorded, and every already-recorded proof module is imported. No new node or
dependency module is part of this delivery, and there is no `statement_change`
requiring a citer audit.

Edge cases: empty I is outside the expressly nonempty node. Singleton I and
repeated vertices in chains are included, with no strict-order or finiteness
restriction. For empty K all U_i are empty, and the collage is its pure N(I)
factor; chosen local colimits are initial objects. An individually empty U_i
likewise has an initial apex, and no prism simplex is required from its empty
domain; the apex equation and fixed-apex equivalence still apply. An empty E
cannot meet the chosen-cocone hypotheses for nonempty I. Degree zero is included
in the chain cells and prism quantifiers; the ordinal-equivalence conversion
`stdSimplex.objEquiv.symm (stdSimplex.objEquiv a)` enumerates every interval
simplex in the larger universe, not a restricted interval. There are no scheme,
ring-characteristic, or additive zero-object hypotheses in this statement.

Independent searches, using different phrases from the worker (logged by
`msearch.py` in `searches.jsonl`): LeanFinder, "A filtered cover of a simplicial
indexing set gives an equivalence between cocones over its diagram and cocones
over the diagram of local colimit objects", returned eight ordinary filtered
category/eventually-constant/Ind-object declarations. Loogle,
`"cocone", "directed"`, returned twelve scheme-cover and cardinal-directed-poset
declarations. LeanSearch, "The coherent diagram of partial colimits for a
filtered simplicial cover has the same space of cocones as the original infinity
category diagram", returned eight ordinary categorical colimit declarations.
The grep wrapper for `filtered.*(cover|cocone)|local.*colimit|colimit.*local`
returned ordinary group/module/presentability results. None is this theorem.

I also directly searched Mathlib, the upstream WeilConjectures tree, the shared
Sheaf tree and upstream name index for quasicategory covers/unions, decomposition
cocones and postcomposition cocone helpers. I opened `DirectedCoverColimitAssembly`
and `InfinityDirectedConeCover` in full: the former assumes all small colimits
and constructs global colimits; the latter starts with specified conical
covering subsets. Neither states this node. `InfinitySmallColimitGeneration`
uses this node to pass from skeleta to their union, rather than supplying it;
the cofiltered equivalence-diagram module is about diagrams of equivalences.
Mathlib `Subcomplex.MulticoequalizerDiagram.isColimit` computes a colimit in
SSet itself. There is no existing replacement or duplicate helper construction.

Repairs: none needed in Lean or the node; the second reading adds this report
section only. The module has seven real helper constructions, no hollow data,
and one named theorem with its entire proof postponed by `sorry`. Its docstring
records the node's seven proof steps and sources. I checked every binder and
universe, the absence of file-local notation/private definitions, the 100-column
limit, and exact equality of the node's `lean.statement` with the file signature.
The only node deltas from the shared base are `lean` and the five added, already
landed dependency owners. Independent `scompile.py` compilation on 2026-10-17
passed for both sandbox and library forms (2.9 s and 3.0 s), with no warnings or
errors. The required server preflight and delivery follow this reading.

## Maintainer review fix

The maintainer's second reader (cc review service) replaced the delivered helper
`SSet.Enhanced.localUnionPostcomposeCocone` with the already landed
`CategoryTheory.Spaces.mappedCocone` of `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`
(def-coef-infinity-category-of-spaces). Both have the apex `H.app _ c.1.1` and the
transformation `((ihom Δ[1]).map ((ihom L).map H)).app _ c.1.2`, so the hypothesis of the
functor clause is unchanged in meaning; only the duplicate definition (H4) goes. The module
now publicly imports that owner. Nothing else in the statement changed; the fixed file
compiles clean per file through `tools/nt_compile.py`.
