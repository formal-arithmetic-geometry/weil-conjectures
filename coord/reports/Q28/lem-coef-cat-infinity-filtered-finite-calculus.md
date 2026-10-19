## Worker report

The module `Sheaf.CategoryTheory.CatInfinityFilteredFiniteCalculus` states
`SSet.CatInfinityCalculus.cat_infinity_filtered_finite_calculus`. Its conclusion is
`Calculus` for the actual coherent nerve and enriched mapping complexes supplied
by the marked-point Cartesian model. The statement uses the universal-cocone
form of canonical comparison equivalences: the actual comparison is an
equivalence precisely when its target cocone is still colimiting. Colimit
objects and inverses are not chosen from a mere existence theorem.

The item node changes only in `lean`. No definition node, dependency replacement,
statement correction, source correction, or disputed statement is needed.
During the work, the previously unrecorded presentability dependency landed; its
published module was read through `scompile.py --source` and is now also recorded
in the shared DAG. This delivery uses that module without copying it.

### Hypotheses, universes and objects

- `M : SSet.Marked.CartesianModelStatement.{u}` supplies exactly the model in the
  third statement dependency. This is a representation parameter, not an
  additional mathematical assumption: the dependency asserts its existence.
  `M.qcat_enrichment` is passed explicitly to `Calculus`; hence the category is
  `SimplicialNerve CoherentNerve.QCats.{u}`, definitionally the dependency's
  `Marked.quasicategoryNerve M.qcat_enrichment`. `M.qcat_mapping` is the
  dependency's normalized identification with cores of internal functor objects.
- Small categories and mapping spaces have universe `u`; their coherent nerves
  have universe `u + 1`. The small index is allowed to be presented in that
  containing universe, with `Presentability.IsSmall.{u, u + 1} I`. Thus the
  statement accepts smallness of a model, rather than accidentally requiring
  every diagram to have the containing universe as its smallness bound.
- All indexing diagrams are simplicial maps into the coherent nerve. They are
  not ordinary functors into the ordinary category of simplicial sets or into a
  homotopy category. `nerveMap` composes enriched functors on every simplex.
- Filteredness is the recorded `Presentability.IsKappaFiltered Cardinal.aleph0`,
  with an explicit `hI : Quasicategory I`. It tests the empty shape too.
- Finiteness is Mathlib's `SSet.Finite`. Its definition in
  `SimplicialSet/Finite.lean` is finiteness of the type `X.N` of nondegenerate
  simplices in all dimensions. This is the exact finite-shape convention in the
  node, not degreewise finiteness.
- No transition map is assumed fully faithful, injective, or an equivalence.
  No inhabitedness of a finite shape or of a category in the diagram is added.

### Clause matching and the universal formulation

1. Small filtered colimits: the first conjunct of `Calculus` is the dependency's
   `HasSmallKappaFilteredColimits.{u, u + 1}` at `Cardinal.aleph0`. Its binders
   range over every small filtered coherent diagram and produce a genuinely
   colimiting enhanced cocone.
2. Finite limits: `HasFiniteCoherentLimits` quantifies over every finite
   simplicial set and every coherent diagram, including the empty simplicial
   set. It asserts existence of a terminal comma-cone vertex. The redundant
   universal-property interface `FiniteLimitAssembly` says that forgetting a
   universal cone to its diagram is an equivalence. This is the coherent
   formulation of the same existence statement: every diagram has a
   contractible space of limiting cones. It allows arbitrary diagrams of limits
   to assemble, without selecting their data from a postponed existence proof.
3. The canonical colimit/limit comparison: `FilteredFiniteExact` ranges over
   every finite `K` and every small filtered `I`. `limitCones K C` is the full
   subcomplex of the actual pullback of constant diagrams and source evaluation
   consisting of universal cones. A coherent diagram into it is precisely a
   family of limiting `K`-cones with their compatibility homotopies. The supplied
   cocone retains both the arrows on apices and the transformations of base
   diagrams. Its evaluations at all `k` are assumed colimiting; its apex
   cocone is asserted colimiting. Thus the apex of the limiting cone on the
   pointwise colimit is the colimit of the limiting apices. This is the universal
   property of the node's canonical comparison, with the same cone/cocone legs.
   `FiniteLimitAssembly` makes this cover every `K × I` diagram; it is not a
   test only on a possibly empty collection of preassembled limits.
4. Empty `K`: the pointwise premise in `FilteredFiniteExact` has no instances,
   while its conclusion still asserts colimitingness of the cocone of terminal
   apices. No terminal-object clause is discarded.
5. Base change over fixed `B` and `T → B`: specialize that same finite-shape
   assertion to the nerve of the walking cospan. Use the given coherent cospans
   `D_i → B ← T` and the identity cocones on the two constant entries. A filtered
   index is weakly contractible, so these are colimiting. `totalArrow` and
   `totalDiagram` retain the entire cospan; the apex arrow to `B` is therefore
   the arrow induced by those supplied structural maps. The conclusion is the
   colimitingness of the canonical cocone on `D_i ×_B T`, with target
   `C ×_B T`, equivalently the stated base-change equivalence. An unrelated
   functor `C → B` cannot be substituted in this formulation.
6. Core preservation: the fifth conjunct supplies `CoreImplementation` and
   `PreservesSmallFilteredColimits (nerveMap R.operation)`. Its object equation
   is literally `(Enhanced.core C.obj).toSSet`. Its map equation is restriction
   along both core inclusions in the full internal Hom. This specifies every
   simplex of the operation, not only its values on objects or ordinary maps.
   Its codomain is the recorded `Spaces.infinityCategory`, definitionally the
   coherent nerve of `Spaces.Kan` with the recorded enrichment.
7. Finite functor categories: the next conjunct ranges over every finite
   `L : SSet.{u}` and supplies `FunctorImplementation mapping L` preserving
   every small filtered colimiting cocone. Its values are literally
   `(ihom L).obj C.obj`. Its enriched action is the transpose of the actual
   closed-category composition `MonoidalClosed.comp L C.obj D.obj`; thus it is
   the canonical functor operation in all simplicial parameters.
8. Simultaneous finite representatives: `FiniteStageRepresentatives` explicitly
   binds any finite `K`, any map `f : K → C`, a common stage `i`, and a map
   `g : K → D_i`. It concludes `AreNaturallyEquivalent (g ≫ coconeLeg D c i) f`.
   A finite collection of vertices, edges and specified simplices is encoded by
   the finite simplicial set they generate. The equivalence is an equivalence
   edge in the full internal functor quasicategory, retaining the specified
   simplex relations. The cocone leg is extracted from the actual enhanced
   cocone; `coconeLeg_endpoints` only supplies its defining endpoint equalities.
9. Coslice: `coslice I i` is literally the recorded enhanced comma
   `comma I I (𝟙 I) i false`, whose vertices are arrows from `i` and whose higher
   simplices retain the compatibility triangles. `FilteredCoslices` explicitly
   asserts its smallness, quasicategory condition and aleph-zero filteredness.
10. Mapping-space comparisons are expressed by the universal finite-fiber
    instance of clauses 3, 6 and 7, with `L = Δ[1]` and the pair of endpoint
    evaluations. Over `I_{i/}`, the points `D(u)x,D(u)y` are the coherent
    transported endpoints. The fiber of
    `core Fun(Δ[1],D_j) → core D_j × core D_j` is the arrow-space model of
    `Map_Dj(D(u)x,D(u)y)`. Taking this finite fiber in the comparison preserved
    by clauses 3, 6 and 7 yields a colimiting cocone with apex the same fiber in
    `C`. The recorded right-pinch convention identifies that fiber naturally
    with `Enhanced.mappingSpace C (r_i x) (r_i y)`. Thus the displayed mapping
    comparison is the fiber of the canonical endpoint comparison; it is not an
    independently selected equivalence. The coslice projection is cofinal for
    filtered `I`, as in node proof steps 9--10. This is a universal-property
    presentation of the formula, not a separately chosen mapping-space model.
11. Fixed-base arrow `f` and naturality: apply the same finite-fiber instance a
    second time, now over the point `f` of the fixed base mapping space. The
    diagram of functors `D_i → B` supplies the map of endpoint/fiber diagrams.
    Because all maps in `CoreImplementation.maps`, `FunctorImplementation.maps`,
    `nerveMap`, and the universal-cone projections are maps on full simplicial
    objects, this restriction retains the compatibility with that diagram,
    precomposition, postcomposition, and every higher simplex. It asserts the
    colimitingness of the cocone of homotopy fibers, which is exactly the
    superscript-`f` comparison in the node. In particular the construction uses
    the existing enhanced homotopy-fiber convention, not a strict fiber over an
    arbitrary nonfibrant map.

The latter clauses are rendered by the same canonical universal comparison,
rather than by introducing a second noncanonical construction of the mapping
space diagram or picking colimit objects. The source's proof of Proposition
3.3.2 itself obtains its mapping formula by this finite endpoint-fiber argument.
The theorem docstring includes all eleven proof steps of the DAG node.

### Dependency declarations read and used

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.core`, `coneCategory`, `coconeCategory`, `constantDiagrams`,
  `diagramVertex`, `evaluation`, `fullSubcomplex`, `IsLimiting`, `IsColimiting`,
  `AreNaturallyEquivalent`, `IsFunctorEquivalence`; its right-pinched
  `mappingSpace` and `homotopyFiber` give the interpretations of the finite
  fiber instances.
- `Sheaf.CategoryTheory.PresentableInfinityCategory`:
  `SSet.Presentability.IsSmall`, `IsKappaFiltered`,
  `HasSmallKappaFilteredColimits`, including their full universe signatures.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`:
  `SSet.Marked.CartesianModelStatement`, `qcat_enrichment`, `qcat_mapping`,
  `qcat_ordinary_maps`, `qcat_composition`, `cat_infinity_quasicategory`,
  `SSet.Marked.quasicategoryNerve`.
- `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`:
  `CategoryTheory.Spaces.Kan`, `kanEnrichment`, `infinityCategory`,
  `mappedCocone` (the full coherent postcomposition construction).
- Existing proof imports: `Sheaf.AlgebraicTopology.GlueSimplex`,
  `Sheaf.CategoryTheory.IsofibrationExponentiation`,
  `Sheaf.CategoryTheory.IsofibrationPullbackLimit`, and Mathlib's
  `SimplicialSet.Degenerate`. The other proof-dependency nodes have no published
  Lean record in the DAG at the time of this delivery; no guessed module names
  are imported. They are needed only for proving the theorem in stage 3.

### Searches and source checks

- `msearch.py leanfinder`, query `Filtered colimits of infinity categories
  commute with finite limits and compute mapping spaces`: eight hits, including
  `CategoryTheory.Limits.filtered_colim_preservesFiniteLimits`,
  `colimitLimitToLimitColimitCone_iso`, and `SSet.Finite.instIsFinitelyPresentable`.
  Read the ordinary filtered-colimit source and finite simplicial-set source.
  None is a coherent infinity-category statement.
- `msearch.py loogle`, query `Quasicategory, IsFiltered`: no hits; the service
  reported the unqualified quasicategory identifier unknown.
- `msearch.py grep`, query `filtered|colimit|core` in
  `AlgebraicTopology/Quasicategory`: zero matches returned by the wrapper.
- Direct `rg` in Mathlib, upstream `WeilConjectures`, `dag/lean_names_upstream.json`
  and project `lean/Sheaf` for `cat_infinity_filtered_finite_calculus`,
  `CoreImplementation`, `FiniteLimitAssembly`, the item id, and the related
  finite/filtered quasicategory terminology found no existing statement or name
  conflict. Ordinary category statements and project ordinary filtered-category
  files do not have the same objects or universal properties.
- Published-source lookup found `PresentableInfinityCategory`; the initial
  shared snapshot lacked its record, but the current shared node now records it.
- Read the specified Gepner--Haugseng source online at
  [Section 3.3](https://arxiv.org/html/1312.3178v4#S3.SS3), especially the
  endpoint-fiber argument following Proposition 3.3.2, Corollary 3.3.8 and the
  finite-limit argument in Theorem 3.3.1. The module follows the node's own
  foundational proof plan, rather than claiming those references already
  provide Lean declarations.

### Edge cases and validation

Empty `K` and empty `L` are included; the former keeps the terminal comparison,
and the latter gives the constant terminal functor. Empty categories at stages,
empty mapping spaces, and empty homotopy fibers are not excluded. The small
filtered index cannot be empty because the recorded filteredness tests the
empty shape. Arbitrary nonfaithful transitions and noninjective transitions
remain permitted. Finite higher simplices are treated together at a common
stage, and the equivalence of finite diagrams retains their face relations.
The fixed-base map is retained by the full cone transformation, including the
identity and arbitrary-arrow fiber cases. All universes and variables are
explicit; no local notation, private definition or local instance is used.

All definitions have real data. There are exactly two postponed theorem proofs:
`coconeLeg_endpoints` (the named well-definedness proof used by `coconeLeg`) and
`cat_infinity_filtered_finite_calculus` (the item). Their source and full proof
plans are in their docstrings. `scompile.py` checked the complete module against
the published library with exit zero and no warnings. The required delivery dry
run is the final validation step; the second reader, not this worker, writes
the independent second-reading section and delivers.

## Earlier second reading (a previous round; superseded)

I read the item's original DAG statement and all eleven proof steps, the complete
sandbox module, and the four statement-dependency records and their declarations.
There is no repair note for this item. The source is not Stacks: it is
[Gepner--Haugseng, Section 3.3](https://arxiv.org/html/1312.3178v4#S3.SS3).
I opened Proposition 3.3.2 and its proof, Corollary 3.3.8 and the proof of
Theorem 3.3.1. The cocartesian-arrow assumptions of Proposition 3.3.2 belong to
that proposition's application; they are not hypotheses of the foundational
filtered-colimit calculus extracted here. In particular its proof computes
mapping spaces by the endpoint-fiber construction. Corollary 3.3.8 is stated
for accessible categories with the indicated product-preservation assumption;
the node specializes the resulting base-change fact to Cat infinity, rather
than claiming it for an arbitrary category.

My object/hypothesis/conclusion checklist, in the order of the node, is:

| Node item | Lean rendering and verdict |
| --- | --- |
| Nested universes and small quasicategories | `CoherentNerve.QCats.{u}` consists of all `SSet.{u}` quasicategories, and its coherent nerve has universe `u + 1`. `M.qcat_enrichment` is the enrichment supplied by the recorded marked model. Pass: actual Cat infinity, not the ordinary category or its ordinary nerve. |
| Spaces in the same small universe | The codomain of `CoreImplementation.operation` is the recorded `Spaces.Kan.{u}`. Its nerve is definitionally `Spaces.infinityCategory.{u}`. Pass. |
| Coherent diagrams | Every diagram binder is a simplicial map; the reused `hammockCoherentNerveMap` postcomposes every enriched simplex. Pass: higher homotopies are retained. |
| Small filtered index | `I : SSet.{u + 1}`, `hI : Quasicategory I`, `Presentability.IsSmall.{u, u + 1} I`, and `IsKappaFiltered Cardinal.aleph0 I`. I read the definitions: smallness counts all nondegenerate simplices; filteredness tests every cardinal-small shape, including the empty shape. Pass: no ordinary-category restriction or additional inhabitedness assumption. |
| Finite means finitely many nondegenerate simplices | `K.Finite` and `L.Finite` are Mathlib's `SSet.Finite`; I checked `Finite.lean`, where the field is finiteness of `X.N`. Pass: not degreewise finiteness. |
| Existence of small filtered colimits | First conjunct of `Calculus`, the dependency's `HasSmallKappaFilteredColimits`. It supplies a colimiting enhanced cocone for every such diagram. Pass. |
| Existence of finite limits | `HasFiniteCoherentLimits` quantifies over every finite simplicial set and coherent diagram and supplies a terminal cone. `FiniteLimitAssembly` gives the equivalent functorial universal-cone formulation. Pass, including the empty shape. |
| Canonical comparison for every `K × I` diagram | `FilteredFiniteExact`, together with `FiniteLimitAssembly`: assemble its slices into `limitCones K C`, and a limiting cone on the pointwise colimit gives the cocone there. Evaluated base cocones are colimiting, so its actual apex cocone is colimiting. That states the universal property of the canonical comparison being an equivalence. `totalArrow` retains the cone transformations, so this does not permit a comparison with unrelated legs. Pass. |
| Empty `K` | There is no vertex/nonemptiness premise on `K`; the pointwise premise has no instances, while the apex conclusion remains. Pass: filtered colimits of terminal objects are included. |
| Base change, fixed `B`, arbitrary `T → B` | The cospan specialization of the preceding universal comparison. The two constant entries have identity colimiting cocones because a filtered index is weakly contractible. Their supplied arrows determine the structural map from the colimit. Pass as this instance; no replacement of the structural map by a free map `C → B`. |
| Core preserves small filtered colimits | Existential `CoreImplementation` in `Calculus`, with object equation `(operation.obj C).obj = (Enhanced.core C.obj).toSSet` and a map equation in the full internal Hom. `PreservesSmallFilteredColimits` tests every actual image cocone. Pass: the map equation specifies the enriched operation, not merely its object values. |
| `Fun(L,-)` preserves these colimits for every finite `L` | Universal finite-`L` conjunct with `FunctorImplementation`. Its object equation uses the actual internal Hom, and its enriched map is the transpose of `MonoidalClosed.comp L C.obj D.obj`. Pass, including `L` empty or not a quasicategory. |
| Common-stage representation of finite objects, arrows and specified simplices | `FiniteStageRepresentatives`: for every finite `K` and `f : K → C`, it supplies one `i` and `g : K → D_i`, with `AreNaturallyEquivalent (g ≫ coconeLeg D c i) f`. I checked `AreNaturallyEquivalent` is an equivalence edge in the full internal functor object. Pass: simultaneous coherent representation, not separate representatives of the vertices. |
| Small filtered coherent coslice `I_{i/}` | `coslice I i = Enhanced.comma I I (𝟙 I) i false`, and `FilteredCoslices` asserts its smallness, quasicategory condition and filteredness. I checked the Boolean in `commaSubcomplex`: `false` fixes source `i` and leaves target variable. Pass: arrows out of `i`, with higher triangles. |
| Mapping-space colimit for `x,y ∈ D_i` | Derived endpoint-fiber instance of the same finite universal comparison, core preservation and finite `Fun(Δ[1],-)` preservation, restricted to the actual coslice. See the detailed equivalence check below. Pass as a universal-property presentation. |
| Naturality in objects and pre/postcomposition | The comparisons above are maps of full coherent diagrams. The degree-two composition and the face/degeneracy maps of the arrow diagram are retained, rather than choosing independent objectwise equivalences. Pass. |
| Diagram to fixed `B`, every base arrow `f`, and homotopy fibers | Apply the same cospan comparison to the endpoint comparison over the fixed base mapping space and the specified vertex `f`. The dependency's `Enhanced.homotopyFiber` is the path model, not a strict arbitrary fiber. Pass, with the coherent endpoint identifications explained below. |
| No fully faithful transitions | No such hypothesis occurs in `Calculus`, `FilteredFiniteExact`, the implementation structures or `FiniteStageRepresentatives`. Pass. |

The two mapping-space lines deserve an explicit check because the file does
not introduce a separately chosen mapping-space colimit or comparison map.
Over `J = I_{i/}`, its projection gives the diagram `D_j` with coherent
transported endpoints `D(u)x,D(u)y`. The category of arrows has endpoint
functor to the pair of objects. Applying the actual core gives the space
map `core Fun(Δ[1],D_j) → core D_j × core D_j`. Its homotopy fiber at those
endpoints is the mapping space. Core preserves limits (the maximal subgroupoid
is right adjoint to the inclusion of spaces), and the two normalized operations
in `Calculus` preserve filtered colimits. Therefore the cospan instance of
`FilteredFiniteExact` identifies the colimit of these fibers with the fiber
at the colimit endpoints. `J → I` is cofinal by filteredness, so the latter
endpoints are exactly `r_i x,r_i y` in `C`. The right-pinched/arrow mapping
comparison identifies these fibers with the dependency's `mappingSpace`.
This is a characterization of the canonical map via its cocone, rather than
an assertion about any freely chosen equivalence between the two spaces.

For a coherent map to `B`, the triangles `p_j D(u) ≃ p_i` transport the
endpoints in `B`; strict equality of endpoints is unnecessary. The endpoint
construction is a coherent diagram over the fixed base mapping space.
Taking its homotopy pullback along `{f} → Map_B(p_i x,p_i y)` is a second
finite cospan instance. A constant diagram over filtered `J` has its indicated
constant value as colimit, including the point `{f}`. Consequently the image
cocone on these homotopy fibers is colimiting. In both instances all legs
come from the original coherent diagram and cocone. Naturality under functors
to `B` and under composition follows from those same full simplicial maps.
Thus these clauses are consequences of the universal comparison actually
asserted in Lean, with the specified maps; they are not additional assumptions
or an unnormalized family of existence claims. The source and the node's
steps 9--11 use this very calculation. I retained this equivalent formulation.

Dependency signatures checked directly:

- `Enhanced.coneCategory`, `coconeCategory`, `comma`, `IsLimiting`,
  `IsColimiting`, `mappingSpace`, `homotopyFiber`, `AreNaturallyEquivalent`
  and `IsFunctorEquivalence`, including the comma's two endpoint equations.
- `Presentability.IsSmall`, `IsKappaFiltered`,
  `HasSmallKappaFilteredColimits` and `PreservesColimitsIn`, with independent
  smallness and containing universes. No extra equality of those universes.
- `Marked.CartesianModelStatement.qcat_enrichment`, `qcat_mapping`,
  `qcat_ordinary_maps`, `qcat_composition`, `cat_infinity_quasicategory`
  and `quasicategoryNerve`. The representation parameter `M` introduces no
  extra mathematical assumption: the dependency asserts it exists.
- `Spaces.Kan`, `kanEnrichment`, `infinityCategory` and `mappedCocone`.
  The last operation postcomposes the entire coherent transformation.
- The already-published `CategoryTheory.hammockCoherentNerveMap` is fully
  general in its category object and morphism universes; setting the object
  universe to `u + 1` and the morphism universe to `u` gives exactly the
  constructor the worker had repeated. I read its owning node as well.

Edge cases checked: empty finite shapes and empty finite collections remain
included. Empty categories at intermediate stages, empty cores, empty mapping
spaces and empty fibers are permitted. An empty index is ruled out by
filteredness itself, rather than an extra hypothesis. Identity arrows and
arbitrary nonidentity arrows `f` use the same homotopy-fiber clause. There is
no ring, characteristic, scheme, or integer parameter in this node, so the
usual characteristic, empty-scheme and `n = 0` restrictions do not arise;
zero-dimensional simplicial shapes are included. Universes `u`, `v`, `w`
and every variable are explicitly declared; no implicit binder was introduced.

Independent searches (recorded by `msearch.py` in `searches.jsonl`):

- LeanFinder: `Homotopy coherent nerve functor of enriched functors and
  preservation of filtered homotopy colimits of mapping spaces`. Eight hits,
  including Mathlib `CategoryTheory.SimplicialNerve`; its definition has
  coherent simplex functors but no theorem matching this node.
- LeanSearch: `Filtered colimits of quasicategories commute with finite limits
  and their mapping spaces are filtered homotopy colimits`. Eight ordinary
  category results, including `colimitLimitIso` and
  `filtered_colim_preservesFiniteLimits`; none states this coherent result.
- Loogle: `SimplicialNerve` returned no hits and reported the unqualified name
  unknown; this was not treated as evidence of absence by itself.
- Wrapper grep: `SimplicialNerve|Quasicategory`, plus direct `rg` over the
  named Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf` trees,
  for enriched nerve maps, universal cones, coslices and preservation predicates.
  This found the duplicate nerve-map constructor and the general preservation
  predicate that I reused below. I read their source signatures. The ordinary
  nerve map, join coslices, and the marked-model-specific functor-pushout
  object extraction are not the generic constructors used here.

Mismatches and changes:

1. H4: the worker's `SSet.CatInfinityCalculus.nerveMap` repeated the already
   published `CategoryTheory.hammockCoherentNerveMap`. Removed it, imported
   its owning module, and used the existing declaration at both operations.
   Added its already-landed node `lem-coef-hammock-infinity-localization` to
   `stmt_deps` under the explicit landed-dependency rule; no dependency node
   or dependency module was rewritten.
2. H4: the body of `PreservesSmallFilteredColimits` repeated the generic
   preservation test. It now specializes `Presentability.PreservesColimitsIn`
   to the class of small filtered indexing shapes. Existence of `hI` inside
   that class predicate is equivalent to the former explicit filtered-index
   binders and imposes no new assumption.
3. H8: repaired a LaTeX command split inside `operatorname` in proof step 5,
   preserving the proof text and putting every line within 100 characters.

The worker's earlier statements that only `lean` changed and that its
`nerveMap` was new are superseded by these repairs. The natural-language
statement, source, proof and proof dependencies are unchanged. There are no
new nodes, no dependency modules, and no statement correction or citer audit.
The main theorem signature remains verbatim the node's `lean.statement`.
All definitions have real data; the only two postponed proofs are the named
endpoint well-definedness theorem and the main theorem, with matching source,
blueprint and proof docstrings. No theorem was proved during this reading.

Final `scompile.py` checked the delivered module at both sandbox and library
paths: exit zero, 2.1 s and 2.3 s respectively, with no warnings. The final
source has no overlong line or local notation/instance/private definition.

## Repair H3: explicit conclusion predicates

The returned H3 required the conclusions used by `lem-coef-filtered-operadic-unstraightening` to be present in the statement itself. I therefore added three named conjuncts to `Calculus`, after `FilteredCoslices`:

- `BaseChange` binds fixed vertices `B,T` of the coherent-nerve category, an arrow `p : Δ[1] → Cat∞` with the two endpoint equations, and every finite `K`, small filtered `I`, coherent limiting-cone diagram `F` and supplied cocone `c`. Its premise is the actual `Spaces.mappedCocone` at every `k : K`, and its conclusion is the actual `Spaces.mappedCocone` on `limitApex`; this is the universal-cocone base-change clause with the structural arrow retained.
- `MappingColimits` binds the actual filtered coherent diagram `D`, its supplied colimiting cocone `c`, a stage `i` and objects `x,y`. It supplies a coherent coslice diagram `M : coslice I i → Spaces.infinityCategory` and supplied cocone `m`; `Enhanced.IsColimiting M m` is required, the apex is identified with the mapping space in the colimit using the actual `coconeLeg`, and every coslice vertex is required to carry a mapping-space object of the corresponding stage. Thus the coslice mapping-space colimit is a statement clause, with the actual cocone rather than a bare equivalence.
- `RelativeMappingColimits` contains `MappingColimits` and explicitly binds `q : A → B`, `f : B₀`, the actual homotopy-fibre simplicial set `Enhanced.homotopyFiber q f`, a fibre diagram `H`, its supplied cocone `h`, and a map `e` to the ambient diagram. It states that the image cocone `Spaces.mappedCocone e H h` being colimiting implies the supplied fibre cocone is colimiting. This is the universal-cocone homotopy-fibre clause over the specified arrow.

The theorem signature remains verbatim `@Calculus.{u} M.qcat_enrichment M.qcat_mapping`; the new predicates are conjuncts inside `Calculus`, so no hypothesis or conclusion is silently omitted. The theorem docstring now names all three predicates and records that naturality and the fibre-over-`f` clause are statement clauses. The proof-plan steps 10 and 11 already give the required object, pre/postcomposition, fixed-base functor, and homotopy-fibre constructions, and now correspond directly to these predicates.

## Second reading by Q28

This reading supersedes the earlier reading and the section "Repair H3" above.
I read the item statement and all eleven proof steps, the complete module, and
all four original statement-dependency nodes and their declarations. There is
no repair note for this item. The source is not Stacks: I read
[Gepner--Haugseng §3.3](https://arxiv.org/html/1312.3178v4#S3.SS3), particularly
Proposition 3.3.2 and its endpoint-fiber proof, Corollary 3.3.8, and the proof of
Theorem 3.3.1. The cocartesian-arrow hypotheses in Proposition 3.3.2 concern its
application; they are not hypotheses of this extracted foundational calculus.
The theorem proof uses the node's eleven-step foundational proof, as recorded
in its docstring. No node statement or target statement changed.

### Objects, hypotheses, and conclusions

| Node item | Lean rendering and verdict |
| --- | --- |
| Small infinity categories and spaces in nested universes | `CoherentNerve.QCats.{u}` with `M.qcat_enrichment`, its coherent nerve in `u + 1`, and `Spaces.infinityCategory.{u}`. I read the marked-model normalization of enriched maps and composition and the Kan enrichment. Pass: coherent categories and spaces, not ordinary nerves or homotopy categories. |
| Coherent small filtered index | `I : SSet.{u + 1}`, explicit `hI : Quasicategory I`, `Presentability.IsSmall.{u, u + 1} I`, and `IsKappaFiltered Cardinal.aleph0`. I read these definitions: smallness counts all nondegenerate simplices, and filteredness tests the empty shape. Pass; no fully faithful or injective transition assumption. |
| Finite simplicial shapes | Mathlib `K.Finite` and `L.Finite`, whose field is finiteness of all nondegenerate simplices, not finiteness in each degree. Pass, including shapes which are not quasicategories. |
| Small filtered colimits | First conjunct of `Calculus`, the recorded `HasSmallKappaFilteredColimits` at aleph zero. Pass: actual colimiting enhanced cocones. |
| Finite limits | `HasFiniteCoherentLimits` and `FiniteLimitAssembly`, whose projection forgets universal cones to their diagrams. Pass: every finite diagram, coherently, including the empty diagram. |
| Canonical finite-limit/filtered-colimit comparison | `FilteredFiniteExact`: pointwise colimiting evaluated base cocones imply colimitingness of the actual apex cocone. `totalArrow` retains all cone transformations. `FiniteLimitAssembly` makes this apply to every `K × I` diagram. Pass. |
| Base change along any fixed `T → B` | Repaired `BaseChange = RelativeMappingColimits Cat∞`. Its parameter `p : Δ[1] → Cat∞` is fixed on the bottom edge of the entire square family and of its target square. The other right edge is the given family `D_i → B`, and the square cocone retains its induced structural arrow at the apex. All object squares and the target are pullbacks. The evaluated fourth-corner cocone is colimiting. Pass: the fixed arrow now occurs in equations, rather than as an unused binder. |
| Core preservation | `CoreImplementation` specifies the core object and full enriched restriction map; `PreservesSmallFilteredColimits` tests the actual image of every cocone. Pass. |
| Finite `Fun(L,-)` preservation | `FunctorImplementation` uses the actual internal Hom and normalized closed-category composition on every enriched map. The universal finite-`L` conjunct requires preservation. Pass. |
| Common-stage finite coherent data | `FiniteStageRepresentatives` supplies one stage and one diagram for every finite `K → C`, with a coherent natural equivalence to the original diagram. Pass, including the empty collection. |
| Coherent coslice | `coslice I i = Enhanced.comma I I (𝟙 I) i false`; its vertices are arrows out of `i`. `FilteredCoslices` asserts smallness, quasicategory structure, and filteredness. Pass. |
| Actual mapping diagram and its canonical comparison | New `CosliceMappingColimits`, with normalized `PairImplementation` and `EndpointImplementation`, supplies an entire square diagram on that exact coslice and a supplied square cocone. Its right edge, including the full cocone prism, is exactly the endpoint cylinder applied to `D` and its original cocone. The point section starts at `(x,y)` over the identity coslice vertex and ends at `(r_i x,r_i y)`. Every upper-left corner is the appropriate mapping-space model, identified by `IsMappingSquare` using the actual right-pinch prism in every simplicial degree. The upper-left image cocone is colimiting. Pass: neither the objects nor the comparison can be replaced by an unrelated diagram. |
| Transported endpoints at every later stage | `HasSquareEndpoints` fixes the endpoint pair of each square; the point section is coherent over the coslice and is fixed at its initial identity vertex. Its values are therefore the transports of `(x,y)` along `D(u)`, up to the coherent equivalences in the node. Pass: the existential `xj,yj` are constrained by this whole section, not arbitrary stage vertices. |
| Naturality in objects and pre/postcomposition | The endpoint cylinder is specified on every enriched simplex: `maps₀`, `maps₁`, and `maps₀₁` give the two endpoint functors and their enriched natural transformation, with actual evaluation components. The whole square cocone is specified on its right edge. `IsMappingSquare` uses the natural right-pinch prism, and pullback universal properties determine the comparison. Degree-two faces give composition and every higher face/degeneracy is retained. Pass: these specify the natural comparison rather than independent pointwise equivalences. |
| Diagram to fixed `B` and fiber over every arrow `f` | New `MappingFiberColimits` binds `B`, `b₀,b₁`, and a literal vertex `f` of `Enhanced.mappingSpace B.obj b₀ b₁`. Its point edge is required by `HEq` to be exactly `SSet.const f`. `W : Enhanced.SpaceBaseChange p` is specified by its entire coherent family of pullback squares. For every filtered slice cocone colimiting on its underlying spaces, the actual image fiber cocone is colimiting. A coherent diagram of functors to `B` gives precisely such a slice cocone on the canonical absolute mapping diagram; the slice includes the induced apex map and all triangles. `Calculus` also asserts existence of `W` for every edge, avoiding a vacuous universal assertion. Pass, including identity arrows and empty fibers. |

The square formulation is the universal-property formulation of the displayed
comparisons being equivalences. No colimit object or comparison inverse is
chosen from a postponed mere-existence proof. The canonical coslice section is
fixed at its initial identity vertex; its remaining values and homotopies are
its coherent transports. This is why the construction retains the given lift
when the node is used for cocartesian arrows, rather than choosing new lifts.

### Mismatches and repairs

1. The old `BaseChange` bound `B,T,p` but never used them in its conclusion or
   hypotheses about the finite diagram. It merely repeated finite exactness.
   I replaced it by the fixed-edge square condition above, using the published
   `spaceSquare`, `spaceSquareEdge`, and `IsSpacePullbackSquare` definitions.
2. The old `MappingColimits` supplied an arbitrary coslice diagram with only
   vertexwise existential mapping-space objects. It did not constrain its
   transitions, did not require `xj,yj` to be the transports of `x,y`, and did
   not specify the cocone maps. I replaced that interface by the explicit
   `CosliceMappingColimits` construction. The pair operation is normalized on
   both enriched projections. The endpoint cylinder is normalized on every
   coherent simplex and every enriched mapping object; its components are
   actual endpoint evaluation. The square family and its full right-edge
   cocone are required to be the images of the original `D,c`. The
   right-pinched comparisons are normalized by the published prism formula.
3. The old `RelativeMappingColimits` asserted an unrelated implication for
   arbitrary `J,A,B,q,f,e,H,h`. In particular `e` was an arbitrary map, and no
   filteredness or fixed-base mapping diagram was retained. Restricting `J`
   alone would not repair this. I replaced the implication by actual
   fixed-edge square comparisons and added `MappingFiberColimits` on the
   canonical space slices and canonical `SpaceBaseChange`, with the literal
   base arrow `f` and actual image cocone.
4. A further H4 search found generic internal-Hom vertex decoders already in
   `CoherentDiagramCoyoneda` and `ModuleUniversalArrowCriterion`. I removed
   the new decoder helper and use Mathlib's `unitHomEquiv` and
   `Functor.natTransEquiv` directly; no duplicate decoder was delivered.
5. Added the published proof imports
   `SpacesKappaLimitFilteredColimit`, `InfinityCosliceColimitFormula`, and
   `InfinityCofinalCommaCriterion`; the remaining unstated proof dependencies
   have no recorded modules to import. Updated `lean.declarations` and its
   explanatory note. The main signature remains verbatim `lean.statement`.

The extra declarations are the canonical maps and normalized interfaces of
this item's mapping/fiber construction, allowed by the brief's helper rule.
They are included in this node's `lean.declarations`. There is no independent
new definition node, no dependency-module repair, and no statement correction.
I reused and added to `stmt_deps` the published nodes
`def-coef-space-base-change` and `lem-coef-infinity-pinch-comparison`, opening
both nodes and their complete modules. The former provides the actual square,
slice, universal-property predicate and canonical base-change interface; the
latter provides the right-pinched comparison and its prism. These notions
were not copied into this module. Earlier additions of
`lem-coef-hammock-infinity-localization` and its published coherent-nerve map
remain in place.

### Edge cases, searches, and checks

Empty `K` and `L`, the empty finite data set, and zero-dimensional shapes remain
admitted. `FilteredFiniteExact` retains the empty-shape terminal comparison.
Empty stage categories and empty absolute or relative mapping spaces are not
excluded. Filteredness tests the empty shape, so an empty filtered index is not
silently admitted. Parallel arrows and noninjective/nonfaithful transitions
are permitted. Every identity/base-arrow case is included in
`MappingFiberColimits`. There is no arithmetic characteristic or degree
restriction in this categorical statement. All universes are explicit: small
objects are in `u`, the coherent nerves and indices in `u + 1`, with smallness
measured in `u`; no universe equality was imposed.

Independent searches in this reading used:

- LeanFinder: "Homotopy pullback squares preserve filtered colimiting coherent
  cocones in quasicategories". Eight ordinary Van Kampen/ordinary category
  hits, none a coherent Cat-infinity or mapping-space result.
- Loogle: `"Quasicategory", "pullback"`. Zero hits.
- The grep search service: `mappingSpace|FilteredColimit|core` in
  `AlgebraicTopology/Quasicategory`. Zero hits.
- Direct `rg` over Mathlib, upstream `WeilConjectures`, project `lean/Sheaf`,
  and DAG nodes, by core/maximal subgroupoid, filtered finite comparison,
  mapping-space/endpoint/fiber terminology, and all added declaration names.
  Read the ordinary filtered-colimit and finite-simplicial-set results and
  the published square and pinch declarations. No exact existing calculus,
  endpoint cylinder, or canonical coslice mapping-cocone declaration was
  found. The published square and pinch notions are reused.

Every declaration has a source and blueprint docstring. All data definitions
are concrete projections, compositions, or normalized structures, with no
`sorry` data or existence-based object choice. The only two postponed theorem
proofs remain `coconeLeg_endpoints` and the main theorem; both carry their
source and full proof plan. No theorem was proved in this stage. The module
has no unbound variables, local notation, private definition, local instance,
or line exceeding 100 characters. The prescribed `scompile.py` compiled the
complete repaired module at sandbox and library paths, without errors or
warnings; final delivery preflight is recorded below.

Final validation: `deliver2.py Q28 lem-coef-cat-infinity-filtered-finite-calculus --no-push`
printed `OK (dry run)` for commit `c0e78a4f30`: the repaired module compiles and
the delivery passes the maintainer's server preflight. Nothing was pushed by
that dry run. The prescribed delivery command follows this successful check.
