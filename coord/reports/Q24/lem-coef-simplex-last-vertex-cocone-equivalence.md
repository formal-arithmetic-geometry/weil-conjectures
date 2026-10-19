## Worker report

Item: `lem-coef-simplex-last-vertex-cocone-equivalence`, Q24 stage 2, 2026-10-17 UTC.

The module `Sheaf.CategoryTheory.SimplexLastVertexCoconeEquivalence` states
`SSet.Enhanced.simplex_last_vertex_cocone_equivalence`. Its only theorem proof is
`sorry`; there are no new definitions, axioms, helper theorems, or dependency repairs.
The docstring gives all nine steps of the node's proof, including the operator
check for the decomposition retraction, the image-factorization retraction, and
the nondegenerate terminal factorization.

The node's mathematical statement is unchanged. Its `stmt_deps` gains the already
landed node `lem-coef-simplex-category-last-vertex`, because that node already owns
the exact simplex category and last-vertex construction required here. This is the
permitted addition of a landed declaration dependency, not a new definition node.
Only `lean` and this added `stmt_deps` entry change in the item copy.

Clause-by-clause correspondence:

- Small simplicial sets and universe enlargement: `(X E : SSet.{u})`, with explicit
  arbitrary `universe u`, uses the dependency's existing common-universe internal
  hom and realization convention. One may choose this common universe large
  enough for both objects; no fixed universe or cardinal bound is imposed.
- All simplices, including degenerate ones: `simplexCategory X` is the existing
  abbreviation `X.Elementsᵒᵖ`. Its objects are a degree and a simplex; no
  nondegeneracy predicate occurs. By Yoneda these are exactly maps `Δ[n] ⟶ X`.
- The arrows and their composition: in the opposite category of elements, an
  arrow from `([n],σ)` to `([m],τ)` is an ordinal map `[n] ⟶ [m]` with
  `X(α)(τ) = σ`. Composition is the existing category-of-elements composition,
  hence composition of these monotone maps.
- The nerve and specified last-vertex formula: `nerve (simplexCategory X)` and
  `simplexCategoryLastVertex X` use the published construction. In that module,
  `simplexCategoryLastVertexOrderFun F i` is the tail-composite image of the last
  vertex of the simplex at `i`; `simplexCategoryLastVertexApp` applies the terminal
  simplex to precisely that ordinal map. This agrees with the node in every
  degree, including repeated vertices and chains omitting their final object
  under a face operator.
- Every quasicategory: `[Quasicategory E]` is the only structural hypothesis.
  There is no `Quasicategory X`, Kan condition on `X`, or colimit hypothesis.
- Every diagram and fixed apex: `(p : X ⟶ E) (T : E _⦋0⦌)` are unrestricted.
- Functor simplicial sets: `((ihom X).obj E)` and
  `((ihom (nerve (simplexCategory X))).obj E)` are Mathlib's existing internal homs,
  whose simplices are the coherent transformations specified by the dependency.
- Source diagram: `diagramVertex p`. Source constant diagram:
  `((constantDiagrams X E).app _ T)`.
- Restricted diagram: `diagramVertex (simplexCategoryLastVertex X ≫ p)`.
  Restricted constant diagram:
  `((constantDiagrams (nerve (simplexCategory X)) E).app _ T)`.
- The two right-pinched mapping complexes: the two explicit `mappingSpace`
  expressions in the first and second conjuncts use exactly these endpoints.
  Their `KanComplex` conjuncts render the phrase "of Kan complexes" explicitly.
- Restriction itself: `mappingSpaceMap
  ((MonoidalClosed.pre (simplexCategoryLastVertex X)).app E)
  (diagramVertex p) ((constantDiagrams X E).app _ T)` applies internal-hom
  precomposition to each transformation simplex. Its endpoint images are the
  restricted diagram and the same constant apex: precomposition sends `p` to
  `ℓ_X ≫ p`, and a constant simplex remains constant in every degree.
  No inverse, chosen equivalence, or arbitrary comparison map is substituted.
- Equivalence: `IsWeakHomotopyEquivalence` of that precise map uses the dependency's
  realization definition: bijection on path components and every positive based
  homotopy group. This is equivalence of the displayed Kan complexes.
- Empty `X`: no inhabitance premise is present, so the same theorem applies.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.diagramVertex`, `constantDiagrams`, `mappingSpace`,
  `mappingSpaceMap`, `IsWeakHomotopyEquivalence`. The full module and its
  docstrings were read, including the explicit right-pinched operators and the
  realization-based component/homotopy-group convention. Mathlib primitives
  `SSet`, `SSet.Quasicategory`, `SSet.KanComplex`, `CategoryTheory.nerve`, `ihom`,
  and `CategoryTheory.MonoidalClosed.pre` are reused.
- `Sheaf.AlgebraicTopology.CategoryOfSimplicesLastVertex`:
  `SSet.simplexCategory`, `simplexCategoryLastVertexOrderFun`,
  `simplexCategoryLastVertexOrder`, `simplexCategoryLastVertexApp`, and
  `simplexCategoryLastVertex`. The full module was read. Its weak-homotopy-
  equivalence theorem alone is not confused with the present cocone theorem.
- Already stated proof dependencies are imported non-publicly:
  `Sheaf.CategoryTheory.DecompositionLocalColimitCocones`,
  `Sheaf.AlgebraicTopology.AnodyneCocones`,
  `Sheaf.CategoryTheory.FinalIndexColimit`, and
  `Sheaf.CategoryTheory.NerveNaturalHomotopyEquivalence`.
  `Mathlib.AlgebraicTopology.SimplicialSet.Degenerate` supplies the recorded
  nondegenerate-decomposition Mathlib match. The simplex-lift right-anodyne
  criterion has no recorded Lean module in the inspected DAG, so there is no
  proof-only import for it; no declaration of that criterion is needed to type
  this theorem, whose proof remains `sorry`.

Edge cases checked before writing:

- For empty `X`, the category of simplices is empty. Each functor simplicial set
  from that empty shape has exactly one simplex in each degree, so the fixed-apex
  mapping complexes are points and the restriction is their identity.
- For `X = Δ[0]`, every degenerate simplex is retained. The last-vertex map is the
  unique map to `Δ[0]`; replacing the full simplex category by its nondegenerate
  part would be a different construction, and is not done.
- For an arbitrary simplicial set which is not a quasicategory, the binders and
  all constructions still typecheck; the only horn-filling instance is on `E`.
- For empty `E`, there is no apex `T`, exactly as in the quantified statement.
  Nonempty `E` need not have any colimits.
- Empty spaces of cocones are allowed by `KanComplex` and the component-bijection
  convention of `IsWeakHomotopyEquivalence`; no inhabitedness is inserted.
- Identity arrows and degenerate nerve chains are included in the existing
  last-vertex formula. Its naturality theorem covers arbitrary monotone maps,
  including deleting the terminal object of a chain.

Searches made for an existing statement (no exact match):

- `msearch.py ... leanfinder` query:
  "The last vertex map from the nerve of the category of simplices induces weak
  equivalences on cocone mapping spaces". Eight hits: nerve coskeletality,
  nerve-map/functor and homotopy-category formulas, and `SSet.stdSimplex.isoNerve`.
  None is a cocone mapping-space equivalence.
- `msearch.py ... leansearch` query:
  "last vertex simplex category cocone mapping spaces equivalence". Eight hits,
  including ordinary `Functor.Final.coconesEquiv` and ordinary colimit
  equivalences; none covers arbitrary simplicial shapes and quasicategories.
- `msearch.py ... loogle` query `CategoryTheory.nerve, SSet.Simplices` returned
  zero hits and reported unknown identifier `SSet.Simplices`. Reran with
  `CategoryTheory.nerve`: twelve nerve and nerve-map declarations, none the
  required theorem.
- `msearch.py ... grep` query
  `lastVertex|last.vertex|categoryOfSimplices|CategoryOfSimplices` in
  `AlgebraicTopology` returned zero Mathlib hits.
- `rg` for `lastVertex|last.vertex|coconeRestriction|cocone.*[Rr]estrict|simplexCategory`
  in the upstream `WeilConjectures` tree and the side `lean/Sheaf` tree found the
  existing side `CategoryOfSimplicesLastVertex` construction and distinct
  subdivision/Ex and anodyne/local-decomposition cocone theorems. No upstream or
  side theorem states the present last-vertex cocone equivalence.
- The required `grep -rn` of the item id in upstream `WeilConjectures` returned
  no match. `tools/lean_names_upstream.py show` summarized the upstream indexes;
  direct `rg` of `dag/lean_names_upstream.json` for the item id and
  `simplex_last_vertex_cocone_equivalence|simplexCategoryLastVertex` returned no match.
- Read the recorded existing last-vertex node and its Lean record after the side
  search found it; reused it rather than making another definition.

Source checked directly: [Lurie, Higher Topos Theory](https://people.math.harvard.edu/~lurie/papers/HTT.pdf),
printed pp. 254--255 (PDF pages 271--272, zero based), Lemma the project server and
Proposition the project server, and printed p. 226 (PDF page 243), Proposition the project server.
The latter identifies cofinal restriction on each fixed-apex fiber; the
shape-natural join/cocone convention in the existing project interfaces gives
exactly the mapping-space formulation here. The existing node's proof gives the
same actual restriction as the composite of the two decomposition restrictions.
WANTED: an archival copy of HTT in `literature/`; the primary online PDF was
successfully opened and the cited construction and proof were read.

No statement dispute or node fault was found. No correction, new node, or
replacement of a dependency interface was necessary.

Validation: the prescribed `scompile.py Q24
lem-coef-simplex-last-vertex-cocone-equivalence <module>` completed successfully,
including its private overlay for the existing last-vertex module and compilation
of both sandbox and library-path forms. No errors or non-sorry warnings were
reported. `autoImplicit false` is set and every universe and variable is bound.
The required `deliver2.py ... --no-push` checks the complete packet before the
worker answers READY. The independent second-reading section is intentionally
left to the second reader.

## Second reading by Q24

I reread the node statement, its source place, the dependency records, and
`Sheaf/CategoryTheory/SimplexLastVertexCoconeEquivalence.lean` clause by clause.

- **Objects and universe:** The node's small simplicial sets and enlarged common
  universe are rendered by `(X E : SSet.{u})` with arbitrary universe `u`; the
  same `u` is used by the existing internal-hom and mapping-space interfaces.
  Verdict: exact common-universe encoding, with no cardinal restriction.
- **Simplex category:** The node's `\mathsf S(X)` of all simplices, including
  degeneracies, is `simplexCategory X`, the recorded `X.Elementsᵒᵖ` abbreviation.
  Verdict: exact object and arrow notion; no nondegeneracy restriction.
- **Arrows and composition:** The opposite category of elements supplies arrows
  with the monotone ordinal map and equation `X(α)(τ) = σ`; its category
  composition is the required composition of monotone maps. Verdict: exact.
- **Nerve and last vertex:** `nerve (simplexCategory X)` and the recorded
  `simplexCategoryLastVertex X` supply the chain nerve and the tail-composite
  image of each simplex's last vertex. Verdict: exact formula, including
  repeated vertices, identity arrows, and operators omitting the terminal
  chain object.
- **Target hypothesis:** `[Quasicategory E]` is the only structural hypothesis.
  Verdict: no hypothesis on `X`, no Kan condition on `X`, and no colimit
  existence assumption on `E`.
- **Diagram and apex:** `(p : X ⟶ E)` and `(T : E _⦋0⦌)` are unrestricted, as
  required. Verdict: exact quantifiers.
- **First mapping space:** `mappingSpace ((ihom X).obj E) (diagramVertex p)
  ((constantDiagrams X E).app _ T)` renders the fixed-apex cocone space
  `Map_Fun(X,E)(p, Δ_X T)`, and its `KanComplex` conjunct is explicit. Verdict:
  exact endpoints and Kan clause.
- **Second mapping space:** The second conjunct uses
  `mappingSpace ((ihom (nerve (simplexCategory X))).obj E)
  (diagramVertex (simplexCategoryLastVertex X ≫ p))
  ((constantDiagrams (nerve (simplexCategory X)) E).app _ T)`. Verdict:
  exact restricted diagram, same apex, and Kan clause.
- **Restriction and equivalence:** The final conjunct is the actual
  `mappingSpaceMap ((MonoidalClosed.pre (simplexCategoryLastVertex X)).app E)`
  on those endpoints, with `IsWeakHomotopyEquivalence`. Verdict: exact
  precomposition map and conclusion; no inverse or arbitrary comparison map.

The source was checked directly in Lurie's *Higher Topos Theory*, Proposition
the project server and Lemma the project server (printed pp. 254--255), with the fixed-apex
cofinal restriction interpretation from Proposition the project server (printed p. 226).
The source gives all simplices, allows arbitrary `X`, supplies the stated
last-vertex formula, and imposes no colimit-existence hypothesis on `E`; these
all agree with the node and Lean.

Edge cases checked independently: `X = ∅` has an empty simplex category and the
restriction is the identity on the resulting point mapping spaces; `X = Δ[0]`
retains all degenerate simplices and has the unique last-vertex map; `n = 0`
and identity/repeated-vertex arrows are included by the existing ordinal formula;
degenerate simplices are not removed; arbitrary characteristic is irrelevant;
empty mapping spaces are permitted by the weak-equivalence convention; and an
empty `E` contributes no apex `T`, exactly as the node's quantification states.
No inhabitance, Kan, or colimit assumption was added.

Independent searches found no existing statement or duplicate definition. The
prescribed `msearch.py` LeanFinder query for “last vertex simplex category cocone
mapping spaces equivalence” returned only standard-simplex and ordinal-last
lemmas; the LeanSearch query returned only ordinary nerve and standard-simplex
results; and the Loogle `CategoryTheory.nerve, SSet` query returned nerve
primitives but no cocone equivalence. `rg` over the upstream `WeilConjectures`
and repository `lean/Sheaf` trees found no theorem with this statement. The
recorded `lem-coef-simplex-category-last-vertex` declaration was read and reused;
its `simplexCategory` and `simplexCategoryLastVertex` are the exact dependency
notions, so no dependency repair or new node is needed.

No mismatch was found and no source, node, or Lean statement was changed. The
only delivery content remains the worker's statement module, whose proof is
`sorry` as required for stage 2. The module compiles with `autoImplicit false`,
and all variables and universes are explicit.
