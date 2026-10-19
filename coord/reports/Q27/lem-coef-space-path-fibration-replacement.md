## Worker report

The module `Sheaf.AlgebraicTopology.PathFibrationReplacement` states
`SSet.Enhanced.path_fibration_replacement`, with its sole proof `sorry`. Its complete
six-step natural-language proof is in the theorem docstring. The only new helper is
`SSet.Enhanced.homotopyFiberToMappingPath`: the canonical map retaining `(x, γ)` and
forgetting the final-endpoint equation. Its data is Mathlib's `Subcomplex.homOfLE`,
using the first projection of the two endpoint equations. It contains no `sorry`.
There are no new independent notions and no new DAG nodes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Small simplicial sets in a fixed arbitrary universe: `{P Q : SSet.{u}}`, with
  explicitly declared `universe u`. All products, subcomplexes and internal homs
  stay in this universe.
- P and Q are spaces, meaning Kan complexes: `[KanComplex P] [KanComplex Q]`.
  There is no inhabitation, connectedness, or dimension-zero horn hypothesis.
- The map is `(f : P ⟶ Q)`.
- The specified object E_f is the existing `mappingPath f`, not a fresh definition.
  `mappingPathSubcomplex f` consists degreewise of `(x, γ)` satisfying
  `evaluation Δ[1] Q 0 γ = f x`; it is the stated degreewise pullback.
- The specified map p is the existing `mappingPathProjection f`, evaluation at 1
  after forgetting the initial-endpoint equation.
- p is a Kan fibration: `Fibration (mappingPathProjection f)`.
  The scoped instance `SSet.modelCategoryQuillen` defines this as `J.rlp`, where
  J consists of `horn (n + 1) i` for every `i : Fin (n + 2)`. Thus it includes
  both outer horns, all positive dimensions, and no zero-dimensional condition.
- The specified inclusion is `mappingPathInclusion f`; its degreewise formula
  is `(x, constantDiagrams Δ[1] Q (f x))`. Its weak-equivalence assertion is
  `IsWeakHomotopyEquivalence (mappingPathInclusion f)`, using the recorded
  realization-based predicate, including the path-component bijection and all
  positive based homotopy-group isomorphisms.
- The factorization identity is
  `mappingPathInclusion f ≫ mappingPathProjection f = f`.
- Every vertex is covered by `∀ q : Q _⦋0⦌`. The strict-fiber clause is
  `IsPullback (homotopyFiberToMappingPath f q)
  (stdSimplex.isTerminalObj₀.from (homotopyFiber f q))
  (mappingPathProjection f) (SSet.const (X := Δ[0]) q)`.
  The upper-left object is exactly the dependency's `homotopyFiber f q`;
  its top arrow retains the original point and path, and its left arrow is
  the unique arrow to Δ[0]. The bottom arrow selects q. The pullback property
  therefore identifies this specified model with the strict fiber canonically,
  retaining its map into E_f; it asserts more than an uncharacterized abstract
  equivalence. Degreewise the extra equation is exactly γ(1) = q.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.evaluation`, `constantDiagrams`, `IsWeakHomotopyEquivalence`,
  `commaSubcomplex`, `comma`, and `homotopyFiber` (recorded main declaration
  `SSet.Enhanced.coneCategory`). I read the full module and its docstrings.
- `Sheaf.AlgebraicTopology.KanFibrationFiberCriterion`:
  `SSet.Enhanced.mappingPathSubcomplex`, `mappingPath`, `mappingPathProjection`,
  `mappingPathInclusion`. This node is already landed and its recorded main
  declaration is `SSet.Enhanced.kan_fibration_fiber_criterion`. Its theorem does
  not state the factorization identity or canonical strict-fiber square, so it
  is not an exact existing match for this item. Its constructions are used
  directly. Its id was added to `stmt_deps` under the explicit permission to
  cite a newly discovered landed node; no field of that dependency changed.
  `scompile.py --source Sheaf.AlgebraicTopology.KanFibrationFiberCriterion`
  confirmed the current published interface.
- The proof-only Mathlib leaf `lem-cbc-internal-hom-fibration-corner-map` records
  `SSet.fibration_pullbackObjObjπ` in
  `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct`.
  Its full signature and proof were read: Mono i and Fibration p imply that
  the internal-hom corner map is a fibration; it is imported without `public`.
- `lem-cbc-realization-weak-equivalence` has no recorded Lean declaration or
  Mathlib match. It is a proof-only prerequisite, so there is no module to
  import yet. Its precise Kan-target component-testing statement is retained
  in the proof docstring; no replacement assertion is introduced here.
- Mathlib's `CategoryWithFibrations.lean` was read for the exact horn convention;
  `Subcomplex.homOfLE` supplies the helper's actual data and `IsPullback` supplies
  the ordinary strict-fiber universal property.

Edge cases checked before the revision: empty P gives empty E_f and empty fibers;
empty Q forces P and E_f empty, and the vertex clause is vacuous. A vertex in a
component missed by f gives an empty homotopy fiber, which this theorem permits.
A vertex merely missing the strict image of f can still have paths from f(P),
which the homotopy-fiber model retains. For f = id, the object is the ordinary
path object, not identified with P by equality. Constant maps impose only the
initial-endpoint constraint. The n = 1 horns include both endpoints, and all
higher outer horns remain included. No extra assumptions are introduced.

Searches performed (also checked the previous attempt's search evidence):

- `msearch.py ... leanfinder` with query "Mapping path space of a map of Kan
  complexes gives a Kan fibration replacement with constant path weak equivalence":
  eight results, including `HomotopicalAlgebra.PathObject.trans`,
  `PathObject.toPrepathObject`, and `SSet.Path.map`; no exact statement. The
  abstract path-object interface assumes the weak-equivalence/fibration data
  it packages; `SSet.Path` is a finite string of edges, not the exponential.
- `msearch.py ... leansearch` with query "Mapping path space fibration
  replacement of a map of Kan complexes": eight results about abstract model
  category replacements and edge paths, no exact statement.
- `msearch.py ... loogle` query `SSet.Path`: twelve results on finite edge paths.
  Valid query `SSet.fibration_pullbackObjObjπ`: one result, the exact corner-map
  leaf already recorded in the DAG and used as a proof-only import.
- `msearch.py ... grep` query `PathObject|homotopyFiber|pathSpace` in
  `AlgebraicTopology`: abstract path-object files, no exact item statement.
- `rg -n 'pathSpace|constantPath|homotopyFiber|lem-coef-space-path-fibration-replacement'`
  over `WeilConjectures` and project `lean/Sheaf`: no upstream item; project
  matches include the enhanced homotopy-fiber definition and the landed
  `KanFibrationFiberCriterion`, whose construction is reused. The exact-id
  `grep -rn` in upstream `WeilConjectures` has no match. Additional `rg` for
  `homotopyFiberToMappingPath|path_fibration_replacement` found no collision.
- Read Kerodon https://kerodon.net/tag/0101 and https://kerodon.net/tag/0328:
  the endpoint orientation, constant inclusion and strict-fiber interpretation
  agree with the node. No source statement correction is needed.

The previous attempt duplicated the already landed mapping-path construction,
postponed a compatibility helper without its own matching DAG statement, and
asserted literal equality between differently constructed pullback models.
This revision removes those declarations and the unsupported equality. The
canonical `IsPullback` clause expresses the unchanged natural-language statement.
The previous self-authored second-reading section was removed: the dispatcher
supplies the independent second reader after READY.

Validation: the revised module compiled cleanly through `scompile.py`, including
its actual library module path. Only the main theorem has `sorry`; all helper
data is fully supplied. The required `deliver2.py --no-push` dry run is the final
validation step. No `STATEMENT-DISPUTED` issue or node correction is outstanding.


## Second reading by Q27

Independent second reading on 2026-10-17. I read the current node, the sandbox
module, both statement-dependency nodes and the declarations they record, and
both proof-dependency nodes. I opened the source online: Kerodon Example
the project server, https://kerodon.net/tag/0101, and Remark the project server,
https://kerodon.net/tag/0328. These are the actual sources of this item, not
Stacks .tex. Example 0101 assumes precisely a map of Kan complexes and attaches
the path at vertex 0; its projection evaluates at vertex 1. No additional ambient
connectedness, inhabitation, finiteness or characteristic assumptions occur.
There is no repair note for this item and no statement_change in the node.

My object/hypothesis/conclusion checklist, matched independently with the Lean:

1. The objects are small simplicial sets P and Q in the fixed universe of the
   enhanced-diagrams dependency. Lean: `{P Q : SSet.{u}}`, with `universe u`.
   Verdict: exact; the universe is arbitrary, not a fixed small numerical level.
2. Both objects are spaces, hence Kan complexes. Lean: `[KanComplex P]`
   and `[KanComplex Q]`. Verdict: exact. The KanComplex and horn conventions
   agree with the dependency, including outer horns and empty complexes.
3. The sole map is f from P to Q. Lean: `(f : P ⟶ Q)`.
   Verdict: exact; no injectivity, surjectivity or fibration of f is assumed.
4. The specified E_f consists in every degree of x in P and a whole internal-hom
   path gamma in Q whose initial endpoint is f(x). Lean: `mappingPath f`, from
   the landed `Sheaf.AlgebraicTopology.KanFibrationFiberCriterion` module.
   I read `mappingPathSubcomplex`: its equation uses evaluation at
   `stdSimplex.obj₀Equiv.symm 0`, not vertex 1; its operators act on both
   coordinates. `mappingPath` is that subcomplex's `toSSet`. Verdict: exact
   degreewise pullback, retaining higher simplices, with no private copy here.
5. The map p evaluates the final path endpoint. Lean:
   `mappingPathProjection f`. Its actual definition is the subcomplex inclusion,
   second projection and evaluation at `stdSimplex.obj₀Equiv.symm 1`.
   Verdict: exact orientation and specified map, not an arbitrary projection.
6. The conclusion that p is a Kan fibration is
   `Fibration (mappingPathProjection f)`. I read Mathlib's
   `CategoryWithFibrations.lean`: under `SSet.modelCategoryQuillen`, this means
   `J.rlp`, where J ranges over every `horn (n + 1) i` with
   `i : Fin (n + 2)`. Verdict: all positive dimensions, both outer horns;
   no unwanted zero-dimensional lifting or nonemptiness requirement.
7. The inclusion by constant paths is `mappingPathInclusion f`. I opened its
   definition: it sends a to `(a, constantDiagrams Δ[1] Q (f a))`, with genuine
   proofs of the endpoint equation and naturality. Its conclusion is
   `IsWeakHomotopyEquivalence (mappingPathInclusion f)`. I read that predicate
   in `EnhancedDiagramsCones.lean`: it is bijectivity on realized path components
   and on all positive based homotopy groups, at every source basepoint.
   Verdict: the specified inclusion and exactly the specified weak equivalence.
8. The factorization equation p composed with i equals f is
   `mappingPathInclusion f ≫ mappingPathProjection f = f`.
   Verdict: exact; Lean's composition order gives the node's p circ i.
9. Every vertex, with no nonemptiness assumption on Q, is quantified by
   `∀ q : Q _⦋0⦌`. The model of its homotopy fiber is the recorded
   `homotopyFiber f q`, not a newly chosen space. I unfolded its definitions
   `comma` and `commaSubcomplex ... true`: both endpoint equations are imposed,
   initial endpoint f(x) and final endpoint the constant simplex at q.
   Verdict: same object as the dependency's displayed homotopy fiber.
10. Its canonical identification with the strict fiber is the final
    `IsPullback` clause. I read Mathlib's argument order: the top arrow is
    `homotopyFiberToMappingPath f q`, the left arrow is the unique map to
    Δ[0], the right arrow is p, and the bottom arrow is `SSet.const q`.
    The helper is `Subcomplex.homOfLE (fun _ _ hz ↦ hz.1)`, hence retains x
    and the entire path, forgetting only the final-endpoint proof. Degreewise
    its pullback condition is exactly gamma(1) = q. Verdict: the canonical
    strict-fiber identification, including its map into E_f, rather than an
    unrelated equivalence or false equality of chosen limit objects.

Dependency and definition audit: the two published dependency modules give
usable exact interfaces for the notions this statement needs. The added
stmt_dep `lem-cbc-kan-fibration-fiber-criterion` is already landed and owns the
mapping-path construction, so its direct use is authorized. No dependency
repair or new definition node is needed. The only newly declared helper is a
map between these already defined subcomplexes; it has real data from
`Subcomplex.homOfLE`, contains no sorry and asserts no postponed theorem.
Its declaration is recorded in lean.declarations. No hollow definition occurs.

Edge cases: empty P makes E_f and each fiber empty; these are Kan and the
empty-to-empty inclusion satisfies the weak-equivalence convention. Empty Q
forces P and E_f empty, and the vertex clause is vacuous. A vertex in a missed
component has empty homotopy fiber, which the statement permits. A vertex
outside the set-theoretic image of f can still have paths from that image;
the model retains them. Identity and constant maps use the same formulas,
without asserting E_f = P. At simplicial degree zero paths are actual edges;
the fibration test starts at dimension one and includes both endpoint horns.
No index set, ring, characteristic, scheme or extra universe occurs. There
are no free implicit variables or independent universe restrictions.

My searches, separate from the first worker's, used different wording:

- LeanFinder via msearch.py: "The inclusion by constant paths into the mapping
  cocylinder is a weak equivalence and endpoint evaluation has fibers equal to
  the homotopy fibers". Eight hits: abstract Cylinder and PathObject results,
  with no construction of this exponential pullback or its strict-fiber square.
- LeanSearch via msearch.py: "Every map between Kan simplicial sets factors
  through its exponential interval pullback with a constant section and a
  fibration whose ordinary fibers are homotopy fibers". Eight hits, including
  FibrantBrownFactorization.mk', PathObject.instFibrationP₁ and the horn-lifting
  instance. None gives this assertion. Abstract factorization interfaces assume
  a chosen factorization, not this specified degreewise path construction.
- Loogle via msearch.py: `SSet.fibration_pullbackObjObjπ`. One hit, exactly the
  recorded proof-only corner-map leaf; I read its complete signature and proof
  in PushoutProduct.lean:70-93. Its mono/fibration hypotheses specialize as
  described in proof step 2, but it is not this item's full statement.
- Direct rg, case-insensitive, for `mapping.?cocylinder|mapping.?path|path.?replacement|
  homotopyfiber|homotopy.fib(er|re)|constant.*path` over all upstream
  WeilConjectures, Mathlib/AlgebraicTopology and project lean/Sheaf. I opened
  the relevant project hits: KanFibrationFiberCriterion, KanPullbackPathComparison,
  EnhancedFunctorConeCalculus and SpacesHomotopyFiberDetection. The latter two
  provide maps to the ambient path product or its separate coordinates, not
  this map into mappingPath. The path-pullback comparison has another domain
  and conclusion. The recorded kan_fibration_fiber_criterion signature gives
  the fibration and weak-equivalence clauses but neither the factorization
  equation nor the canonical strict-fiber square. Therefore it cannot serve
  as an existing:true exact match. I also read Mathlib's PrepathObject and
  PathObject interface: its abstract weak-equivalence data is an input, not
  the required realization-based replacement theorem. No duplicate is added.

Docstrings and validation: the helper and theorem carry the source and blueprint
id; the theorem's docstring follows all six proof steps, including the min
contraction, Kan-target test and degreewise fiber argument. The source-based
statement needs no correction. The sole theorem proof is sorry; no theorem was
proved. The imports include the two statement interfaces and the available
corner-map proof leaf; the realization-testing proof node has no recorded
module to import. All lines in the Lean module fit 100 columns. The node's
lean.statement is verbatim the theorem signature before `:= by`.

Mismatches found in this second reading: none in the current Lean, node or
helper. I preserved all correct declarations and changed only this report by
adding the independent second reading and search evidence. The required
scompile.py wrapper compiled both the sandbox view and actual library module
cleanly. The final deliver2.py dry run and delivery follow this audit.
