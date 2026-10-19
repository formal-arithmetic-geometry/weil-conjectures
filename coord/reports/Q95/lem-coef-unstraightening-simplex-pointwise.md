## Worker report

The delivery states `SSet.ConePresheaf.unstraightening_simplex_pointwise` in
`Sheaf.AlgebraicTopology.UnstraighteningSimplexPointwise`. The natural statement,
its dependencies, and its seven-step proof are unchanged. Q75's earlier PASS was
stage-1 split review, not a stage-2 statement delivery: the base item has no `lean`
record. The preserved Q95 sandbox contained only brief markers. This delivery
therefore supplies the actual statement rather than changing an accepted proof.

Source checked directly: Lurie, Higher Topos Theory,
https://people.math.harvard.edu/~lurie/papers/HTT.pdf, printed pp. 74 and 76–77
(PDF pages 91, 93–94): Proposition the project server; the preservation assertion of
Theorem the project server; the definition of Q and its largest-element projection preceding
Proposition the project server; Proposition the project server; Remark the project server. No source correction,
statement dispute, or new independent notion is needed.

Clause-by-clause correspondence:

- Small simplicial sets are Mathlib `SSet.{u}`, for an arbitrary explicitly bound
  universe `u`. `Enhanced.IsWeakHomotopyEquivalence` is the recorded realization,
  path-component and positive based-homotopy-group convention. No model structure
  on a slice is assumed.
- The presheaf category and adjoints are exactly `ConePresheaf.Presheaf`, `left`,
  `rightObj`, `rightSet`, and `rightProjection` from the recorded adjunction module.
  Their arrows are full enriched transformations, including positive-dimensional
  mapping simplices. None of them is replaced by ordinary natural transformations.
- For every arbitrary `S`, `n`, `i : Fin (n+1)` with `0 < i.val`, and every
  `σ : Δ[n] ⟶ S`, the first conjunct asserts `weakEquivalences S` of `left S`
  applied to `Over.homMk (horn n i).ι rfl`. The Fin bound is exactly `i ≤ n`.
  Together with positivity it implies `n ≥ 1`, so no case is lost by not repeating
  this redundant inequality. `weakEquivalences` means every component is a weak
  homotopy equivalence. In particular the outer right horn `i=n` is included.
- `restrict u F` has objects `F(C[u](c))` and its full mapping-simplex action is
  `C[u].map` followed by `F.functor.map`. It is precisely
  `F ∘ C[u]^op`. The named `restriction_laws` and
  `restrictHom_naturality` postpone only the identity/composition and action
  compatibility proofs required to package those actual maps. Their proof
  docstrings explain the equations; their names are in `lean.declarations`.
- The second conjunct existentially provides one coherent family `β` of slice
  isomorphisms `rightObj (restrict u F) ≅ (Over.pullback u).obj (rightObj F)`.
  Inverting gives the displayed orientation of the natural statement. This is an
  isomorphism over T, not just an isomorphism of total simplicial sets.
- `baseChangeProjection` composes its forward map with the existing pullback's
  first projection. Equality for identities and composition is expressed using
  `HEq` solely because restriction by identity/composition has propositionally
  equal endpoints through `rigidification.map_id/map_comp`. The equations compare
  actual simplicial maps, so all degrees and operators are included. This is the
  usual identity/composite coherence of pullback isomorphisms: the other pullback
  coordinate is fixed by the slice morphism.
- Naturality in every enriched map `f : F ⟶ G` is the equation between
  `rightSetMap (restrictHom u f)` followed by the projection and projection
  followed by `rightSetMap f`. `restrictHom` retains f's original components.
- The family is fixed by the simplexwise cone formula: for every simplex `σ` of T
  and every enriched label `a`, its image is labelled by `σ ≫ u` and `b`, with
  `Straightening.valueMap` followed by b equal to a at every old vertex. This is
  precisely restriction along the canonical enriched cone-pushout map; it is not
  an unconstrained choice of a base-change map. `HEq` here accounts only for
  C[u] of the vertex versus the vertex of u(s), which are canonically equal.
  Every object of the coherent realization comes from an old vertex: its object
  set is the colimit of the simplex vertices with the face/degeneracy relations.
- The third conjunct gives isomorphisms
  `Enhanced.fiber (rightProjection F) s ≅ singQ (obj F (Straightening.vertex s))`.
  `Enhanced.fiber` is the existing strict pullback over the point, with the point
  factor first; pullback symmetry gives the written order in the node. Its
  naturality equation uses existing `Enhanced.fiberMap ((right S).map f) s` and
  `UnmarkedStraightening.singQMap (component f (Straightening.vertex s))`.
  This quantifies all presheaves and their maps, without a Kan assumption.
- `UnmarkedStraightening.singQ K` is reused verbatim: its m-simplices are
  `PinchedCube.qFunctor.obj m ⟶ K`, exactly `Q^m ⟶ K`, and its operator is
  precomposition with `qFunctor.map`. `singQMap` is postcomposition.
- `pinchedProjection` selects the projection already asserted by
  `PinchedCube.pinched_cube_latching`. Its normalization is
  `quotientMap n ≫ π.app ⦋n⦌ = maximumMap n`. The quotient map is surjective in
  every degree by its explicit `Quotient.mk` construction; this equation uniquely
  determines every component and hence π. Thus the definition selects data
  determined up to equality, as authorized by AGENTS §5, rather than a map from
  an undetermined existence statement. All four universe arguments of the
  dependency theorem are explicitly instantiated at u; this does not add any
  assumption on the input simplicial sets.
- `singularComparison K` has component `z ↦ π.app m ≫ yonedaEquiv.symm z`,
  exactly precomposition by `Q^m → Δ^m`. Its simplicial naturality is supplied by
  naturality of π and Mathlib's Yoneda equivalence. There is no arbitrary
  equivalence in place of the required comparison.
- The fourth conjunct assumes exactly `KanComplex K` and concludes both
  `KanComplex (singQ K)` and `IsWeakHomotopyEquivalence (singularComparison K)`.
- The last conjunct quantifies all maps `h : K ⟶ K'` between Kan complexes and
  gives the equality `h ≫ singularComparison K' = singularComparison K ≫ singQMap h`.
  Together with the preceding fiber-naturality equation, this is naturality of
  all the fiber comparisons requested in the final sentence.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, the ordinary realization convention;
  the recorded `coneCategory` signature and docstring were also read.
- `Sheaf.AlgebraicTopology.ConePresheafAdjunction`:
  `Presheaf`, `obj`, `action`, `component`, `homMk`, `left`, `right`, `rightObj`,
  `rightSet`, `rightSetMap`, `rightProjection`, `weakEquivalences`, and the full
  `cone_presheaf_adjunction` signature and proof docstring.
- `Sheaf.AlgebraicTopology.PinchedCubeLatching`:
  `rigidification`, `qFunctor`, `Q`, `quotientMap`, `maximumMap`, and the full
  `pinched_cube_latching` signature and proof docstring.
- Construction-only reuse: `Sheaf.AlgebraicTopology.RightStraighteningFiberComparison`
  provides `Straightening.vertex` and the canonical `Straightening.valueMap`.
  These are already public dependencies of the cone-presheaf module.
- Construction-only reuse: `Sheaf.AlgebraicTopology.UnmarkedStraighteningQuillen`
  provides `singQ` and `singQMap`. Its downstream theorem is never invoked.
  Its DAG node is deliberately not added as a prerequisite: that theorem depends
  through the contravariant slice model and homotopy descent on the present item.
  Using only the explicit definitions avoids that circular mathematical dependency.
  These definitions belong to the singular notion already described in the item's
  own statement, so no new definition node is introduced. If later proof-import
  propagation would create an import cycle through these construction-only modules,
  that proof import must be omitted under stages/2-statements.md §3(7).
- `Enhanced.fiber` and `Enhanced.fiberMap` are reused from the existing infinity
  fibrations/contravariant slice modules, already exposed by the imports.
- Stated proof prerequisites are imported without `public`: coherent inner-anodyne
  equivalences, derived-counit criterion, gluing/filtered equivalences; the boundary
  cellular statement is Mathlib `SSet.relativeCellComplexOfMono` from
  `Mathlib.AlgebraicTopology.SimplicialSet.Skeleton`. The other recorded proof
  prerequisites are already public imports of the cone-presheaf module. Every
  step of the unchanged seven-step proof is in the main theorem's docstring.

Edge cases checked before writing: for n=0 there is no positive i in Fin 1;
for n=1,i=1 the coned horn is the inner horn Λ₁². Noninjective σ and bases which
are not quasicategories remain allowed. Empty S or T has no labelled simplices
and gives the unique base-change maps; arbitrary and non-Kan presheaves remain
in the base-change and fiber clauses. Q^0=Δ^0 gives the vertex comparison. Empty
K is Kan under the all-positive-dimensional-horns definition; each Q^m has
vertices, so singQ(empty) is empty and the comparison is its weak equivalence.
No nonempty, projectively cofibrant, locally Kan, or quasicategory binder occurs.

Searches (2026-10-17):

- `msearch.py` LeanFinder: "Unstraightening commutes with base change and its
  vertex fiber is the singular complex of the pinched cubes". Eight hits about
  simplicial nerves, ordinary realization and strict Segal objects; no such theorem.
- `msearch.py` Loogle: `"SSet", "horn"`. Twelve horn results, including `SSet.horn`
  and its face maps; these supply the standard horn rather than unstraightening.
  Read the horn definition, docstring and signature in Mathlib Horn.lean.
- `msearch.py` grep: `unstraighten|straightening|SingQ|pinched.?cube`. Zero Mathlib
  matches.
- `msearch.py` LeanSearch: "unstraightening base change pinched cube singular
  complex Kan". Eight hits include `SSet.KanComplex`, ordinary topological
  singular sets and Guitart Kan base change; none is the coherent-presheaf result.
- `rg` of the same unstraightening/pinched-cube terms in the upstream
  `WeilConjectures` tree has no corresponding result; searching the item id there
  has no hit. `rg` in project `lean/Sheaf` finds the dependency modules just listed
  and the existing `singQ` construction, which is reused. A separate name search
  for the new qualified declarations found no duplicate; unrelated `restrict`
  definitions in other namespaces are not the presheaf restriction here.

Validation: the delivered module compiled via the prescribed `scompile.py`, both
as a sandbox file and under its intended module path, cleanly with no warnings.
All variables and the only universe are explicit; definitions contain real data;
all three postponed theorems are named, have source/blueprint/proof docstrings,
and are listed in this node's `lean.declarations`. No proof was supplied in stage 2.

## Second reading by Q95

I read the node statement, its source places, every recorded statement dependency,
and the delivered Lean signature item by item.

- The node's objects are arbitrary small `SSet.{u}` bases `S` (and `T`, `R`),
  `n ≥ 0`, `0 < i ≤ n`, simplex maps `σ`, enriched presheaves `F`, base maps
  `u` and `v`, enriched maps `f`, vertices `s`, and simplicial sets `K`, `K'`.
  Lean renders these as the explicit binders in
  `unstraightening_simplex_pointwise`; `Fin (n + 1)` together with `0 < i.val`
  is exactly `0 < i ≤ n`, and implies the source's redundant `n ≥ 1`.
  Verdict: same objects and no extra hypotheses.
- The right-horn clause is `weakEquivalences S ((left S).map (Over.homMk ...))`
  for `horn n i` over every `σ`; this is precisely the source's objectwise weak
  equivalence. Verdict: every quantifier and clause matches.
- The base-change clause is the single family `β` of slice isomorphisms
  `rightObj (restrict u F) ≅ (Over.pullback u).obj (rightObj F)`, followed by
  identity, composite, enriched-map naturality, and simplex-label formulas.
  `restrict` retains the complete enriched action and `baseChangeProjection`
  composes the chosen isomorphism with the pullback projection. Verdict: this is
  the stated natural isomorphism (the displayed orientation is its inverse), with
  exactly the requested coherence and canonical cone formula.
- The vertex clause is the family `e` of isomorphisms
  `Enhanced.fiber (rightProjection F) s ≅ singQ (obj F (Straightening.vertex s))`,
  with the stated map naturality. Verdict: same strict fiber, vertex object, and
  full enriched map naturality.
- `singularComparison K` is precomposition with the selected cosimplicial map
  `pinchedProjection : qFunctor ⟶ stdSimplex`; the Kan clause gives both
  `KanComplex (singQ K)` and `Enhanced.IsWeakHomotopyEquivalence`, and the last
  clause gives naturality under maps of Kan complexes. Verdict: same `Q^m → Δ^m`
  comparison and hypotheses.

Edge cases checked: no positive `i` exists for `n = 0`; `n = 1, i = 1` is
the included inner horn; noninjective simplex maps, empty bases, arbitrary
presheaves, empty and non-Kan coefficient simplicial sets remain allowed; `Q^0`
is `Δ[0]`; the empty `K` is Kan and `singQ (∅) = ∅`; all maps and fibers are
degreewise and the sole universe is explicit.

I re-ran the LeanFinder, Loogle, LeanSearch, and repository/Mathlib `rg` searches
recorded by the worker, and read the returned declarations. They find only ordinary
horn, nerve, coskeleton, and singular constructions; no existing combined theorem
or duplicate declaration exists. The source was checked directly in HTT
Proposition the project server, the right-horn assertion of Theorem the project server, the construction
before Proposition the project server, Proposition the project server, and Remark the project server.

No mismatch was found. I made no statement, dependency, or definition change.
`pinchedProjection` is the canonical map selected by the dependency's normalization
`quotientMap ≫ π = maximumMap`; the quotient map is degreewise surjective, so the
normalization determines every component. The module compiles cleanly with the
prescribed `scompile.py` invocation.
