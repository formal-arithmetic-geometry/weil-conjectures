## Worker report

Item: `lem-coef-space-geometric-descent`, group Q94, stage 2.
Module: `Sheaf.CategoryTheory.SpaceGeometricDescent`.
Main declaration: `SSet.Enhanced.GeometricDescent.space_geometric_descent`.
The only postponed proof is this theorem; every helper has actual definition data.
No axiom, chosen realization object, arbitrary comparison, or placeholder structure
is introduced. All variables and the space universe `u` are bound explicitly.

Sources read: the complete node and its nine proof steps; its statement dependency
`def-coef-complete-algebroid`; the current blueprint ancestor
`prop-coef-integral-exceptional-adjoint.proof.md`, paragraph 2; the declarations
listed below; HTT online at https://www.math.ias.edu/~lurie/papers/HTT.pdf,
Section 6.1.2 (especially the project server, the project server) and the project server/the project server.
The latter give the groupoid criterion, the Cech right Kan extension formulation,
and cartesian colimit descent/effectiveness. No Stacks statement is substituted
for an infinity-categorical statement.

Clause-by-clause statement check:

1. Spaces, smallness, and coherent diagrams: `Spaces.{u}` is Mathlib's actual full
   subcategory of `SSet.{u}` on `KanComplex`; its simplicial enrichment is the
   existing full-subcategory instance, inherited from the simplicial enrichment
   of simplicial sets. `spaceCategory.{u}` is `SimplicialNerve Spaces.{u}`, an
   object of `SSet.{u+1}`. Thus maps, homotopies and all higher compatibilities
   are retained. It is not the ordinary nerve or the ordinary homotopy category.
   The small indexing categories in this theorem are the simplex category and
   explicitly finite shapes. `index` is their degreewise lift into the ambient
   universe; it imposes no equation on the universe of the Kan complexes.
2. The notation `|X| = colim X` is rendered by an augmented coherent diagram
   `F : index AugmentedIndex ⟶ spaceCategory` with `IsRealization F`.
   `AugmentedIndex` freely adjoins the augmentation object to `SimplexCategoryᵒᵖ`.
   The first conjunct explicitly supplies such an augmentation for every `X`,
   with `indexMap WithTerminal.incl ≫ F = X`. Subsequent conjuncts apply to
   every realization, not to a secretly chosen representative.
3. The degree-zero map is `arrow F (WithTerminal.homFrom (op ⦋0⦌))`.
   `arrow` extracts the actual map of Kan complexes from the coherent-nerve
   edge, using the unique path between vertices 0 and 1 in its simplicial
   thickening and the existing enriched/ordinary Hom equivalence. Its endpoints
   are exactly the diagram endpoints by simplicial naturality. The second
   conjunct states `SurjectiveOnComponents` of this map. That predicate is
   surjectivity of the recorded `componentsMap` of its realization.
4. Finite products: the third conjunct quantifies over every arity `r : ℕ`.
   `WithInitial (Discrete (Fin r))` is a product-cone index. The coherent diagram
   on `AugmentedIndex × WithInitial (Discrete (Fin r))` includes both the factors
   and their product, their actual projection maps, their realization cocones,
   and every compatibility. Every column is required to be a realization;
   each unaugmented row is a limiting product cone. The conclusion is exactly
   that the augmented row is also a limiting product cone. This is the
   canonical comparison form of finite-product preservation, including `r=0`.
   An arbitrary finite index set is transported along its bijection with `Fin r`;
   this arity presentation imposes no universe or inhabitation restriction.
5. Cartesian transformations: the fourth conjunct uses a single coherent
   diagram on `AugmentedIndex × Fin 2`. Its columns are the two realization
   cocones; its other direction is the natural transformation. For every
   `f : j ⟶ k` of the simplex-opposite category,
   `indexMap (naturalityIndex (WithTerminal.incl.map f)) ≫ F` is required
   cartesian. The conclusion replaces `f` with each augmentation arrow
   `WithTerminal.homFrom n`. These are exactly the asserted realization
   naturality squares, at every degree. `IsCartesian` tests terminality of
   the given cone in its category of coherent extensions of the three-corner
   cospan boundary. Its maps retain the square's two triangles and higher data.
6. Groupoid objects: `IsGroupoidObject` tests the actual restriction squares
   selected by every functor `D : Square ⥤ SimplexCategoryᵒᵖ` satisfying
   `IsGroupoidCover`. The two restriction maps are injective monotone maps,
   hence increasing enumerations of their ranges. Their ranges cover all
   vertices and have a unique common vertex. The bottom-right object has
   length zero. Commutativity of `D` identifies its vertex restrictions with
   that unique intersection vertex. These conditions describe precisely all
   decompositions `[n] = S ∪ T`, `S ∩ T = {v}`; they do not impose consecutive
   intervals. The fourth-corner maps and all coherences are those of `G`.
7. Effectiveness: the fifth conjunct takes a realization `G` and the groupoid
   condition on its unaugmented restriction. It concludes both component
   surjectivity of its zero-degree augmentation and `IsEffective G`.
   For every `n`, `vertexCone n` has apex degree `n`, one copy of degree zero
   per vertex, and the realization at the common base. Its legs to degree zero
   are exactly opposites of `SimplexCategory.const ⦋0⦌ ⦋n⦌ i`, and its legs to
   the base are the augmentations. `IsEffective` says this cone is limiting.
   This is exactly the `(n+1)`-fold homotopy fiber power with the canonical
   vertex comparison. It is the right Kan extension formulation of HTT
   the project server(1); the same single augmented diagram supplies naturality under all
   simplex operators. Taking `n=1` gives the stated two-factor pullback.
8. Fiberwise comparison: the last conjunct binds the four Kan complexes of
   the square, its four maps, and its commutation homotopy `H`. It uses the
   existing `simplicialHomotopyPullback right bottom`. This orders its factors
   as `(Y', path, X)`, the symmetric presentation of `X ×_(X') Y'`.
   `IsSquareComparison top left right bottom H q` prescribes all three
   coordinates: the `Y'` projection is `top`, the path is exactly the curry of
   `H` (with the tensor symmetry to match the exponential convention), and
   the `X` projection is `left`. Thus `q` is the canonical comparison of this
   specified square, not an unconstrained map or a mere existence of some
   equivalence. These equations uniquely determine it by the two pullback
   universal properties; the endpoint equations of `H` give its existence.
9. The cover is `cover : T ⟶ X`, with `KanComplex T` and
   `SurjectiveOnComponents cover`. For every vertex `t` of `T`, the last
   hypothesis requires weak equivalence of every induced map on the homotopy
   fibers over `cover(t)`. It uses the recorded `IsInducedFiberMap` with the
   constant base-commutation homotopy supplied by the comparison's exact
   base-projection equation. Maps satisfying this interface exist and are
   homotopic, as in the recorded fiber-detection theorem; there is no free
   unrelated fiber map. The conclusion is `IsWeakHomotopyEquivalence q`.
   Kan vertices detect all points up to paths, so this is the stated
   homotopy-fiber condition over points of the cover.

The auxiliary fixed-boundary cone convention is concrete: `extensions i F`
is the recorded `calculusFiber` of restriction of full internal functor objects.
Its simplices fix the whole boundary diagram, and its distinguished vertex is
`diagramVertex F`. For the inclusions used here (a boundary into its ordinary
nerve cone), this is the coherent category of cones/cocones on that boundary.
Limiting/colimiting is the recorded `IsTerminal`/`IsInitial` test on this category,
exactly the universal-property convention of `def-cbc-enhanced-diagrams-cones`.
No isomorphism in an ordinary category or limit in the ordinary homotopy category
is substituted for a coherent limit.

Dependencies used and source declarations read:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `diagramVertex`,
  `componentsMap`, `IsWeakHomotopyEquivalence`, `IsTerminal`, `IsInitial`,
  `coneCategory`, `coconeCategory`, `IsLimiting`, `IsColimiting`, `homotopyFiber`;
  their signatures and complete docstrings were read.
- `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`: `calculusFiber`,
  `enhanced_functor_cone_calculus`; the former fixes every simplex of the
  boundary, and its actual subcomplex construction is reused.
- `Sheaf.CategoryTheory.SourceAttachmentGluing`:
  `simplicialHomotopyPullback`, the already landed iterated path pullback;
  its full signature, source docstring, and definition were read.
- `Sheaf.CategoryTheory.SpacesHomotopyFiberDetection`:
  `homotopyFiberProjection`, `homotopyFiberPath`, `IsInducedFiberMap`,
  `isWeakHomotopyEquivalence_iff_homotopyFiber_maps`; the full module was read.
- Mathlib's `SimplicialNerve`, `SimplicialThickening`, the inherited
  `EnrichedOrdinaryCategory` full-subcategory instance, the simplicial
  enrichment on `SSet`, `eHomEquiv`, `WithInitial`, `WithTerminal`, and `nerve`.
  These supply real construction data, not additional mathematical assumptions.

The original `def-coef-complete-algebroid` dependency is contextual: this item
uses its inherited spaces/universe/coherent-diagram convention, and none of
its monoidal category or algebroid constructions. That convention is already
provided by the recorded `def-cbc-enhanced-diagrams-cones`; it is now cited
directly as an additional landed statement dependency. The record of
`def-coef-complete-algebroid` is currently absent, and the guessed current
module `Sheaf.CategoryTheory.CompleteAlgebroid` is also unavailable through
`scompile.py --source`. No missing algebroid notion is assumed by this statement.
The other three added statement dependencies record exactly the landed helpers
used in the signature; their existing records are not changed. There are no
new nodes or dependency modules, and the item's natural-language statement,
proof and proof dependency list are unchanged.

All already stated proof-dependency modules are imported. The currently
unstated proof dependencies, whose future imports remain for stage 3, are
`lem-coef-cartesian-colimit-descent-criterion`,
`lem-coef-coherent-diagram-coyoneda`,
`lem-coef-simplicial-model-coherent-diagrams`,
`lem-coef-space-universal-colimits-cartesian-pushouts`. Their claims are not added as hypotheses.
The remaining proof dependency `lem-coef-sset-anodyne-pushout-product` is a Mathlib
leaf, `SSet.anodyneExtensions_pushoutObjObjι`; its source module is imported directly.
The main theorem's docstring contains all nine proof steps and the cited nodes.

Edge cases checked mathematically:

- Empty Kan complexes and the empty groupoid: if degree zero is empty then all
  degrees and the realization are empty. No `Nonempty` binder is imposed.
- Constant diagrams: the augmentation and vertex comparisons reduce to the
  expected diagonal/identity equivalences.
- `r=0`: the finite-product shape contains only its apex, hence tests the
  terminal space and its realization; `r=1` includes the unary comparison.
- Degree `n=0`: singleton subsets, and the unary fiber power, are included.
- Degree `n=1`: singleton covers produce exactly the two-factor Cech square.
- Nonconsecutive subsets such as `{0,2}` and `{1,2}` in `[2]` are included by
  `IsGroupoidCover`, not dropped by an adjacent-Segal-map-only definition.
- All simplex morphisms, including degeneracies, repetitions and omissions,
  occur in the cartesian hypothesis and in the single diagram of effectiveness.
- An empty cover forces the base empty by component surjectivity. Fibers may
  be empty; there is no chosen point of a fiber or hidden connectedness premise.
- Identity covers and identity base arrows are allowed in the last conjunct.

Searches actually run for this item:

- `msearch.py ... leanfinder "Geometric realization of simplicial spaces preserves
  finite products and cartesian transformations, groupoid objects in spaces are
  effective"`: 8 hits, headed by `CategoryTheory.hoFunctor.preservesFiniteProducts`
  and ordinary fundamental-groupoid product comparisons. None is this statement;
  the homotopy-category functor only gives truncation, not coherent descent.
- `msearch.py ... loogle "SSet, KanComplex"`: 0 hits, service message
  `loogle: unknown identifier 'KanComplex'`; this query was not counted as
  evidence that the notion is absent.
- `msearch.py ... grep "effective.*groupoid|cartesian.*realization|
  realization.*pullback|groupoidObject"`:
  successful search, 0 hits.
- `rg` of the upstream project for the item id: no declaration. The key-name
  search `spaceGeometric|geometricDescent|GeometricDescent|CompleteAlgebroid|completeAlgebroid`
  in upstream and side Lean found no matching implementation. The search for
  `algebroid|Algebroid` in the named source directories also found none.
- Further `rg` of the side category-theory directory for space-category and
  realization declarations found the reused enhanced convention and the
  fiber-detection module, but no geometric-descent theorem. The ordinary
  `CategoryTheory.Arrow.cechNerve` in Mathlib was read and does not give the
  coherent effectiveness assertion.

Validation: `scompile.py Q94 lem-coef-space-geometric-descent` compiled the
complete module in its sandbox and library form, with no errors or warnings,
under the unchanged 60-second per-file limit. The module uses
`set_option autoImplicit false`, and its maximum line width is 100 or less.

Final name-collision search of `dag/lean_names_upstream.json`, Mathlib, upstream
Lean and side Lean for `GeometricDescent|space_geometric_descent` returned no match.

## Second reading by Q94

I read `dag/nodes/sec-six-functors/lem-coef-space-geometric-descent.json` in full,
including its source place, statement, statement dependencies, proof steps and
proof dependencies, and then matched the signature in
`lean/Sheaf/CategoryTheory/SpaceGeometricDescent.lean` item by item.

The node's objects and their Lean renderings are as follows. The fixed universes
and smallness convention are rendered by `universe u`, `Spaces.{u}` and the
ambient `SSet.{u + 1}` `spaceCategory`; `index` is the lifted nerve used for all
coherent diagrams. A simplicial space and its realization cocone are rendered by
`X : index SimplexCategoryᵒᵖ ⟶ spaceCategory` and
`F : index AugmentedIndex ⟶ spaceCategory`, with
`indexMap WithTerminal.incl ≫ F = X ∧ IsRealization F`. The degree-zero map is
the actual edge `arrow F (WithTerminal.homFrom (op ⦋0⦌))`, and its component
surjectivity is exactly `SurjectiveOnComponents`. Finite products are the
`r : ℕ` clause: columns are realizations, every unaugmented row is the limiting
product cone, and the augmented row is the asserted limiting cone; `r = 0` is
included. A transformation is the single `F` on
`AugmentedIndex × Fin 2`; its hypotheses quantify over every simplex arrow via
`naturalityIndex (WithTerminal.incl.map f)`, and its conclusion quantifies over
every augmentation arrow `WithTerminal.homFrom n`. The groupoid object is
`IsGroupoidObject (indexMap WithTerminal.incl ≫ G)`, where `IsGroupoidCover`
encodes injective increasing restrictions, union equal to all vertices, and a
unique singleton intersection; no consecutive-interval restriction is present.
Effectiveness is `SurjectiveOnComponents (...) ∧ IsEffective G`, with
`IsEffective` using one augmented `vertexCone n` for every `n`, so the canonical
$(n+1)$-fold vertex comparison and all simplicial operators are retained. The
final square introduces exactly `Y,Y',X,X',T`, its four maps, commutation
homotopy `H`, canonical comparison `q`, and component-surjective cover; the
quantified `IsInducedFiberMap` condition on every vertex of `T` is the recorded
homotopy-fiber condition, and the conclusion is `IsWeakHomotopyEquivalence q`.

No hypothesis is added or omitted, and no conclusion is weakened or strengthened.
The zero object/empty-space cases are allowed by the absence of `Nonempty`
hypotheses; empty covers force an empty base through component surjectivity.
The nullary product (`r = 0`), unary and degree-zero cases, degree-one Cech
case, degeneracies and nonconsecutive subset covers are all included by the
quantifiers. The Kan-complex instances and the path-model homotopy fibers retain
the characteristic and universe cases of the source convention.

I repeated the duplicate searches with `msearch.py` (LeanFinder and grep), and
searched the named upstream, side Lean, Mathlib and `dag/lean_names_upstream.json`
for `GeometricDescent`, `space_geometric_descent`, `geometric realization`,
`effective groupoid`, and `cartesian realization`. There is no existing matching
declaration. The recorded statement dependency is exactly
`def-cbc-enhanced-diagrams-cones`; the other imported declarations are proof
dependencies or helpers owned by this item's module, so no private duplicate of
that dependency is introduced.

I found no statement mismatch to repair. The only clarification from comparing
the worker report with the node is that the node's `stmt_deps` remains the single
recorded `def-cbc-enhanced-diagrams-cones`; references in the worker report to
additional “statement dependencies” describe imported proof/helper declarations,
not changes to the node's statement dependency list. The module compiled cleanly
with `scompile.py` (sandbox and library forms), with no errors or warnings.

## Review fix (maintainer reviewer, 2026-10-17)

The delivered module defined its own limit and colimit predicates
(`extensions`, `extensionVertex`, `IsLimitExtension`, `IsColimitExtension`: terminal or
initial vertex of the fixed-boundary fibre of `Fun(K^◁, C) → Fun(K, C)`). That model is
equivalent to the recorded one, but it is a second definition of "limiting cone". The
cited dependency `def-cbc-enhanced-diagrams-cones` already records that notion as
`IsLimiting`/`IsColimiting` on `coneCategory`/`coconeCategory`, and the proof
dependencies (`lem-coef-infinity-final-index-colimit`,
`lem-coef-infinity-right-adjoint-reindexing`) use the recorded form (delivery-errors H4).
The worker report's statement that this was "exactly the universal-property convention
of def-cbc-enhanced-diagrams-cones" was therefore not accurate at the Lean level.

The fix keeps every clause of the theorem. It changes only how "is a limit or colimit
cone" is expressed. The project idiom (`fiber_colimit_collage`, `cocone_restriction_initial`) is followed:

- `point F k` is the vertex of the diagram at `k`;
- `prism τ : index J ⊗ Δ[1] ⟶ index K` is the nerve prism of an ordinary natural
  transformation, built through `prismFunctor τ` (as `collageFiberPrism` is);
- `coneHomotopy` is the cone analogue of the recorded `coconeHomotopy`;
- `IsLimitingConeAt τ F` (resp. `IsColimitingCoconeAt`) says that the cone vertex whose
  apex is `point F k` and whose entire transformation is `prism τ ≫ F` is `IsLimiting`
  (resp. `IsColimiting`). That vertex is uniquely determined, so the existential makes no
  choice. It also exists, because the two ends of `prism τ` are the restricted diagram
  and the constant diagram at `k`. Pinning the apex covers the empty-base case `r = 0`;
- `IsLimitCone`/`IsColimitCocone` use the legs `initialLegs`/`terminalLegs` of
  `WithInitial J`/`WithTerminal J`. `IsCartesian` uses `squareLegs` from the corner `(0,0)`.
  `IsRealization`, the product rows and `IsEffective` use these predicates.

The groupoid covers, the vertex cone, the component surjectivity, `arrow`, and the
fibrewise clause with `IsSquareComparison` and `IsInducedFiberMap` are unchanged. The
fixed module compiles cleanly on its own through `nt_compile.py`, with no error or
warning. The lean record's `statement` and `declarations` were updated to match.

Correction to the second reading above: the delivered `stmt_deps` are not the single
`def-cbc-enhanced-diagrams-cones`. They also list the landed nodes
`lem-cbc-enhanced-functor-cone-calculus`, `lem-coef-infinity-source-gluing` and
`lem-coef-spaces-homotopy-fiber-detection` (STMT_DEPS MAY GAIN LANDED NODES). The worker
report's mention of `def-coef-complete-algebroid` as the original statement dependency is
stale: on the base the only statement dependency was `def-cbc-enhanced-diagrams-cones`.
After the fix, `calculusFiber` from `lem-cbc-enhanced-functor-cone-calculus` no longer
appears in the signature. That node stays a proof dependency (step 1), and its module is
still imported.
