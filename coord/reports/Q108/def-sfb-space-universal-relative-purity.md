## Worker report

The new module `Sheaf.AlgebraicGeometry.SpaceUniversalRelativePurity` defines
`AlgebraicGeometry.AlgebraicSpace.relativeAssassin`, `IsImpurityOverScheme`, and
`IsUniversallyPureRelativeToScheme`. There are no theorems and no `sorry`s in this
module. The node's mathematical statement is unchanged.

The sources read were Stacks `spaces-flat.tex`, situation-pre-pure,
definition-impurity (0CV8), and definition-pure (0CVD), specifically clauses (2)
and (4), together with `spaces-divisors.tex`, lemma-relative-assassin and
definition-relative-weak-assassin (0CV0). The source identifies association with
weak association on the locally Noetherian fibres occurring here. The predicate
is the absence of impurities everywhere on the base, not just above one fixed
point. This is a prerequisite below the current blueprint's six-functor
constructibility-stability unit, not that unit's own statement.

Clause and hypothesis correspondence:

- Work over Spec Z, with the size convention: the main predicate has
  `X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))`, where `u` is explicit.
  The lift represents Spec Z in the chosen scheme universe. `Y` and every test
  `B` are `Over` this same scheme. Thus every scheme B and every map B -> Y in
  the chosen universe is allowed, including the identity. There is no unrelated
  smaller universe on tests, nor an extra size hypothesis.
- X is an algebraic space, Y a scheme, and f : X -> Y:
  `X`, `Y : Over ...`, and `f : X ⟶ schemeSpace Y` use the actual Yoneda sheaf
  of the scheme Y. Scheme structure maps to Spec Z are unique, so requiring
  morphisms in this over-category adds no geometric condition.
- f is finite type: `_hf : MapIsFiniteType f`, the dependency's quasi-compactness
  and locally-finite-type chart test. Quasi-separatedness is precisely
  `_hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom)`, with no separatedness
  or properness assumption. These proof parameters specify the domain of the
  definition; they do not become implications making purity vacuous outside it.
- M is quasi-coherent: `M : X.QCoh` uses the dependency's full subcategory for
  Mathlib's site quasi-coherence predicate. Finite type is
  `_hM : SheafOfModules.IsFiniteType M.obj`, Mathlib's local finite generation
  by sections on this small étale site. Its objects are precisely the
  representable étale scheme charts. This is the stated étale-local finite
  generation condition, with no coherence or finite-presentation restriction.
- For every scheme B -> Y: the body quantifies over every `B : Over ...` and
  `g : B ⟶ Y`. `gSpace` is the actual Yoneda map, `ObjectProperty.homMk
  ⟨yoneda.map g⟩`, with no chosen or unconstrained comparison.
- X_B is `enlargedFibreProduct f gSpace`, the existing sheaf fibre product,
  bundled with its algebraic-space property. `fB` is its actual second
  projection; its first projection is `enlargedFibreProductFst f gSpace`.
  `MB` is `(moduleTensorPullback (enlargedFibreProductFst f gSpace)).obj M.obj`,
  the recorded canonical tensor pullback, with no arbitrary module supplied.
- Ass_{X_B/B}(M_B): `relativeAssassin B fB MB` is the set of points ξ for which
  there exist `T : XB.EtaleSite` and `t : XB.etaleForget.obj T` with
  `t ∈ Scheme.Modules.relativeAssassin ... ((XB.schemeRestriction T).obj MB)`
  and `schemePointMap T.obj.hom t = ξ`. This is exactly the union of images of
  the scheme relative assassins over all representable étale scheme charts.
  The chart-to-base scheme map is the actual Yoneda preimage of the composite
  chart map and fB. `schemeRestriction` is restriction to Zariski opens, the
  ordinary module associated to this chart restriction. Thus the scheme
  relative assassin uses the supplied stalkwise fibre-module association.
- The point classes and topology are the existing `Point`, `schemePointMap`,
  `mapPoint`, and `pointTopologicalSpace`. The scheme point b is represented
  canonically by `schemePointMap (𝟙 (yoneda.obj B)) b`; equality of point
  classes expresses equality of the underlying scheme point, with no chosen
  inverse map from point classes to a scheme's carrier.
- A specialization b' -> b is literally `b ∈ closure ({b'} : Set B.left)`.
  Being over b' is `mapPoint fB.hom.hom ξ = schemePointMap (𝟙 _) b'`.
- `IsImpurityOverScheme` records the specialization, association, and image
  equality, together with the negation of existence of θ in `closure {ξ}`
  over b. Applying it to X_B, fB, M_B is precisely an impurity of the node.
- Universal purity uses the positive form the node explicitly specifies:
  for every B, g, b', b, ξ satisfying those three conditions, there exists
  `θ : Point XB.obj.obj` with `θ ∈ closure {ξ}` and fB(θ) equal to b.
  The point θ is not required to be associated. No closure in a chart, or in
  the original X instead of X_B, is substituted. The internal `let`s name
  constructed objects in a definition body, not assumptions or let-binders in
  a theorem signature.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `EtaleSite`, `etaleForget`, `structureSheaf`, `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsFiniteType`;
  its existing `ProperCurveModuli` import supplies `MapIsQuasiCompact` and
  `mapPoint`, read in their source.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleDirectImageModel`, `moduleDirectImage`, `moduleTensorPullback` and
  `moduleTensorAdjunction` were read; the definition uses `moduleTensorPullback`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, used by the existing bundled fibre product.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`,
  `enlargedFibreProduct`, `enlargedFibreProductFst`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction`,
  including the canonical `schemeOpensRingHom` construction.
- `Sheaf.AlgebraicGeometry.RelativeAssassin`:
  `Scheme.Modules.associatedPoints`, `Scheme.Modules.relativeAssassin`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses` and
  `AlgebraicSpacePointTopology`: `Point`, `schemePointMap`, `PointRepresentative.map`,
  `pointTopologicalSpace`; the point images are expressed with `mapPoint`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`:
  `SheafOfModules.IsFiniteType`, whose full class definition was read.

The existing definition-owner nodes `def-trf-scheme-algebraic-space`,
`def-sfb-space-sheaf-fibre-product`, and `def-trf-space-module-scheme-restriction`
were added to `stmt_deps`, as allowed for landed notions. They have usable Lean
records, so no new nodes or dependency repair modules were needed. Their full
statements and Lean records were read. No other node field changes.

Edge cases checked mathematically before writing:

- Empty X or empty B has no ξ, so the universal condition is vacuous.
- M = 0 has empty fibrewise relative assassin; purity is vacuous, not false.
- b = b' permits θ = ξ. Reflexivity is included, not silently excluded.
- The identity morphism with its structure module has the required lift b,
  after every base change. No condition excludes identity base change.
- For D(t) -> A1 over a field, with its structure module, the generic
  associated point over the generic point cannot specialize above t = 0.
  The definition detects that impurity; it is not a tautology following from
  stability of module support under specialization.
- A non-Noetherian B is allowed. No Noetherian, flatness, proper-support or
  finite-presentation hypothesis is introduced. Finite type of the original
  morphism supplies the locally Noetherian fibres in the source's comparison
  of Ass and WeakAss, without restricting the base.

Searches actually made:

- `msearch.py ... leanfinder "universal relative purity module algebraic space
  absence impurities associated points specialization"`: eight hits, including
  `specializingMap_isZariskiLocalAtTarget` and valuative criteria; none defines
  module impurities on algebraic spaces.
- `msearch.py ... leansearch "universally pure quasi coherent module relative
  algebraic space associated points impurities"`: eight hits, including site
  quasi-coherence and associated primes; no purity definition.
- `msearch.py ... loogle "AlgebraicGeometry, Pure"`: zero hits, with note
  `unknown identifier 'AlgebraicGeometry'`. This query is inconclusive, not
  evidence of absence. Follow-up `loogle '"Specializes"'` succeeded with
  twelve hits for the topological specialization relation, not module purity.
- `msearch.py ... grep 'impurit|universally.?[Pp]ure|relative.?[Pp]urity'`:
  zero Mathlib hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for impurity, universal
  purity and relative purity found only unrelated Weil weights, cohomological
  purity, and ring-theoretic filtration purity, not this notion. A further
  relative-assassin search found the recorded scheme declaration and its
  consumers, but no algebraic-space relative assassin. The exact node-id
  search in `lean/WeilConjectures` returned no hits. Existing names and actual
  signatures were inspected instead of replacing dependency notions.

Validation: `scompile.py Q108 def-sfb-space-universal-relative-purity
lean/Sheaf/AlgebraicGeometry/SpaceUniversalRelativePurity.lean` compiled both
sandbox and library forms cleanly on the server (5.2 s and 5.7 s).
No errors, warnings, node faults or STATEMENT-DISPUTED issues were found.

## Second reading by Q108

No second reading by a worker: since 2026-10-17 the worker delivers directly and
the maintainer's independent review is the only review. The worker's self-check
matched each original clause against the declaration above, including the
specialization direction, the actual base-changed module, all chart images,
and existence of a point in the space closure. No independent reading is claimed.
