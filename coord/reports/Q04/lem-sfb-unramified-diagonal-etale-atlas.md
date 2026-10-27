## Worker report

The module `Sheaf.AlgebraicGeometry.UnramifiedDiagonalEtaleAtlas` states
`CategoryTheory.unramifiedModuliDiagonal_iff_etaleAtlas`, with proof `sorry`.
The source read is Stacks `stacks-morphisms.tex`, theorem-DM (06N3), including
its complete regular-slice construction, and lemma-separated-implies-morphism-separated
(050N), part (1). The latter identifies the relative-base formulation.
No split is attempted: Q33's reviewed eleven-step split is retained verbatim.
The earlier worker's stale-assignment diagnosis concerned splitting a reviewed node;
this delivery only attaches its Stage 2 statement.

Clause-by-clause correspondence:

- The scheme S is the explicit universe-polymorphic binder `{S : Scheme.{u}}`.
  An arbitrary category over S-schemes is `F : BasedCategory.{v, w} (Over S)`;
  the total-category object and arrow universes remain independent.
- The stack-in-groupoids condition is `hstack : IsModuliStack F`. Its recorded
  definition includes `IsFibredInGroupoids`, isomorphism gluing and effective
  object descent for the etale topology. No coarse set of isomorphism classes
  replaces the groupoid or its automorphisms.
- Representability of the relative diagonal is `hdiag : HasAlgebraicSpaceDiagonal F`.
- The algebraic-stack smooth surjective scheme-atlas hypothesis is `hatlas`.
  `U : Over S` is the atlas scheme with its structure map; `a` is its map to F.
  For every test scheme `T` and map `t`, the witnesses `Z,p` and
  `HasSpaceBaseChange a T t Z p` identify the actual two-fibre product with an
  algebraic space and pin its projection to T. `SpaceMapIsSurjective Z T p`
  expresses surjectivity. The final universal quantifiers over `V,b`, with
  `AlgebraicSpace.IsEtale b`, test smoothness of this projection on every etale
  scheme chart, using `AlgebraicGeometry.Smooth ((yoneda.preimage (b ≫ p)).left)`.
  Thus representability, smoothness and surjectivity are all tested after every
  scheme base change. No finite-type, quasi-compact or separated atlas is assumed.
- Relative unramified diagonal is the existing `HasUnramifiedModuliDiagonal F`.
  Its defining tests retain both comparisons from the representing algebraic space
  to `T` and `U` and use their product in `Over S`, hence the relative product
  `T ×_S U`. `SpaceMapIsUnramified` uses the recorded `IsUnramified` on all
  representable etale scheme charts. This includes both locally finite type and
  open-immersion diagonal, not just formal unramifiedness.
- The first equivalence quantifies `W : Over S` and its map `a`, with every
  scheme base change represented by `Z,p` and identified by `HasSpaceBaseChange`.
  `SpaceMapIsEtale Z T p ∧ SpaceMapIsSurjective Z T p` gives exactly the
  representable surjective etale atlas. `SpaceMapIsEtale` uses the recorded
  Mathlib `AlgebraicGeometry.Etale` on every etale scheme chart.
- The final conjunct is explicitly
  `HasUnramifiedModuliDiagonal F ↔ IsDeligneMumfordModuliStack F`.
  Unfolding the latter gives the assumed stack condition, representable diagonal,
  and exactly the same etale atlas existential. It adds no condition.
- The sentence on open substacks fixes vocabulary but imposes no extra hypothesis
  or conclusion on this equivalence. The imported recorded `OpenModuliSubstack`
  supplies precisely that full, pullback-stable, scheme-tested open notion.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsModuliStack`, `HasAlgebraicSpaceDiagonal`,
  `HasSpaceBaseChange`, `discreteModuli`, `SpaceMapIsEtale`,
  `SpaceMapIsSurjective`, `IsDeligneMumfordModuliStack` (full signatures and
  docstrings read, together with their fibre-product and based-functor conventions).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`,
  via the public import in `OpenModuliSubstack`.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`:
  `CategoryTheory.SpaceMapIsUnramified`, `HasUnramifiedModuliDiagonal`.
  This already landed node is added to `stmt_deps` under the explicit permission
  to gain recorded landed definitions. No existing notion is duplicated.

All already stated proof dependencies have proof-only imports: chartwise etale
permanence, dense separable points, smooth regular local rings, the unramified
local criterion, local Nakayama, regular systems of parameters, and scheme
coproducts. The generic algebraic-space and smooth definitions are also available
through the public statement imports. The nine new stack/space supporting lemma
nodes of Q33 have no Lean record or Mathlib match at this reading; there is no
proof-only module to import yet. They are not needed to type the statement.
Their node ids and precise uses are retained in the theorem's eleven-step proof
docstring. Their future imports are for the maintainer after statement landing.

Edge cases checked before writing:

- Empty stack: there is no `Nonempty` hypothesis on W or U; the empty atlas and
  empty disjoint union are admitted. For an empty target, pointwise surjectivity
  has no points to test, as required.
- Empty relative base scheme, empty scheme tests and empty charts impose no
  accidental point-existence or finite-type condition.
- Arbitrary base S, including nonreduced and nonseparated bases, is retained.
  The product is over S; no absolute-product substitute or separatedness is used.
- Arbitrary residue characteristics and nontrivial stabilizers are retained;
  no tame, finite, reduced, trivial-inertia or characteristic-zero assumption occurs.
- The source's zero-dimensional regular local slice permits the empty parameter
  list, explicitly covered by the proof docstring.
- There is no independent index universe for a new coproduct in the statement;
  atlas schemes stay in `Scheme.{u}`, while F's category universes are explicit.

Searches for existing notions/statements:

- `msearch.py leanfinder`: “An algebraic stack has unramified diagonal if and only
  if it has a surjective etale scheme atlas” returned eight scheme-level
  unramified/etale and diagonal facts, no algebraic-stack equivalence.
- `msearch.py leansearch`: “algebraic stack unramified diagonal equivalent
  surjective etale atlas by a scheme” returned eight ring/scheme formal
  unramifiedness and etale declarations, no stack atlas criterion.
- `msearch.py loogle`: `"Etale", "diagonal"` returned three WeaklyEtale
  diagonal-flatness facts; none states this theorem.
- `msearch.py grep`: `IsAlgebraicModuliStack|SpaceMapIsSmooth|unramified.*atlas|atlas.*unramified`
  returned zero Mathlib matches.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id, unramified
  diagonal, algebraic stacks and smooth atlas definitions found the existing
  OpenModuliSubstack interface and the consumer CurveStackInfinitesimalDmLocus,
  but no statement of this criterion. The field-specific
  HasSmoothFiniteTypeModuliAtlas is a different, stronger atlas notion and is
  not used. Direct reads of Mathlib Smooth/Etale and project UnramifiedMorphism
  confirm reuse of the recorded definitions.
- Searches in DAG definition nodes and `tools/blueprint_refs.py search
  'algebraic stack'` (zero blueprint hits) were used to check vocabulary;
  no new definition node is required because the smooth-atlas hypothesis is
  written out using existing constructions.

No statement correction, dependency repair, new node or disputed mathematical
statement is needed. The live node's statement, proof and review remain intact.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
