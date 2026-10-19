## Worker report

The module `Sheaf.AlgebraicGeometry.NonzeroDifferentialGenericallyEtale` states precisely
Stacks Project Tag 0C1C, `curves.tex`, `lemma-generically-etale`, equivalence (1) and (4).
I read the source lemma and proof, and checked the tag against `tags/tags`. No mathematical
statement, dependency list, or proof plan is changed. The node copy changes only `lean`.

The additional declaration `AlgebraicGeometry.Scheme.Hom.cotangentMap` is the canonical map
already introduced in this item's natural statement. It has actual data: take the inverse
of the section-normalized tensor-pullback Hom equivalence, applied to the map obtained from
the existing universal derivation. The upstream `pushforwardDerivation` sends a function
`a` on `Y` to `d(h.app a)` on its inverse image. Its descent along
`relativeDifferentialsHomEquiv` therefore sends `da` to `d(h.app a)`.
`relativeDifferentialsCongr w` transports the resulting target from `h ≫ pY` to `pX`.
The adjunction chosen from `exists_tensorPullbackAdjunction` has its unit explicitly
normalized by `m ↦ 1 ⊗ m`; consequently its inverse Hom equivalence gives the specified
map on the tensor pullback, not an arbitrary map or an arbitrary adjunction structure.
This choice is allowed because the normalized universal property determines the map.
The helper belongs to the map in this node, is listed in `lean.declarations`, and has its
own source/blueprint docstring. No new independent notion or new node is introduced.

Hypothesis and clause correspondence:

- A field `k`: `{k : Type u} [Field k]`. The universe `u` is explicitly declared.
- Schemes over that field: `{X Y : Scheme.{u}}`, with the named structure maps
  `(pX : X ⟶ Spec (.of k))` and `(pY : Y ⟶ Spec (.of k))`. Explicit structure maps follow
  the recorded curve declaration, which takes that map as its argument.
- Separated integral schemes of finite type and dimension one:
  `[IsIntegralCurve pX] [IsIntegralCurve pY]`. I read the current source of `IsVariety`
  and `IsIntegralCurve`: the former includes `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsIntegral`; the latter adds `topologicalKrullDim X = 1`.
- Smooth over `k`: `[Smooth pX] [Smooth pY]`, the recorded Mathlib notion, without adding
  smoothness of `h`, geometric integrality, projectivity, properness or perfectness of `k`.
- Every `k`-morphism: `(h : X ⟶ Y) (w : h ≫ pY = pX)`. The triangle equation expresses
  being over `k`; it is not an extra geometric condition.
- The sheaves associated on affine charts to Kahler differential modules:
  `pY.relativeDifferentials` and `pX.relativeDifferentials`. These reuse the existing
  construction in the recorded proof dependency `def-sc-relative-differential-sheaf`.
  Its `relativeDifferentialsSpecIso` and restriction isomorphisms identify it with the
  sheaf associated to the affine `KaehlerDifferential`; the construction is not duplicated.
- Module pullback: the helper's source is exactly
  `(Scheme.Modules.tensorPullback h).obj pY.relativeDifferentials`, using the recorded
  tensor-formula functor. Its target is `pX.relativeDifferentials`.
- The map on local functions is the helper construction explained above; the source
  declaration `pushforwardDerivation_desc_app_d` confirms its formula on generators.
- Nonzero as a morphism of sheaves: `h.cotangentMap pX pY w ≠ 0`.
- If and only if: `↔`, retaining both implications.
- Nonempty open subscheme of the source: `∃ V : X.Opens, (V : Set X).Nonempty ∧ ...`.
  An open of `X` gives its canonical open subscheme and inclusion `V.ι`.
- The restricted map is etale: `Etale (V.ι ≫ h)`, the recorded Mathlib predicate.

Dependency declarations used in the statement/construction (full signatures and docstrings
were read in the local source, or via `scompile.py --source` for current-only modules):

- `def-pc-curve`: `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`,
  `AlgebraicGeometry.IsIntegralCurve` and its parent `IsVariety`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`.
- `def-weil-pbc-kahler-differentials`: `Mathlib.RingTheory.Kaehler.Basic`,
  `KaehlerDifferential`, `KaehlerDifferential.D`, and `linearMapEquivDerivation`,
  realized sheafwise by the existing relative-differential construction.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`.
- `def-pc-module-pullback`: `WeilConjectures.AlgebraicGeometry.TensorPullback`,
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` (publicly imported by its adjunction).
- Existing canonical adjunction: `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`,
  `AlgebraicGeometry.Scheme.Modules.exists_tensorPullbackAdjunction`. This is the recorded
  declaration of `lem-pc-module-pullback-adjunction`, a prerequisite of module pullback.
- `def-sc-relative-differential-sheaf` and `lem-sc-smooth-omega-finite-locally-free`:
  `WeilConjectures.AlgebraicGeometry.Modules.Differentials`,
  `Scheme.Hom.relativeDifferentials`, `relativeDifferentialsHomEquiv`,
  `pushforwardDerivation`, `relativeDifferentialsCongr`, and
  `isFiniteLocallyFreeOfRank_relativeDifferentials`.

The other already stated proof dependencies are imported without `public`:
`Sheaf.AlgebraicGeometry.FunctionField` (`Scheme.functionFieldOfComponents`, with the
integral generic stalk supplied by Mathlib `Scheme.functionField`),
`Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg`
(`finiteType_domain_ringKrullDim_eq_trdeg`),
`WeilConjectures.AlgebraicGeometry.TensorPullbackTilde`
(`Scheme.Modules.exists_tensorPullback_tilde_iso`),
`Mathlib.RingTheory.Kaehler.Basic` (the first exact sequence),
`Mathlib.RingTheory.Etale.Kaehler` (localization of differentials),
`Mathlib.Algebra.Module.LocalizedModule.Exact` (exactness of localization),
`Sheaf.RingTheory.DimensionAtPointLocalRingTrdeg`
(`topologicalKrullDimAt_eq_ringKrullDim_add_trdeg`),
`Sheaf.AlgebraicGeometry.UnramifiedAlgebraOverFieldProduct`
(`exists_algEquiv_pi_finite_separable_of_unramified_spec`), and
`WeilConjectures.AlgebraicGeometry.Regular` (`isIntegrallyClosed_stalk_of_smooth`).
The finite presentation, finite type and open-diagonal notions are available through the
Mathlib morphism imports. The proof-only node `lem-a1-nonconstant-normal-curve-map-flat`
has no recorded declaration or Mathlib match in the supplied DAG snapshot, so there is no
module to import for it yet; its exact use remains documented in the theorem's proof
paragraph 6. It is not needed to elaborate the statement or construct the differential.

Edge cases checked before writing: integral curves have nonempty underlying space and
exact dimension one, so the empty scheme and zero-dimensional schemes are excluded by the
node itself. The empty open is excluded explicitly by `Set.Nonempty`. The identity has
nonzero differential and is etale on the whole curve. A constant morphism of smooth curves
has zero differential and no nonempty etale restriction. In positive characteristic,
Frobenius on the affine line has zero differential and no such etale open. No separability,
finite morphism, properness, algebraically closed field, rational point, or characteristic
zero hypothesis is imposed. Curves smooth but not geometrically integral remain included.
The helper works for arbitrary commutative triangles of schemes, without requiring curves.

Searches (all msearch calls used group Q131 and this item):

- LeanSearch: `A morphism of smooth curves has nonzero differential if and only if it is
  etale on a nonempty open subset`: 8 hits, general smooth/etale APIs and unrelated manifold
  differentials; no curve criterion.
- LeanFinder: `A morphism of smooth integral curves has nonzero differential if and only if
  it is etale on a nonempty open subset`: 8 hits, general etale classes and algebra etale
  loci; no matching statement.
- Loogle: `AlgebraicGeometry.Etale, KaehlerDifferential`: 0 hits.
- Mathlib grep: `generically.?[eé]tale|nonzero.*[dD]ifferential|[dD]ifferential.*nonzero`:
  4 hits, all about homological-complex shapes, not curve differentials.
- LeanFinder: `Canonical map on relative differential sheaves induced by a morphism of
  schemes over a base via tensor pullback`: 8 hits, including algebraic differential maps
  and presheaf restriction maps, not the needed scheme tensor-pullback arrow.
- Mathlib grep under `AlgebraicGeometry`:
  `pushforwardDerivation|cotangentMap|relativeDifferentialsHomEquiv`: 0 hits.
- `rg` in the upstream `WeilConjectures`, published `lean/WeilConjectures`, and `lean/Sheaf`
  searched differential map spellings, pullback/differential combinations, and the chosen
  names `cotangentMap` and `cotangentMap_ne_zero_iff_exists_etale_open`: no existing arrow
  or curve equivalence under those names. Reading the actual modules located the universal
  derivation and pushforward derivation used for the construction.
- Exact item-id search in the source repository: no match. DAG search for differential
  morphisms in the curve chapters found this item and its consumers, not a separate
  canonical-map node. The existing sheaf node supplies the sheaves without duplication.

Validation: prescribed `scompile.py Q131 <item> <module>` passed, compiling the sandbox
and library form separately with the default 60-second per-file limit (7.8 s and 4.1 s).
No errors or warnings were printed. All variables and universes are explicit. The only
`sorry` is the named main theorem; its docstring records the full node proof route.
No statement dispute, statement correction, dependency repair, or new node is needed.

## Second reading by Q131

Author's second reading, not a claim of independent review: I reopened the node and the
completed module and compared the field, curve, smoothness, triangle, source and target
of `dh`, its local-function formula, nonvanishing, both logical directions, nonempty source
open, and etaleness of the restriction as listed above. I specifically checked that the
curve class imposes neither properness nor geometric integrality, that the restriction
is over an open of X (not a neighborhood in Y), and that `w` only encodes k-linearity.
I checked that the adjunction is the normalized `exists_tensorPullbackAdjunction`, rather
than choosing a bare `Nonempty` adjunction that would lose the map's section normalization.
The helper contains no `sorry` and the theorem proof is exactly `sorry`. No mismatch was
found and no mathematical statement was changed. The maintainer supplies the independent
review under the dispatcher's direct-delivery protocol.
