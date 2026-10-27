## Worker report

States `AlgebraicGeometry.AlgebraicSpace.perfect_quasiCoherent_uniformTor` in
`Sheaf.AlgebraicGeometry.SpacePerfectUniformTor`. Its only proof is `sorry`.
No definition, instance, theorem proof, new node, or dependency repair is supplied.

The previous BLOCKED ending concerns an unchanged stage-1 split, not this stage-2
statement. The current brief-stage2 §0 explicitly resolves that handoff: the live
node is split, is in coord/queue.tsv at stage 2, and has no Lean record. There is no
coord/repair-notes/lem-sfb-space-perfect-uniform-tor.json. The accepted statement,
proof, and proof dependencies are preserved verbatim.

Hypothesis-by-hypothesis and clause-by-clause:

- The size convention is rendered by explicit universes `u w`, `S : Scheme.{u}`,
  and `[HasDerivedCategory.{w} X.SmallModules]`. The localization morphism universe
  is arbitrary; no equality with `u` is assumed.
- A scheme S and algebraic space X over S are `{S : Scheme.{u}}` and
  `(X : AlgebraicSpace S)`, using the actual fppf sheaf construction.
- The small étale structure sheaf and its module sheaves are represented by the
  already published small affine basis: `X.smallStructureSheaf`, `X.SmallModules`.
  `smallModuleEquivalence : X.Modules ≌ X.SmallModules` is the equivalence whose
  functor restricts to the actual affine charts. It preserves the section universe;
  the statement introduces no coefficient lift and excludes no original module.
- `E : X.DerivedModules` is an arbitrary object of the unbounded derived category,
  not an object assumed in D_QCoh. The latter membership is a conclusion.
- Quasi-compactness, every open cover having a finite subcover, is exactly
  `(hqc : CompactSpace (Point X.obj.obj))` with the existing atlas topology.
- Perfectness is `(hE : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u,u,u,w}
  X.smallStructureSheaf E)`. This recorded definition is existence of a locally
  strict-perfect complex representing E. Its covering-sieve models are bounded,
  and its degreewise package gives retractions of finite tuple structure modules.
  Ranks and bounds depend on the chart, with no chain-map requirement on splittings.
- The quasi-coherent-cohomology conclusion is `X.derivedQCohProperty E`: for every
  integer n, the inverse module equivalence takes H^n(E) to a module satisfying
  Mathlib's `SheafOfModules.IsQuasicoherent` on the original étale site.
- The global interval is `∃ a b : ℤ, a ≤ b ∧ ...`, outside both universal binders.
- Every structure-module sheaf in degree zero is `∀ M : X.SmallModules` followed
  by `(DerivedCategory.singleFunctor X.SmallModules 0).obj M`. Every original
  module is represented under the specified module equivalence.
- K-flat tensor is precisely the recorded
  `SheafOfModules.siteDerivedTensorIndependentCoefficients.{u,u,u,w}` applied to
  the small model topology and its actual commutative structure sheaf, then to
  E and M[0]. No arbitrary bifunctor or extra comparison is hypothesized.
- Vanishing for every i outside the interval is `∀ i : ℤ, i < a ∨ b < i →
  IsZero ((DerivedCategory.homologyFunctor X.SmallModules i).obj (...))`.
- There is no quasi-separatedness, Noetherian, rank-bound, quasi-coherence of M,
  enough-points, or constructibility hypothesis.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `structureSheaf`, `Modules`; `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, the transparent Mathlib module-sheaf category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`; cohomology and single functors are the
  existing derived-category functors, not copied.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, the
  specialization of Mathlib `SheafOfModules.IsQuasicoherent`, and slice instances.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `IsPerfectOnRingedSiteOfUniverses`, `IsLocallyStrictPerfectComplexOfUniverses`,
  `StrictPerfectCoefficientRepresentationOfUniverses`; the source was read down
  through the local bounded complex and finite-free-retract package fields.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `siteDerivedTensorIndependentCoefficients`, with its resolving-class tensor
  comparison and uniqueness specification. Its definition selects only the
  mathematically determined localization descent, not arbitrary tensor data.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`:
  `smallStructureSheaf`, `SmallModules`, `smallModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `derivedQCohProperty`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `pointTopologicalSpace`, on `Point` from AlgebraicSpacePointClasses.

The last three owning nodes are already landed with usable Lean records and are
added to stmt_deps under the rule permitting added landed statement dependencies.
This records the existing equivalent representation, not a statement correction.

Proof-only imports retain the recorded modules of
lem-trf-space-fibre-products-etale-covers, lem-a1-etale-scheme-map-open-image,
lem-trf-space-chartwise-etale-permanence,
lem-weil-pbc-ringed-sheaf-slice-adjunction,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback, and
lem-sfb-split-perfect-dual-tor-window. The modules of the remaining stated proof
notions are already public imports or their public dependencies. The genuine
proof prerequisite lem-sfb-space-qcoh-kernels-colimits has no recorded declaration
and therefore has no module to import yet; it is not needed to type this statement.
The complete four-step proof is carried in the theorem docstring for stage 3.

Sources read: spaces-perfect.tex lemma-pseudo-coherent (08JL) and
lemma-ext-from-perfect-into-bounded-QCoh (09MB), and sites-cohomology.tex
lemma-perfect (08G8) and lemma-tor-amplitude (08G1). In 08JL the terms are direct
summands of finite free modules and their cohomology is quasi-coherent. In 08G8
these terms are flat, and 08G1 supplies the local tensor support bound. The finite
subcover argument of this node globalizes that local bound. No quasi-separatedness
is used for this intermediate assertion, although 09MB's later Ext statement uses it.

Edge cases checked before writing: empty X and empty finite subcover admit [0,0]
and sheaf vanishing on the empty cover; E=0 admits [0,0]; zero-rank terms are
allowed by Fin 0; a=b is permitted; arbitrary negative cohomological degrees occur;
M is arbitrary and need not be quasi-coherent or flat. Unbounded varying local
ranks and non-Noetherian/non-quasi-separated spaces are retained. The small basis
is a specified restriction equivalence, so changing the site presentation neither
adds a geometric hypothesis nor narrows the module test objects.

Searches for an existing exact statement:

- msearch.py leanfinder, query "A perfect complex on a quasi compact algebraic space
  has quasi coherent cohomology and uniform finite Tor amplitude": eight results
  on DerivedCategory cohomological bounds and K-projective complexes; none is this
  assertion for algebraic spaces.
- msearch.py loogle, query `"IsPerfect", "torAmplitude"`: zero hits.
- msearch.py grep, query
  `perfect.*(tor.?amplitude|quasi.?coherent)|finiteTorAmplitude.*perfect`: zero hits.
- rg of the same expression in WeilConjectures and Sheaf/AlgebraicGeometry finds
  scheme and relative-perfect statements and proof comments, not this theorem.
- rg for `lem-sfb-space-perfect-uniform-tor` in WeilConjectures: no hits.
- rg for site perfectness and algebraic-space compactness in Sheaf found and led
  to reuse of the exact definitions above; no second notion is introduced.

No statement dispute or source correction was found. Validation uses only the
prescribed scompile.py and deliver2.py wrappers; no live source is edited.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
