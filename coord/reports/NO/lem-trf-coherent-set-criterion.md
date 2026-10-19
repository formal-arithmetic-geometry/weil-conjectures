## Worker report

`Sheaf.Paper.CoherentSetCriterion` states
`AlgebraicGeometry.coherent_iff_finite_constructible_strata`, with its proof `sorry`.
It also constructs the canonical set inverse image `orientedStratumSetRestriction`
and supplies Mathlib's existing sheafified-presheaf coproduct instance directly.
Every variable and universe is explicitly bound; definitions contain real data.
The theorem docstring carries the three steps of the node's proof and their dependencies.

Hypothesis and conclusion correspondence:

- The schemes and morphism are `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Noetherian S is exactly `[IsLocallyNoetherian S] [CompactSpace S]`.
- Finite presentation is exactly `[LocallyOfFinitePresentation f] [QuasiCompact f]
  [QuasiSeparated f]`, as `def-weil-pbc-scheme-conventions` specifies. No separatedness
  or nonemptiness assumption is added.
- The given sheaf is `(A : OrientedNearbyCycles.VanishingTopos.{u, v} f)`, the exact
  recorded vanishing topos, with set values in `Type (max (u + 1) v)`.
- Coherence is the existing `IsCoherentObject.{max (u + 1) v} A`, and the conclusion
  is an equivalence `↔`, giving both directions of the node.
- The two finite locally closed stratifications are
  `SX : Scheme.FiniteLocallyClosedStratification X` and the analogous `SS` for S.
  Their existing fields give finite indexing, locally closed strata, disjointness,
  exhaustive coverage, stratum schemes, and their immersions.
- Both constructibility clauses are written separately as
  `∀ i : Fin SX.n, Topology.IsConstructible (SX.stratum i)` and its S analogue.
- Every pair is quantified by `(i : Fin SX.n) (j : Fin SS.n)`.
  Its topos is `Sheaf (productTopology (SX.immersion i ≫ f)
  (SS.immersion j ≫ 𝟙 S)) (Type (max (u + 1) v))`.
  Thus both actual stratum schemes occur and the common base remains S.
- The restricted sheaf is `(orientedStratumSetRestriction f (SX.immersion i)
  (SS.immersion j)).obj A`. This is an explicit construction: forget A to its
  presheaf, precompose with the published `vanishingNormalization f`, apply left
  Kan extension along the opposite of the published `stratumBaseChange`, and
  sheafify on the stratum-product topology. These functors implement exactly the
  inverse image specified by the projections, immersions and orientation in ILO
  XI 1.6/1.9. In particular no arbitrary geometric morphism is quantified over.
- Local constancy with finite values is written out rather than introducing another
  predicate: for every site object U, `∃ R : Sieve U, R ∈ J U ∧ ...`; for each
  `r : V ⟶ U` in R there is `(M : Type (max (u + 1) v))` with `Finite M` and a
  `Nonempty` sheaf isomorphism between the restricted sheaf `.over V` and
  `((constantSheaf J (Type (max (u + 1) v))).obj M).over V`.
  This is Stacks Modules on Sites Definition 093Q, read at
  `sites-modules.tex`, lines 8414–8431. It is equivalent to the node's family covering
  the terminal topos object: associated representables generate, refine every
  epimorphic family, and their slices are the localized sites `J.over V`.
  Conversely, collect the representable trivializing charts to cover the terminal
  object. Constant sheaves pull back to constant sheaves (093R). Requiring models
  over every arrow of a covering sieve is equivalent to requiring models on a
  covering family, since the property is preserved by restriction.
  The isomorphism is in the slice sheaf category, rather than an isomorphism of
  underlying objects that could forget the map to the slice object.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`;
  `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; the convention node specifies its conjunction
  with `QuasiCompact` and `QuasiSeparated`.
- `Sheaf.Paper.OrientedNearbyCycles`: `VanishingTopos`, `vanishingTopology`.
- `Sheaf.CategoryTheory.Sites.CoherentTopos`: `IsCoherentObject`, with its exact
  coproduct universe fixed to the universe of sheaf values.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`; `Mathlib.Topology.Constructible`:
  `Topology.IsConstructible`.
- `Sheaf.CategoryTheory.Sites.OrientedProductLargeSites`: the oriented-product
  triple/site construction and universal property (imported through the definition
  module). Its concrete specialization is `ProductSite`, `productTopology`, and
  `stratumBaseChange` in `Sheaf.Paper.OrientedConstructibleSheaf`.
- The current recorded dependency `def-trf-oriented-constructible-sheaf` points to
  `Sheaf.Paper.OrientedConstructibleSheafVanishing`, which publicly imports that
  general definition and defines `vanishingNormalization`. The delivery imports
  the recorded module and adds this already landed node to `stmt_deps`, to cite
  the canonical site functors it uses. No dependency interface is changed.
- `Mathlib.CategoryTheory.Sites.Over`: `Sheaf.over`; the constant set models use
  Mathlib's `constantSheaf` from the imported site framework.

Already stated proof dependencies are imported without `public`: the finitary site
coherent-generator theorem, coherent-conservative reflection, qcqs triple presentation,
étale stratified finiteness, and finite étale representability in
`WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale`. The two proof-only DAG
helpers about finite locally constant operations and the stratified cover currently
have no Lean record; this statement introduces no reference to an unstated declaration
of either. Their erroneous saved candidate modules are retained in the scratch archive
and excluded from the delivery. They are not statement prerequisites: the local-constancy
condition is explicitly written out in this theorem.

Edge cases checked: `X = ∅` allows `SX.n = 0`; empty strata and empty product topoi
are allowed; the slice isomorphism admits `M = ∅`; no member of a covering family is
required individually epimorphic. In the degenerate topos an empty covering sieve
makes the local condition vacuous, as it should. For a nondegenerate point topos an
infinite constant set cannot satisfy the finite local models. The auxiliary universe
v is independent of u, and every site and set is placed in their common containing
universe, so no site universe equality or additional smallness assumption is imposed.

Searches retained from the saved packet and repeated against current sources:

- `msearch.py leanfinder`, query “A sheaf of sets on a vanishing topos is coherent
  exactly when finite locally constant on products of constructible strata”: eight
  condensed/locally constant sheaf hits, no exact statement.
- `msearch.py loogle`, query `CategoryTheory.Sheaf, CategoryTheory.Over`: twelve hits,
  including `Sheaf.over` and `GrothendieckTopology.overPullback`. Their source
  signatures and docstrings identify the Mathlib slice API used here.
- `msearch.py grep`, query
  `IsFiniteLocallyConstant|oriented.*strat|coherent.*constructible`: zero Mathlib hits.
- `rg` over upstream `WeilConjectures` and project `lean/Sheaf` for the theorem and
  helper names: no declarations already have these names. A direct upstream search
  for the item ID returns no matches. General constructible-module predicates exist,
  but do not state this equivalence for set sheaves on the vanishing topos.
- Project source reading found and reused `stratumBaseChange` and
  `vanishingNormalization`; `scompile.py --source` confirmed the latter against
  the current published sources. The final file does not duplicate either.

Validation: `scompile.py NO lem-trf-coherent-set-criterion
lean/Sheaf/Paper/CoherentSetCriterion.lean` passes with exit 0 and no warnings;
the final module compiled in 2.6 seconds. The primary `lean.statement` is extracted
verbatim from the file before `:=`, as the server preflight requires. No informal statement correction was needed.

## Self-check by NO

The saved packet's RHS ignored the S stratum, quantified an unconstrained morphism,
and did not give a slice isomorphism over its chart. Its unused helper candidates
also asserted unrelated or vacuous propositions. Those saved files are archived
under scratch; none is delivered. The repaired RHS uses both strata, the concrete
canonical inverse image, finite constant sheaf models, and actual slice sheaf
isomorphisms. I reread each hypothesis and clause against the node and source
interfaces as matched above. The independent mathematical review remains with the
maintainer, as required by the dispatcher brief.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
