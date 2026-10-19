## Worker report

The module `Sheaf.CategoryTheory.InfinityCompactApproximation` states
`SSet.Presentability.infinity_compact_approximation` with a single `sorry` proof.
Its only helper, `compactSourceInclusion`, is the actual inclusion of the already defined
full compact-source subcomplex in the coherent slice; its data is the subcomplex inclusion,
with no choice or postponed construction. No statement correction, new node, or dependency
repair is needed. The already landed `lem-coef-accessible-compact-slice-density`, previously
a proof dependency, is added to `stmt_deps` because its canonical constructions occur in
the signature.

Hypotheses and clauses, in node order:

- The smaller universe is `u`, and every category is in `max (u + 1) v`, with arbitrary
  ambient `v`. This follows the recorded complete-algebroid and presentability conventions.
- Finite families are `V : Type w`, `E : Type z`, `[Finite V]`, `[Finite E]`; the source and
  target functions `s t : E → V` specify the directed incidence data. Independent `w` and
  `z` do not impose a size restriction on a finite family. No nonemptiness is assumed.
- The categories are `C : V → SSet`, with `[hC : ∀ a, Quasicategory (C a)]`.
  `haccessible` is exactly `∀ a, IsAccessible.{u, v} (C a)`.
- `F e : C (s e) ⟶ C (t e)` is the actual coherent functor. `hF` expands the stated
  accessibility convention as an existential small regular `ρ` followed by
  `PreservesColimitsIn`, restricted by `IsSmall.{u}` and `IsKappaFiltered ρ`.
  It imposes no compact-object preservation as a hypothesis.
- The conclusion starts `∃ κ τ : Cardinal.{u}`. `κ.IsRegular`, `τ.IsRegular` include
  infinitude (Mathlib); `κ < τ` and `Cardinal.aleph0 < τ` express the two strict inequalities.
- For each vertex, the first universal clause asserts `IsLocallySmall.{u}`,
  `IsKappaAccessible` at both ranks, and `IsEssentiallySmall.{u}` for the recorded
  `compactObjects τ` full subcomplex. Essential smallness means equivalence to a small
  quasicategory, not literal smallness of the chosen model.
- For each edge, the next clause gives the two filtered-colimit preservation assertions
  using `PreservesColimitsIn`, and sends every `IsKappaCompact` vertex at `τ` to a
  `τ`-compact image under the given `F e`.
- For every `a` and `c`, `compactSourceSlice τ c` is the recorded full coherent slice
  on compact sources. It retains all the higher simplices of the coherent comma model.
  The conclusion gives essential smallness and a quasicategory witness with
  `IsKappaFiltered τ`.
- The source projection is precisely the recorded `compactSourceProjection τ c`.
  Existence of `q` with `IsTautologicalCocone τ c q` and `IsColimiting ... q` specifies its
  canonical colimit: the former pins both its vertex to `c` and its full coherent
  transformation to the arrows of the slice. This uses exactly the density node's
  convention for colimits over essentially small indexing categories.
- `HasTauSmallKappaFilteredColimits κ τ` asserts existence of all the required colimits
  in the slice. `PreservesTauSmallKappaFilteredColimits κ τ (compactSourceInclusion τ c)`
  states that they are computed in the ambient coherent slice. Because this is the full
  subcategory inclusion, it also reflects the colimiting property.
- The final clause gives an induced simplicial map `G` on compact-source slices. Its
  degree-`n` formula specifies the complete underlying pair: apply `F e` to the source
  simplex and apply `(ihom Δ[1]).map ((ihom Δ[0]).map (F e))` to its entire structure arrow.
  This holds for every simplex, not only vertices or homotopy classes; it determines `G`
  uniquely after forgetting subtype proofs. Thus the existential map is the canonical
  restriction of postcomposition, and no arbitrary comparison is admitted.
- `PreservesTauSmallKappaFilteredColimits κ τ G` and `IsKappaCofinal κ G` are the requested
  preservation and cofinality statements, using the published definitions unchanged.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CompleteAlgebroid`: `SSet.Enhanced.Algebroid.completeCategory`
  and the documented small/containing-universe convention. No algebroid data is required
  in this theorem, whose categories are arbitrary quasicategories.
- `Sheaf.CategoryTheory.PresentableInfinityCategory`: `SSet.Presentability.IsAccessible`,
  `IsKappaAccessible`, `IsLocallySmall`, `IsKappaCompact`, `IsEssentiallySmall`, `IsSmall`,
  `IsKappaFiltered`, and `PreservesColimitsIn`. Their signatures and definitions were read.
- `Sheaf.CategoryTheory.InfinityFilteredCofinalPullback`, with its public imports
  `InfinityCofinalCommonImage` and `InfinityCofinalCosliceCalculus`: `IsKappaCofinal`,
  `HasTauSmallKappaFilteredColimits`, `PreservesTauSmallKappaFilteredColimits`.
  Cofinality tests all κ-small weakly contractible simplicial boundaries and uses actual
  edges between coherent cocones, in the direction target-to-image.
- `Sheaf.CategoryTheory.AccessibleCompactSliceDensity`: `compactObjects`,
  `compactSourceSlice`, `compactSourceApex`, `compactSourceProjection`,
  `IsTautologicalCocone`, and `accessible_compact_slice_density`. This is the existing
  coherent slice construction, not an ordinary comma category or a private replacement.
- The module also imports every currently recorded proof dependency with a Lean module:
  `AccessibleCompactCocones`, `AccessibleInfinityRankCalculus`, `CompactSmallColimits`,
  `InfinityCommonCompactnessRank`, `InfinityJoinConeCalculus`, `InfinityYonedaPresheafLimits`,
  and `SpaceTransportClassification`. The proof dependency
  `lem-coef-spaces-small-colimits-universe` has no recorded module in the read snapshot;
  it supplies no term needed to state this item, so there is no import for it.

Edge cases checked before drafting: either or both finite families may be empty; there is
no `Nonempty` or `Fintype` assumption. An empty accessible category has no vertices, so its
object-indexed clauses are vacuous. A terminal category and identity functors are admitted.
A constant accessible functor must satisfy the actual preservation hypothesis, and its
compact-object preservation is concluded only after the common rank is chosen. The first
rank may be countable; only τ must be uncountable. A κ-filtered shape cannot be empty,
since its definition tests the empty boundary; arbitrary boundaries in the cofinality test
are not incorrectly required to be quasicategories. The slice functor's formula handles
all degeneracies and every higher compatibility. No equality of ambient and small
universes is imposed.

Searches (2026-10-17):

- `msearch.py ... leanfinder "Uniform compact approximation slices of accessible infinity
  category functors are filtered and cofinal"`: eight hits, including ordinary
  `CategoryTheory.Functor.IsCardinalAccessible` and ordinary compact comma density; no
  quasicategorical theorem.
- `msearch.py ... loogle '"IsCardinalAccessible"'`: twelve hits, all ordinary-category
  accessible functors and their preservation properties. Read Mathlib's
  `CategoryTheory/Presentable/Basic.lean` and `AlgebraicTopology/Quasicategory/Basic.lean`;
  the ordinary theorem does not give this coherent mapping-space statement.
- `msearch.py ... leansearch "compact approximation slices accessible infinity categories"`:
  eight hits on ordinary accessible categories, condensed limits, and compact spaces;
  no exact match.
- `msearch.py ... grep '[Cc]ompact|[Aa]ccessible|[Cc]ofinal'
  AlgebraicTopology/Quasicategory`: zero hits.
- `rg` in the upstream `WeilConjectures` tree for compact approximation,
  `CompactApproximation`, and `IsAccessibleFunctor`, and `grep -rn` for this node id:
  no matches. Exact proposed declaration-name search there and in
  `dag/lean_names_upstream.json` also returned no match.
- `rg` in `lean/Sheaf/CategoryTheory` for compact sources and accessible/filtered
  preservation found the published compact-source density and cofinality interfaces,
  which are used. It also found `PreservesKappaFiltered` in
  `SmallRightAdjointDiagramCompactModel` and `IsAccessibleFunctor` in
  `OperadicAlgebraPresentability`; the theorem expands the common `PreservesColimitsIn`
  definition instead of adding another definition or importing these unrelated consumers.
  Exact-name searches for the new theorem and inclusion returned no matches.

Source checked online: https://www.math.ias.edu/~lurie/papers/HTT.pdf, printed pages
443–444 (Lemma the project server) and 447–448 (cardinal choice in Proposition the project server).
The source PDF's proof of the project server prints τ-small where the κ-cofinality test uses κ-small;
the node already makes the required κ-small test explicit. This is not a change to the node.
The theorem docstring carries each of the seven DAG proof steps.

## Second reading by Q12

Replaced at maintainer review (delivery-errors H11): the delivered section was an author
self-check. This reading was done with the node, the module and every dependency module open
(side clone da93d6405).

Node objects, hypotheses and clauses, with the Lean and the verdict:

- Universes: small `u`, categories in `SSet.{max (u + 1) v}`, as in `IsAccessible.{u, v}` of
  def-coef-presentable-infinity-category. Finite families `V : Type w`, `E : Type z`,
  `[Finite V] [Finite E]`, incidence `s t : E → V`. No nonemptiness. Correct.
- Accessible categories: `[Quasicategory (C a)]` and `IsAccessible.{u, v} (C a)`. Correct.
- Accessible functors: `F e : C (s e) ⟶ C (t e)` and `hF`: some `ρ : Cardinal.{u}`,
  `ρ.IsRegular` (infinite in Mathlib) with `PreservesColimitsIn` over small (`IsSmall.{u}`)
  `ρ`-filtered quasicategory shapes. This is the node's definition of accessible functor,
  with the shape test as in `HasSmallKappaFilteredColimits`. No compactness hypothesis. Correct.
- `∃ κ τ : Cardinal.{u}`, both regular, `κ < τ`, `aleph0 < τ`. Correct.
- Per vertex: `IsLocallySmall.{u}`, `IsKappaAccessible` at `κ` and `τ`,
  `IsEssentiallySmall.{u} (compactObjects τ).toSSet`; `compactObjects` is the replete full
  subcomplex on `IsKappaCompact τ`. Correct.
- Per edge: preservation of small `κ`- and `τ`-filtered colimits (same predicate as the
  hypothesis); `IsKappaCompact τ d → IsKappaCompact τ ((F e).app _ d)`. Correct.
- `K_v(c)`: `compactSourceSlice τ c`, the full subcomplex of `coneCategory (const c)`. That is
  `commaSubcomplex … true`, endpoint 0 the constant diagram at the source and endpoint 1 the
  constant diagram at `c`: arrows into `c`, with all higher simplices. Essentially small; a
  quasicategory witness with `IsKappaFiltered τ`; a cocone `q` on `compactSourceProjection τ c`
  with `IsTautologicalCocone` (apex `c` and the whole coherent transformation given by the
  slice arrows) and `IsColimiting`. These have the form of the conclusion of
  `accessible_compact_slice_density`. Correct.
- "admits all τ-small κ-filtered colimits, computed in C_v/c":
  `HasTauSmallKappaFilteredColimits κ τ` of the slice and
  `PreservesTauSmallKappaFilteredColimits κ τ (compactSourceInclusion τ c)`, where the
  inclusion is the actual `.ι` of the full subcomplex into `coneCategory (const c)`. Correct.
- Induced functor: `∃ G` between the slices over `c` and over `(F e).app _ c`, normalized in
  every degree. The underlying pair is `(F e)` on the source simplex and
  `(ihom Δ[1]).map ((ihom Δ[0]).map (F e))` on the structure arrow, the same formula as
  `coconePostcompose`. It determines `G`, so this is the node's `(d → c) ↦ (F d → F c)`, not an
  arbitrary map. `PreservesTauSmallKappaFilteredColimits κ τ G` and `IsKappaCofinal κ G`
  (κ-small, weakly contractible test shapes; an edge from each target cocone to an image
  cocone) match the definition in lem-coef-infinity-filtered-cofinal-pullback. Correct.

Edge cases: empty `V` or `E` (the clauses are vacuous; κ and τ exist); an empty category;
identity and constant functors; `κ = aleph0` allowed, only `τ` uncountable. There is no
universe equality or extra instance. The empty test shape is included in `IsKappaFiltered`.

Searches: `rg compactSourceInclusion|infinity_compact_approximation` over the side lean tree
gives no hits, so the names are new. The worker's searches were re-read (Mathlib's
`IsCardinalAccessibleCategory.uniformization` and `Presentable/Dense` concern ordinary
categories), so no existing declaration states this. The helper is real data (a subcomplex
inclusion) with a source and blueprint docstring.

Mismatches: none in the Lean. Only this section was changed.

## Validation

The single-file compile and required delivery preflight are run through the prescribed
`scompile.py` and `deliver2.py` wrappers. The shared repository and upstream source trees
were only read; all authored files are in the item sandbox.

`scompile.py Q12 lem-coef-infinity-compact-approximation` passed with exit 0 and no
errors or warnings. The server checked the sandbox identity (7.5 s) and library module
identity (9.8 s), each under the 60-second per-file limit.

Maintainer review re-compile: nt_compile.py --json on the delivered module gave exit 0,
no errors and no warnings (5.5 s).
