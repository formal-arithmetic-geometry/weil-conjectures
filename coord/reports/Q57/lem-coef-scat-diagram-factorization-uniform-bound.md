## Worker report

The module `Sheaf.CategoryTheory.ScatDiagramFactorizationUniformBound` states
`SSet.Bergner.UniformFactorization.scat_diagram_factorization_uniform_bound`.
It has one postponed theorem, with proof `sorry`, and explicit data definitions. No source,
library or shared repository file was modified. The module's docstring gives the source;
the theorem's docstring carries all eleven proof steps and the least-bound justification.

Clause-by-clause reading:

- The original universe is `u`; `D : Type u` and `[SmallCategory D]` express precisely
  an ordinary category with small objects and morphisms. There is no nonemptiness hypothesis.
- Simplicial categories are the landed `CategoryTheory.CoherentNerve.SCat`, with its
  enriched-functor category instance; neither the object carrier nor its Hom notion is copied.
- Ambient universes are `max u v` and `max u v w`. The variables `v,w` are arbitrary,
  and either may equal `u` or each other. This includes equal universes without a strict
  inequality assumption.
- The cardinal delta is `bound D : Cardinal.{u}`. Its actual construction is the infimum
  of the set `generatorBounds D` of regular ranks bounding the indices and full endpoint
  data of base generating families. These families generate the two left classes by
  `ofHoms(...).rlp.llp`. This realizes the choice in proof steps 2--3 by the least suitable
  base rank. It does not choose an arbitrary object from a sorry existence assertion.
  Crucially, `bound` has only the original-universe parameter: the same expression occurs
  for every choice of `v,w`. Placing an existential cardinal separately inside each
  ambient-universe instance would fail to express this uniformity.
- `Fact (bound D).IsRegular` asserts regularity, including infinitude by Mathlib's
  `Cardinal.IsRegular` definition. No regularity or generation condition is a hypothesis
  of the theorem. Nonemptiness of `generatorBounds` is part of its documented proof.
- Objectwise cofibrations are `(I.rlp.llp).functorCategory D`, using the actual Bergner
  boundary and empty-object generators from interval lifting. Objectwise trivial
  cofibrations are `(I.rlp.llp ⊓ dwyerKanEquivalences).functorCategory D`.
  The Bergner class identification is proof step 1, not an additional assumption.
- `Factorizations.cofibration` is Mathlib `FunctorialFactorizationData` for the first
  left class and its `.rlp`; `.fibration` is the same record for the second left class
  and its `.rlp`. The injective model dependency identifies these right orthogonals
  with injective trivial fibrations and injective fibrations respectively.
- For each input arrow, the record's `Z`, `i`, `p`, `fac`, `hi`, `hp` give exactly the
  two intermediate objects, both factor maps, the composite equal to the input, and
  the four specified class memberships. The functor `Z` acts on commuting squares;
  its identity/composition laws and naturality of `i,p` express all functoriality clauses.
- `PreservesFiltered` quantifies over *every* `J : Type (max u v)` with `SmallCategory J`
  and `IsCardinalFiltered J (bound D)`, and asserts `PreservesColimitsOfShape J` for
  both `Z` functors. Mathlib's filteredness definition counts `Arrow A`, as in the
  node's fewer-than-delta-morphisms convention, with no restriction to directed posets.
  Diagram and arrow colimits are the ordinary pointwise colimits. There is no assumption
  that transition maps are monomorphisms. The same clause is repeated for the larger ambient.
- `inclusion` explicitly lifts object types and all simplices with `ULift` and
  `SSet.uliftFunctor`, retaining the actual identity and composition operations.
  `diagramInclusion` postcomposes with this fixed functor. This construction generalizes
  the dependency's `liftBundle`, whose larger universe is tied to its object universe
  and cannot itself enlarge an already-small bundled `SCat` arbitrarily.
- Each `Compatible.iso` is an isomorphism `F.Z ⋙ ι ≅ ι.mapArrow ⋙ G.Z`, so is natural
  in the input arrow. Its `left` and `right` equations impose compatibility with both
  factor maps. The theorem supplies this for `e=c` and `e=f` using the same `F,G`.
  No arbitrary inclusion or comparison is assumed.
- `D` may be empty or the terminal category. In the latter case these are precisely
  the Bergner factorizations in its one value. No locally Kan, cofibrant, skeletal,
  countable, or finite-diagram restriction was added.

Dependency declarations read and used:

- `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`:
  `SSet.Bergner.I`, `SSet.Bergner.simplicial_interval_lifting`, and its full definitions
  of `SCat`, the fixed-object structures, boundary/horn/interval generators and lifting classes.
- `Sheaf.AlgebraicTopology.SimplicialIntervalCellStability`:
  `SSet.Bergner.dwyerKanEquivalences`, `simplicial_interval_cell_stability`.
- `Sheaf.CategoryTheory.SimplicialLocalizationComparisonCalculus`:
  `CategoryTheory.SimplicialLocalizationCalculus.simplicial_localization_comparison_calculus`
  and `liftBundle`; its `BergnerModelData` is the existing model structure interface.
- `Sheaf.CategoryTheory.CombinatorialInjectiveDiagramModel`:
  `HomotopicalAlgebra.combinatorial_injective_diagram_model`, including its equations
  characterizing both objectwise classes and the right lifting class.
- Mathlib `MorphismProperty.FunctorialFactorizationData`, `IsCardinalFiltered`,
  `PreservesColimitsOfShape`, `Cardinal.IsRegular`, `HasCardinalLT`, `sInf`,
  `Functor.whiskeringRight`, `Functor.mapArrow`.

Proof imports include all published proof dependencies: finite-limit-model presentability,
Kan--Quillen (already public via the statement dependencies), lifting-class closure,
transfinite lifting, regular cardinal bounds, colimit Fubini, filtered-colimit elementwise
comparisons, filtered-colimit/finite-limit commutation, and transfinite recursion
(the latter regular-bound and recursion declarations are available transitively).
`lem-coef-scat-injective-universe-generators` has no published Lean record to import;
its natural-language statement is explicitly cited in the proof docstring. It is a proof
input, not an assumption or missing notion required to type this theorem.

Edge cases checked: empty and terminal D; equal ambient universes; arbitrary larger
ambient universes; the empty cardinal-bound set has defined infimum zero but the conclusion
asserts regularity, so it cannot silently supply a vacuous bound; empty generator indices
and n=0 are included by the dependency's `I`; arbitrary noninjective filtered transitions;
empty test diagrams in the definition of cardinal-filteredness. `Compatible` keeps the
natural isomorphism in the stated direction and both triangle equations.

Searches before writing:

- msearch LeanFinder: "functorial injective weak factorization system simplicial categories
  filtered colimits" returned generic small-object factorization records/theorems and
  simplex-category factorizations, none with the statement's uniform Bergner bound.
- msearch Loogle: "ModelCategory, FunLike, PreservesColimit, IsRegular" returned no hits
  (ModelCategory was not a recognized search identifier). Earlier recorded query
  "FunctorialFactorizationData, PreservesColimitsOfShape" returned no exact result.
- msearch LeanSearch: "Functorial injective diagram factorizations simplicial categories
  uniform filtered colimit bound" returned set-level filtered colimit and ordinary
  surjective/injective factorization results, no exact match.
- msearch grep `Bergner|uniform.*[Ff]actori|[Ff]actori.*uniform` in CategoryTheory:
  no Mathlib hits. Direct Mathlib reads found and reused the generic factorization,
  cardinal-filteredness and preservation records.
- rg in upstream WeilConjectures and side lean/Sheaf for the uniform-factorization names
  and phrases: no existing statement. The node-id grep upstream returned no match.
  The side common-chunk module mentions the node only as a future proof input.
- Direct source reads found `SCat`, `dwyerKanEquivalences`, and the smaller `liftBundle`;
  these were checked by signature and used, or generalized only for the extra lift size.

The node statement and dependency list are unchanged. No statement dispute or dependency
repair is needed. All universes and variables are explicitly bound, with autoImplicit false.

Validation: file-only compile through the required scompile wrapper; maintainer preflight
through deliver2 --no-push. The only postponed declaration is the named theorem above.

## Second reading by Q57

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
