## Worker report

The module `Sheaf.CategoryTheory.InfinityFilteredCofinalPullback` states all clauses of
`lem-coef-infinity-filtered-cofinal-pullback`. The consumer has two named theorems with `sorry`:
`SSet.Presentability.infinity_filtered_cofinal_pullback` for the cospan assertion and
`SSet.Presentability.kappaCofinal_cofinal` for the independent final assertion. The prerequisite module now owns the
helpers constructing the specified equivalence-path pullback and its two projections.
Their data are actual iterated simplicial pullbacks, not selected existence witnesses.
No mathematical statement is corrected. The missing genuine prerequisite is now
stated in this delivery; its node changes only in `lean`.

Source checked: HTT, April 9, 2017, Definition the project server (printed page 439),
Lemma the project server (page 442), Lemma the project server (pages 446--447), and the cofinality
consequence of Proposition the project server. The HTT PDF was read in the sandbox scratchpad;
it is not part of the delivery. Definition the project server and both lemmas agree with the
node. The source's reduction to categorical fibrations is a proof device, so the
statement imposes no fibration hypothesis on either input functor.

Clause-by-clause rendering:

- The small universe is `u`, the containing universe is `max (u + 1) v`, as in
  `def-coef-complete-algebroid` and `def-coef-presentable-infinity-category`.
  Both cardinals have type `Cardinal.{u}`. `hκ : κ.IsRegular` and
  `hτ : τ.IsRegular` include infinitude by Mathlib's definition; `hκτ : κ < τ`
  is precisely the strict inequality. No universe equality is imposed.
- A coherent functor is a simplicial map. `[Quasicategory I]`, `[Quasicategory J]`,
  `[Quasicategory I']`, `f : I ⟶ J`, and `g : I' ⟶ J` introduce the three
  categories and the specified cospan, with no further structures.
- Weak cofinality is the existing `SSet.Enhanced.IsWeaklyCofinal`: every target
  vertex has an edge to an image vertex. It is imported, not defined a second time.
- `SSet.Presentability.IsKappaCofinal κ f` is the existing quantified test on
  every `IsKappaSmall κ L` and `SSet.Enhanced.IsContractible L`, every diagram
  `r : L ⟶ I`, and every target coherent cocone. Its conclusion is an actual edge
  from that target cocone to `CategoryTheory.Spaces.mappedCocone f r s` for a
  source cocone `s`. Thus it says exactly weak cofinality on cocone categories,
  including the coherent triangular compatibility. The same predicate is used for
  `g` and for both projections. No hypothesis that the test shape is itself a
  quasicategory is added.
- `IsKappaSmall` counts the dependent sum of nondegenerate simplices in every
  degree. `IsContractible` tests weak contractibility of realization, hence the
  groupoid completion, and does not require the original shape to be Kan.
- `hI`, `hJ`, and `hI'` render τ-filteredness with the recorded
  `IsKappaFiltered τ` predicate, testing every τ-small simplicial shape, including
  the empty shape. `hIcol`, `hJcol`, and `hI'col` render existence of all τ-small
  κ-filtered colimits using `HasTauSmallKappaFilteredColimits κ τ`.
- `hfcol` and `hgcol` render preservation of exactly that class by
  `PreservesTauSmallKappaFilteredColimits κ τ`. These predicates use the actual
  canonical postcomposition on coherent cocones, with no chosen colimit data.
  `hf` and `hg` supply precisely the required κ-cofinality hypotheses.
- `SSet.Enhanced.equivalencePullback f g` uses the existing full subcategory
  `equivalenceDiagrams Δ[1] J` with its evaluations at 0 and 1. Its vertices
  are triples `(i, i', e : f(i) ≃ g(i'))`. All parameter simplices are retained;
  the morphisms between triples are arbitrary coherent commuting pairs of arrows.
  In particular, it does not replace this category by its Kan core. Its definition
  parallels the already recorded `relativeCoconeCategory` construction for the
  general cospan in this node. The projections are the actual pullback projections.
- The first conclusion existentially supplies the quasicategory structure on the
  specified pullback model and asserts `IsKappaFiltered τ` for it. The next two
  conjuncts assert `IsKappaCofinal κ` for each specified projection separately.
- The final paragraph is the separate theorem `kappaCofinal_cofinal`. Its only
  hypotheses are an infinite regular κ, a functor between quasicategories, ordinary
  filteredness of both (`IsKappaFiltered Cardinal.aleph0`), and κ-cofinality. It
  inherits neither τ nor any colimit existence or preservation assumption from
  the cospan theorem. `E : SSet.{max (max (u + 1) v) w}` is an arbitrary target
  quasicategory in an arbitrary further universe. `uliftFunctor.{w}` transports
  the indexing categories and the functor to that common universe; it imposes no
  mathematical restriction on the target or the diagram.
- For every `H`, the actual `gluingCoconeRestrict` is an
  `IsLMEquivalenceOver` the canonical apex projections. This existing predicate
  means an equivalence with an inverse and inverse natural equivalences over the
  same base, without requiring any operadic structure. Thus restriction itself
  identifies coherent cocone categories over the same vertex category. The next
  conjunct is, for each supplied cocone `t`, the equivalence of its colimiting
  property and that of its restriction. The last equation states that the
  restricted vertex is exactly `t.1.1`, not merely an equivalent or newly chosen
  object. This also identifies the colimiting full subcategories and yields the
  stated existing-colimit consequence without assuming either colimit exists.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.CompleteAlgebroid`,
  `SSet.Enhanced.Algebroid.completeCategory`: the containing-universe convention
  of the recorded dependency is retained. No algebroid is needed as an additional
  hypothesis in this general category-theoretic result.
- `Sheaf.CategoryTheory.PresentableInfinityCategory`,
  `SSet.Presentability.IsKappaSmall`, `IsKappaFiltered`, and `PreservesColimitsIn`;
  the complete `IsPresentable` signature and surrounding definitions were read.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`,
  `SSet.Enhanced.equivalenceDiagrams`, `evaluation`, `coconeCategory`,
  `IsContractible`, `IsColimiting`, and their coherent simplicial definitions.
- `Sheaf.CategoryTheory.InfinityCofinalCommonImage`,
  `SSet.Presentability.IsKappaCofinal`, `HasTauSmallKappaFilteredColimits`,
  `PreservesTauSmallKappaFilteredColimits`, and the common-image theorem.
- `Sheaf.CategoryTheory.InfinityCofinalCosliceCalculus`,
  `SSet.Enhanced.IsWeaklyCofinal`, `coconePostcompose`,
  `relativeCoconeCategory`, and the absolute/relative coslice theorem.
- `Sheaf.CategoryTheory.InfinityCofinalCommaCriterion`,
  `SSet.Enhanced.infinity_cofinal_comma_criterion`; its public imports expose
  `gluingCoconeRestrict`, `gluingCoconeApex` from `InfinityColimitGluing` and
  `IsLMEquivalenceOver` from `LeftModuleOperadicEncoding`.
- The stated proof dependency `InfinityCosliceColimitFormula` is imported
  non-publicly. The genuine prerequisite `lem-coef-accessible-pullback-filtered-colimit`
  is now stated and imported publicly, because it owns the pullback construction
  and projections in this signature. Its proof dependency is retained.

The item gains the three already landed owners
`lem-coef-infinity-cofinal-common-image`,
`lem-coef-infinity-cofinal-coslice-calculus`, and
`lem-coef-infinity-cofinal-comma-criterion` in `stmt_deps`, because their actual
interfaces supply the cofinality, colimit-class, and canonical restriction notions
appearing in the signature. Each was already a proof dependency. The same applies
to the newly supplied accessible-pullback prerequisite. No new node or private
replacement notion is introduced.

Edge cases checked before stating the result:

- The empty test shape is included in filteredness. Thus empty input categories
  cannot satisfy the hypotheses, and the result genuinely asserts nonemptiness
  of the pullback. The empty shape is not incorrectly treated as weakly contractible
  in κ-cofinality tests.
- κ = aleph_0 is permitted with any strictly larger regular τ. Finite regular
  cardinals are excluded by the existing definition, as in HTT.
- For terminal categories and identity functors the pullback retains its expected
  equivalence data and both assertions specialize correctly.
- Distinct but equivalent base objects are retained by equivalence paths. A strict
  pullback would miss these cases; arbitrary base arrows would give the wrong
  object instead. Neither replacement is used.
- Parameter arrows in the pullback are not required to be invertible. Consequently
  the construction handles non-groupoidal filtered indexing categories.
- The final theorem works for arbitrary target quasicategories with no colimit
  completeness assumption. The explicit vertex equality handles identity maps
  and arbitrary supplied colimit cocones, not just a newly chosen representative.

Searches made with the prescribed wrapper and source readers:

- `msearch.py ... leanfinder` with query "Homotopy pullback of kappa cofinal
  functors between tau filtered infinity categories is tau filtered and projections
  are kappa cofinal": 8 hits, including ordinary `IsCardinalFiltered.wideSpan`,
  product and directed-presentation lemmas. None is the quasicategory theorem.
- `msearch.py ... loogle` with query
  `CategoryTheory.Functor.Final, CategoryTheory.IsCardinalFiltered`: 5 ordinary
  category hits (`IsCardinalFiltered.of_final`, `final_toCostructuredArrow`, and
  directed-presentation results). Their signatures require ordinary Category
  instances and do not state this coherent infinity-categorical assertion.
- `msearch.py ... leansearch` with query "Cofinality and filteredness of homotopy
  pullbacks of infinity categories": 8 hits on ordinary filtered categories,
  finite colimits, and hypercovers, with no match.
- `msearch.py ... grep` with `cofinal|filtered|pullback` restricted to
  `AlgebraicTopology/Quasicategory`: zero Mathlib source hits.
- `rg` of `WeilConjectures` for this blueprint id and κ-cofinal/filtered-cofinal
  notions: no matching declaration. `rg` of `lean/Sheaf` found the existing
  common-image and coslice predicates listed above, which were reused.
- `rg` for pullback constructions and `equivalenceDiagrams Δ[1]` in the project
  found `SourceAttachmentGluing.simplicialHomotopyPullback` (all base arrows,
  suited to Kan spaces) and `relativeCoconeCategory` (only a cocone-shaped second
  leg). Their full definitions were read. Neither is the general equivalence-path
  cospan construction required here, so the latter formula is supplied as an
  owning-node helper. No unrelated independent notion is added.
- Duplicate-name search of Mathlib, upstream `WeilConjectures`, `lean/Sheaf`,
  and `dag/lean_names_upstream.json` for `equivalencePullback`,
  `infinity_filtered_cofinal_pullback`, and `kappaCofinal_cofinal`: no hit.

Compilation is exclusively through `scompile.py`, with the default per-file limit.
The consumer still has its two postponed theorem clauses. The prerequisite has six
postponed theorem clauses, each owned by its genuine DAG node. There are no hollow
definitions or statement disputes.

## Dependency modules

`lem-coef-accessible-pullback-filtered-colimit` is delivered as
`Sheaf.CategoryTheory.AccessiblePullbackFilteredColimit`. This is the genuine existing
DAG prerequisite requested by H1 at immutable head `9e563ce6e69f`. Its `lean` and
`mathlib_match` were both absent, so there was no usable declaration to import. The
current shared node, including its recent stage-1 proof expansion, is copied unchanged
except for `lean`; its stage-1 repair note is read and its proof route is retained.
The consumer gains this id in `stmt_deps`, retains it in `proof_deps`, and imports its
module. The original three pullback helpers move to this owner without changing their
names or constructions. Consequently there is no import cycle and no second definition.

The prerequisite's statement is rendered clause by clause as follows. All categories
are `SSet.{max (u + 1) v}`, with explicit quasicategory instances; `f : A ⟶ C` and
`g : B ⟶ C` are the specified functors. No filteredness or cocompleteness of C is
silently imposed on the general mapping, colimit or slice assertions.

- `equivalencePullback` and its projections are the iterated endpoint pullbacks of
  `equivalenceDiagrams Δ[1] C`. Reassociation gives the node's product-pullback model.
  `equivalencePullbackPath` retains the whole equivalence-arrow simplex.
- `accessible_pullback_mapping` supplies its quasicategory structure and the mapping
  formula at every pair `x,y`. `pullbackComponentMaps` is the pair of fixed-endpoint
  arrow spaces in A and B. `pullbackComponentImages` applies F and G. The target
  `pullbackMappingTarget` is their pullback with `arrowSquarePathFamily` over the
  two free edges. That existing construction has triangles for `e' F(u)` and
  `G(v) e` and a path between their long edges with endpoints fixed. Its existing
  `ArrowSquareSpanPresentation` identifies it with the literal homotopy pullback
  over the cross mapping space. `right_pinch_comparison` identifies each arrow space
  naturally with the node's right-pinched mapping-space convention. The two equations
  for `j` specify its components and its whole square, via the monomorphic path-family
  inclusion. Thus it is the natural comparison, rather than merely an unrelated weak
  equivalence. The final three implications give exactly local-smallness closure.
- `accessible_pullback_colimits` quantifies over each small simplicial `K`, without
  assuming K is a quasicategory. `hA,hB` assert existence of its colimits in A and B;
  `hf,hg` assert preservation of every supplied colimiting cocone. The first conclusion
  gives existence in P, and the second is precisely the biconditional with both
  actual mapped component cocones. It applies to every supplied cocone.
- `accessible_pullback_compact` has the infinite regular κ, `hA,hB` for all small
  κ-filtered colimits, and `hf,hg` preserving exactly those shapes. Its conclusion
  includes the resulting filtered colimits in P, followed by compactness of each
  triple whenever a, b and F(a) are κ-compact. The stored equivalence identifies
  F(a) with G(b); one common-image compactness premise is sufficient. The existing
  `IsKappaCompact` definition is reused, including its containing-universe tests.
- `accessible_pullback_slices` uses `fullSourceSlice E (fun _ ↦ True) z` for the
  coherent slice E/z. The existential edge `e` is constrained to be exactly the
  stored path of x. `F,G` are the induced slice functors, constrained on their whole
  arrow coordinates. `T` is postcomposition by e, characterized by the existing
  `IsSlicePostcomposition` coherent square predicate. We use C/G(b) as the common
  slice base; postcomposition by e identifies C/F(a) with it, equivalently to the
  node's choice of C/F(a). The comparison j is a functor equivalence, with both
  component arrow-coordinate equations. For every pair of full source predicates
  PA,PB, the concluding r is its restricted equivalence and the final equation
  says that inclusion followed by j is exactly r followed by inclusion.
- `accessible_slice_locallySmall` states the independent assertion for every locally
  small ambient E and every target z, using the same small-Kan-model predicate.
- `accessible_pullback_fullSubcategories` takes arbitrary vertex predicates PA,PB,PC
  and exactly the two image-containment hypotheses hf,hg. Its F,G are the restrictions,
  with both inclusion equations. The equivalence j has all three coordinates fixed:
  both projections and the entire equivalence path. Its last three implications
  are exactly essential-smallness closure, using the existing predicate meaning
  equivalence to an actual small quasicategory. No repleteness is assumed.

Additional declarations used, with their owning modules:

- `Sheaf.CategoryTheory.ArrowMorphismSquare`: `arrowSquarePathFamily`,
  `arrowSquarePathEndpoints`, `arrowSquareRestriction`, `arrowSquareUpper`,
  `ArrowSquareSpanPresentation`, and the canonical two-triangle ambient comparison.
- `Sheaf.CategoryTheory.IsofibrationExponentiation`: `arrowMappingSpaceMap`.
- `Sheaf.CategoryTheory.RightPinchComparison`: `arrowMappingSpace`,
  `arrowMappingSpaceInclusion`, and `right_pinch_comparison`.
- `Sheaf.CategoryTheory.RelativeSliceSections`: `fullSourceSlice`,
  `fullSourceSliceArrow`, `fullSourceSliceSource`, and `IsSlicePostcomposition`.
- `Sheaf.CategoryTheory.PresentableInfinityCategory`: `IsSmall`, `IsLocallySmall`,
  `IsEssentiallySmall`, `HasSmallKappaFilteredColimits`, `IsKappaCompact`,
  `IsKappaFiltered`, and `PreservesColimitsIn`.
- `CategoryTheory.Spaces.mappedCocone` from
  `Sheaf.CategoryTheory.InfinityCategoryOfSpaces` is the actual postcomposition map.

All recorded proof-dependency modules are imported. The still unstated proof-only
`lem-coef-infinity-yoneda-presheaf-limits` has no module to import and introduces no
missing notion in these signatures. Nothing waits on it in stage 2.

Additional edge checks: an empty component category gives the expected empty pullback
without a general nonemptiness assertion; empty mapping spaces are permitted. Identity
cospans and terminal categories retain equivalence data and satisfy the formula. For
K empty the colimit theorem detects initial objects componentwise, under the stated
preservation assumptions. κ = aleph_0 is allowed. Arbitrary non-Kan small simplicial
shapes are tested. Empty full subcategories and nonreplete full subcategories are
included. Slice targets are always supplied vertices, so no object of an empty category
is invented. The local-smallness and essential-smallness conclusions distinguish small
models from cardinal bounds on the chosen large simplicial sets.

Additional searches on 2026-10-17, all through the prescribed msearch wrapper:

- LeanFinder, “Mapping spaces colimits compact objects slices full subcategories of
  homotopy pullbacks of infinity categories”: eight hits including `SSet.hasColimits`,
  `SSet.Finite.instIsFinitelyPresentable`, `DeltaGenerated.hasColimits`, and ordinary
  model-category colimit facts. These concern colimits of simplicial sets or ordinary
  categories, rather than the componentwise quasicategorical theorem.
- Loogle, `SSet.Quasicategory, CategoryTheory.IsCardinalPresentable`: zero hits.
- grep, `cofinal|filtered|compact|pullback`, under `AlgebraicTopology/Quasicategory`:
  zero hits. `rg` in the upstream WeilConjectures tree for the prerequisite id,
  `equivalencePullback`, and `accessible_pullback_filtered` also gives no declaration.
- LeanSearch, “Mapping spaces and componentwise colimits in a homotopy fiber product
  of infinity categories”: eight hits, including `CategoryTheory.pi` componentwise
  cocone statements and ordinary product/Fubini statements. Their signatures concern
  ordinary Category instances and do not state the homotopy fiber-product assertion.
- Project source search found the existing arrow-square path model, fixed-target
  slices and presentability predicates above. Their full signatures and docstrings
  were read and reused; no new independent notion or definition node is needed.

## Second reading by Q98

This is the worker's self-check, not the maintainer's independent review. The initial
saved-packet dry run passed mechanically, but its report explicitly omitted the genuine
prerequisite, so it did not resolve returned H1. The repair adds that prerequisite in
full, checks every clause above, retains the consumer's statement and its two theorem
signatures, and removes its ownership of the moved helpers. The dependency's natural
statement and proof plan are unchanged. All eight theorem proofs are exactly `sorry`;
all ten helper constructions contain real data. Explicit binders, 100-column lines,
source/blueprint docstrings, module ownership, and verbatim primary signatures were
checked. Both files are compiled separately in dependency order through scompile.py.
The sole universe-linter suppression is scoped to the size-free slice theorem, whose
two universe parameters intentionally occur only as the containing `max (u + 1) v`.
