## Worker report

The module `Sheaf.CategoryTheory.InfinityMonadicComparison` states
`SSet.Enhanced.infinity_monadic_comparison`, with `sorry` as its entire proof.
It constructs the canonical free-object comparison from the supplied coherent
adjunctions and coherent natural equivalence. Its other declarations unpack
conservativity and existence/preservation of geometric realizations. These are
helpers of the assigned comparison criterion, not new axioms or alternative
models of infinity categories. No statement correction and no new DAG node.

The source was read at Higher Algebra (2017), Corollary the project server and Remark
the project server, printed pp. 689–690:
https://www.math.harvard.edu/~lurie/papers/HA.pdf . In the source notation,
`U, G, G', F, F'` are our `H, U, V, F, G`. The node assumes existence and
preservation of all geometric realizations, which implies the source's
split-simplicial conditions, and assumes both forgetful functors conservative.
The current blueprint proof of `prop-coef-integral-exceptional-adjoint`,
paragraph 2, was read: the item supplies infrastructure for the middle coherent
finite-coefficient mapping-complex adjunction. It is not the unit's own statement.

Hypothesis and conclusion correspondence:

- Infinity categories C, E, B: `{C E B : SSet.{v}}` and the three
  `[Quasicategory ...]` instances. The simplicial-set and mapping-space conventions
  are the published ones imported through `CompleteAlgebroid`. The fixed shape
  Δᵒᵖ is countable, so its smallness is independent of the choice of containing
  ambient universe. No local-smallness or presentability assumption is added.
- Functors U, V, H: the three displayed simplicial maps, with the node's domains
  and codomains. These act on all simplices, not only objects and arrows.
- U and V conservative: `hU` and `hV`, each `ReflectsEquivalenceEdges`, explicitly
  quantify over every source edge and reflect the published equivalence predicate.
- Supplied coherent VH ≃ U: `eta`, `eta_src`, `eta_tgt`, `heta` are an equivalence
  edge of the entire internal functor simplicial set from U to VH. This is the
  inverse orientation of the displayed equivalence VH ≃ U and exactly the
  orientation used in the node's adjunct formula UFb → VHFb. It changes no data
  or hypothesis, since coherent equivalences have coherent inverses.
- Every small geometric realization exists in C and E: `hC`, `hE` use
  `HasGeometricRealizations`, quantifying over every coherent diagram from
  `nerve (AsSmall.{v} SimplexCategoryᵒᵖ)` and requiring an actual colimiting
  cocone in `coconeCategory`. Resizing this ordinary countable index category
  makes no restriction on the diagrams. No colimits in B are required.
- U and V preserve these realizations: `hUr`, `hVr` use
  `PreservesGeometricRealizations`, which sends each colimiting coherent cocone
  to its actual image `Spaces.mappedCocone` and requires that image colimiting.
  It does not merely assert that two independently selected apexes are equivalent.
- The two left adjoints and coherent adjunctions: F, G and
  `aF : CoherentAdjunction F U`, `aG : CoherentAdjunction G V`. This is the
  published structure with coherent unit/counit edges, triangle simplices and
  universal comma objects, expressing the natural mapping-space equivalences.
  None of the model-category hypotheses of the theorem owning that structure
  occur in this statement.
- First unit e: exactly `aF.unitEdge`, with the supplied endpoint equations.
- Alpha is the specified adjunct, not a freely chosen map: the definition
  `freeAdjunctionComparison` is the composite of G applied to e, G applied to
  eta whiskered by F, and the G–V counit whiskered by FH. Thus its b-component
  is ε_(HFb) composed with G(eta_(Fb)) composed with G(e_b), the adjunct of the
  specified b → UFb → VHFb. All three edges come from coherent transformations. Their composite is
  taken in the homotopy category of E and is the class of the corresponding
  coherent adjunct component. This chooses neither a comparison nor a filler.
- V(alpha_b) is an equivalence for every b: `hfree` takes that canonical
  component class at b and postcomposes with V, then asks `IsIso`. In a quasicategory an
  edge is an equivalence precisely when its class in its homotopy category is
  invertible. Consequently this test depends only on the canonical class and
  is exactly the node's hypothesis. It does not replace adjunction mapping
  spaces, naturality, or cocones by their homotopy categories. Applying the
  supplied eta identifies the target VHFb with UFb as in the node's formula.
- Conclusion H is an infinity-category equivalence: `IsFunctorEquivalence H`
  supplies a simplicial quasi-inverse and coherent natural inverse equivalences.

Dependencies reused:

- `Sheaf.CategoryTheory.CompleteAlgebroid`, recorded declaration
  `SSet.Enhanced.Algebroid.completeCategory`, supplies the node's conventions
  through its published imports, especially `EnhancedDiagramsCones`,
  `PresentableInfinityCategory` and `InfinityCategoryOfSpaces`.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `IsEquivalenceEdge`,
  `diagramVertex`, `evaluation`, `coconeCategory`, `IsColimiting`, and
  `IsFunctorEquivalence` are the exact published definitions.
- `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`:
  `CategoryTheory.Spaces.mappedCocone` supplies actual cocone postcomposition.
- `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`:
  `HomotopicalAlgebra.ModelInfinity.CoherentAdjunction`, `diagramObject`,
  `edgeClass` (the latter two were inspected; the final component formula only
  uses `CoherentAdjunction`). Its already-landed node
  `lem-coef-model-infinity-derived-adjunction` is added to `stmt_deps` to cite
  this existing structure explicitly. Its complete structure and docstring were
  read; its theorem's additional hypotheses are not used or imported as binders.
- Mathlib `SSet.hoFunctor`, `SSet.Edge`, the homotopy category's `homMk` and
  composition perform the literal canonical component composite; `Cat.Hom.toFunctor` maps those arrows.
- Stated proof dependencies are imported without `public`:
  `EnhancedFunctorConeCalculus.enhanced_functor_cone_calculus` and
  `InfinityFullEssentialImage.fullyFaithful_fullEssentialImage` (with their
  namespace `SSet.Enhanced`). Their declarations and docstrings were read.
  `def-cbc-enhanced-diagrams-cones` is already imported transitively/publicly.
  At drafting time the proof-only nodes
  `lem-coef-infinity-yoneda-presheaf-limits` and
  `lem-coef-adjunction-free-simplicial-resolution` have no Lean records; no
  fictitious imports were added. The full six-step node proof is in the theorem
  docstring, including those dependencies.

Edge cases checked before drafting:

- Empty categories: the predicates do not require vertices or chosen apexes
  where no diagrams exist. If B is empty, the supplied U and V force C and E
  empty; the equivalence conclusion remains valid. If C is empty but B is not,
  an adjoint F cannot exist, so no false special case is admitted.
- Identity adjunctions and H the identity: the mate is the canonical composite
  of identity unit/counit and eta, hence gives the expected equivalence test.
- No hypothesis that B has geometric realizations was introduced; preservation
  requires only the image cocones of diagrams whose source has a realization.
- No arbitrary chosen alpha, arbitrary realization, nonempty hypothesis, compact
  generation, monadicity assumption, or all-colimits assumption was added.
- The free-object test is not vacuous for an inhabited B, and the conservativity
  and realization predicates are substantive, not universally true binders.
- Ambient universe v is arbitrary; the countable index Δ fits every such
  universe. Enlarging an ambient category changes no allowed index shape.

Searches performed using `msearch.py` (full machine records in `searches.jsonl`):

- LeanFinder: “Infinity categorical Barr Beck comparison conservative functors
  preserve geometric realizations equivalence on free objects”. Eight hits on
  ordinary nerves, Dold–Kan and free groupoids; none states this theorem.
- Loogle: `"Monadic", "Equivalence"`. Two hits:
  `instIsEquivalenceAlgebraToMonadMonadicAdjunctionComparison` and its comonadic
  dual, both for ordinary categories. Read Monad/Adjunction.lean:253–285;
  they do not supply an arbitrary-quasicategory comparison theorem.
- Mathlib grep: `monadic|Barr.Beck|geometric.realization`, restricted to
  CategoryTheory/Monad. Twenty-four hits, all ordinary monadic/comonadic
  machinery and split-coequalizer results; no coherent realization criterion.
- LeanSearch: “Infinity categorical comparison theorem conservative right
  adjoints preserve geometric realizations”. Eight ordinary adjunction/limit
  hits; none the required statement.
- `rg` in the upstream `WeilConjectures` tree and side `lean/Sheaf` searched
  monadicity, conservativity, geometric realization and coherent adjunctions;
  no copy of the item was found. The exact item-id search upstream was empty.
  This found the existing `ModelInfinity.CoherentAdjunction`, which is reused.
  An exact-name check of the proposed declaration names in both
  trees found no duplicates. No private copy of an existing notion was made. `comparisonComponent` is the
  degree-one evaluation formula for the published internal Hom, with endpoint
  equalities proved directly by its naturality and the simplicial identities;
  it supplies no new theorem with postponed proof.

Validation: per-file compilation through the prescribed `scompile.py`; the
expected sorry warning is the only permitted warning. The delivery dry run
also runs the server preflight and per-file compile. No global build or direct
Git mutation was run, and no shared source was edited.

## Second reading by Q142

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
