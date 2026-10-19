## Worker report

The module `lean/Sheaf/CategoryTheory/SimplicialRightFibrationPresentation.lean` states
`SSet.SimplicialRightFibration.simplicial_right_fibration_presentation`. Its conclusion is
`Nonempty Presentation.{u}`. `Presentation` bundles the construction data simultaneously
for all `u`-small bases, so that the requested naturality and composition of base changes
can be stated. It does not select a model or functor from the postponed theorem. Its
helper definitions have actual data, and the sole postponed proof is the final theorem.
The theorem docstring contains the complete ten-step proof recorded in the DAG.

The following is the hypothesis-by-hypothesis and clause-by-clause reading.

1. The universe is the explicitly bound `u`. Bases, coefficient values, cone values,
   total spaces, strict fibers and enriched mapping objects are `SSet.{u}`. Collections
   of diagrams and slice objects occupy `Type (u + 1)`. There is no Kan or quasicategory
   hypothesis on `S`, and no equality between distinct universe parameters is imposed.
2. Simplicial sets, weak homotopy equivalences and internal functor objects are Mathlib
   `SSet`, `KanComplex`, `ihom`, and the dependency's
   `SSet.Enhanced.IsWeakHomotopyEquivalence`. Right and left fibrations are the existing
   `SSet.Enhanced.rightFibration` and `leftFibration`, with arbitrary simplicial bases.
3. Simplicial opposite is Mathlib `SSet.opFunctor`, `SSet.opObjEquiv`, `SSet.op_δ` and
   `SSet.op_σ`: the latter give exactly the reversed `Fin.rev` face/degeneracy indices.
   Enriched opposite is Mathlib's `EnrichedCategory.opposite`; `enrichedOp` supplies
   the actual opposite enriched functor, with reversed hom arguments and composition.
4. `Diagram S` is the already landed `ConePresheaf.Presheaf S`, whose data are precisely
   `EnrichedFunctor SSet (PinchedCube.rigidification.obj S)ᵒᵖ SSet`. Its morphisms are
   full enriched, unit-graded transformations, not underlying ordinary transformations.
5. `ProjectiveData.weak`, `.fib`, and `.cof` fix the three model classes to
   `ConePresheaf.weakEquivalences`, `.fibrations`, and `.cofibrations`. These are
   respectively objectwise realization weak equivalences, objectwise all-horn Kan
   fibrations, and the left lifting class of objectwise boundary-injective trivial
   Kan fibrations. `.fibrant` identifies fibrancy with `IsKanDiagram`.
6. `SimplicialModel` includes the actual `ModelCategory` axioms, all `u`-small limits
   and colimits, and both functorial weak factorization systems, as required by the
   boundary-collapse dependency's convention. `.enrichment`, `.tensorCotensor`,
   and `.sm7` include enrichment, tensors, cotensors, and the actual SM7 corner map.
   The corner is Kan, and weak when either the cofibration or fibration is weak.
7. `ProjectiveData.mapping` identifies the enriched Hom with the existing
   `ConePresheaf.mapping`: its degree `n` is the full `Δ[n]`-graded enriched
   transformations, equivalently enriched maps `F × Δ[n] → G`. `.mapping_vertex`
   fixes ordinary morphisms to their actual components; `.mapping_comp` fixes
   pointwise composition with one common simplex parameter in every degree.
8. `DiagramCF S` is the full subcategory of projectively cofibrant, objectwise Kan
   diagrams, with initial-map cofibrancy from `ConePresheaf.IsProjectivelyCofibrant`.
   `RFib S` is the full subcategory of the actual slice `Over S` cut out by
   `rightFibration`. The inherited enrichment is the one fixed by `SliceData.mapping`.
9. The slice mapping object is exactly the existing
   `Enhanced.transportOverHom X.hom Y.hom`. Its subcomplex condition says, on every
   test simplex, that a map `X × Δ[n] → Y` commutes with projection to `S`.
   `SliceData.mapping_vertex` and `.mapping_comp` fix its vertices and shared-parameter
   composition. There is no arbitrary replacement of the requested mapping complex.
10. `RightData.quillen.adjunction` is an ordinary adjunction for the existing
    `ConePresheaf.left S` and `ConePresheaf.right S`. The first is the actual `T`:
    `leftObj p` uses `Straightening.straightening p.hom`, whose value is
    `Straightening.valueAt p.hom s`, the hom from the base inclusion of `s` to
    `Straightening.coneVertex p.hom` in `Straightening.conePushout p.hom`.
    That pushout is `C[X ⋆ Δ[0]] ⨿_{C[X]} C[S]`, with the existing ordered join
    and its pure-left, pure-right, and mixed simplex summands and concatenation operators.
11. The actual right functor, rather than an unspecified adjoint, is used throughout.
    `ConePresheaf.RightSimplex F n` is the dependent sum over `σ : Δ[n] → S` of
    `left(σ) → F`. `rightRestrict` restricts by the actual simplex arrow;
    `rightSet`, `rightProjection`, and `rightSetMap` give the total space, projection,
    and postcomposition of labels. Thus the explicit simplex and operator formulas
    are part of the constructions used in the statement, not additional hypotheses.
12. `RightData.enriched`, `.enriched_objects`, and `.enriched_maps` assert a simplicial
    structure whose ordinary functor is this same right functor. `.right_fibration`
    applies to every objectwise Kan diagram. `.presentation` restricts this exact
    enriched functor to `DiagramCF S → RFib S` and asserts the existing
    `DwyerKanEquivalence`: weak equivalences on all hom complexes, bijections on
    their path components, and essential surjectivity up to inverse components.
13. `RightData.fiber_comparison` takes the stated objectwise Kan hypothesis and is a map
    from `F(s)` to the actual strict vertex fiber of `U F`. `.fiber_comparison_natural` uses the actual component of every diagram
    arrow and the actual pullback-induced `Enhanced.fiberMap` of its image under `U`.
    `.fiber_comparison_weak` asserts weak equivalence exactly when `F` is objectwise
    Kan. This direction is the natural `F(s) → Sing_Q F(s)` comparison in the source;
    the statement does not assert an unjustified natural map in the reverse direction.
14. `RightData.preserves_weak` quantifies over a given enriched diagram arrow `f`,
    assumes both endpoints objectwise Kan and its actual components weak, and concludes
    `IsOverHomotopyEquivalence ((ConePresheaf.right S).map f)`.
15. `RestrictionData.objects` is precisely precomposition with `C[u]ᵒᵖ`, and
    `.components` fixes the restricted morphisms. `BaseChangeData.comparison` is a
    natural isomorphism of functors `U_S ⋙ u* ≅ restriction(u) ⋙ U_B`.
    `.restriction_id`, `.restriction_comp`, `.comparison_id`, `.comparison_comp`
    express identity and composition compatibility, using the actual canonical
    `Over.pullbackId` and `Over.pullbackComp` for pullback associativity.
16. `ConstantData` fixes the constant diagram's values, its entire enriched action
    to identity, and the component of every arrow in its coefficient value.
    `.comparison` is a natural transformation from the actual `productFamily S`
    (objects `S × X → S`) to `constant ⋙ U`. `.comparison_weak` asserts the weak
    equivalence of its actual vertex-fiber maps for Kan `X`.
    `ConstantBaseChangeData` further asserts naturality in the base, with the product
    pullback isomorphism fixed by both its Cartesian projections and the constant
    restriction isomorphism fixed by identity coefficient components.
17. `SliceData.mapping_kan` applies to arbitrary source `Z` and right-fibrant target
    `Y`. `.equivalence` applies to a specified map `f` between right fibrations and
    equates fiberwise weak equivalence to `IsOverHomotopyEquivalence f`. The latter
    requires an inverse arrow and two actual edges in the slice endomorphism complexes
    with the correct identity/composite endpoints. It imposes no strict inverse laws.
18. The contravariant `SliceData` fixes cofibrations to monomorphisms of underlying
    simplicial sets and fibrations to lifting against the actual trivial cofibrations.
    `.fibrant` identifies precisely the right fibrations and `.all_cofibrant` covers
    every slice object. `RightData.weak_test` fixes weak equivalences to the actual
    precomposition map `slicePrecompose f Z` on mapping complexes, for every right
    fibration `Z`. It tests the given arrow and does not substitute an unrelated map.
19. `SliceData.tensor` fixes the tensor object to `X × K → S`.
    `.tensor_unit` fixes the universal element to the curried identity on that product,
    after the inclusion of the actual slice mapping subcomplex. Together with
    `.tensorCotensor`, `.mapping` and `.sm7`, this states the requested simplicial model.
20. `QuillenEquivalenceData` states preservation of cofibrations and trivial
    cofibrations. Its criterion uses a cofibrant source and fibrant target in the
    specified models and equates weak equivalence of the given `f : T X → F` with
    weak equivalence of exactly `adjunction.homEquiv X F f`.
21. `CovariantData.slice` uses the same `SliceData` with `left = true`, hence the same
    Cartesian tensor, standard slice homs, SM7, all cofibrant objects, left fibrant
    objects, Kan mapping complexes, and the actual-map homotopy/fiber criterion.
    `.transported_weak` and `.transported_fib` transport the contravariant classes
    over `S.op` by the actual ordinary `Over.post opFunctor`; cofibrations on both
    sides are the monomorphisms. `.fiberwise_weak` explicitly gives the model weak
    equivalence criterion between left fibrations.
22. `CovDiagram S` is the existing `UnmarkedStraightening.Diagram (C[S])`, i.e.
    genuine covariant enriched diagrams. `CovProjectiveData` supplies its simplicial
    projective model, objectwise Kan fibrancy and standard graded-transformation
    mapping complex, with normalized vertices and composition in all degrees.
23. `CoherentReversal.reversal` is `C[S.op] ≅ C[S]ᵒᵖ`. `.simplex_objects` reverses
    `Fin` labels. `.simplex_paths` states, for every chain, exactly reflection of each
    subset in each position of the chain. `.naturality` fixes the extension to `C[S]`
    on every simplex generator, and `.vertices` fixes its action on each base vertex.
24. `CovariantData.reindex_values`, `.reindex_action`, and `.reindex_components`
    specify the covariant-to-opposite-base contravariant change of indexing, on the
    full enriched action as well as objects and arrows. `.opposite_formula` is an
    equality with `reindex ⋙ U_{S.op} ⋙ (Over.postEquiv opEquivalence).inverse`.
    Thus the output is literally opposite-base unstraightening followed by ordinary
    reversal of the total space and the canonical double-opposite base identification.
    `.quillen` gives its ordinary adjoint and the same exact Quillen-equivalence test.
    There is no assertion that simplicial opposite preserves simplicial enrichment.
25. `.derived` spells out the infinity-functor assertion: for coherent localizations
    of the full objectwise Kan diagram subcategory and the covariant slice, the
    induced map agrees with the restriction of this right functor up to an equivalence
    edge in the full functor simplicial set. It uses `FiniteReedy.IsLocalization`,
    which is the universal property on the entire coherent functor category.
26. `CovariantData.fibers` identifies the strict covariant fiber with the opposite
    strict fiber of right unstraightening over `S.op`; `.fibers_natural` uses the
    actual images of diagram arrows. Its natural equivalence as a space to `F(s)`
    is stated by `.space_comparison`, `.space_comparison_natural` and
    `.space_comparison_weak`: a natural map on realizations inducing bijections
    on components and every positive based homotopy group, using exactly the
    dependency's `componentsMap` and `homotopyGroupMap` convention. This comparison is
    constructed from the natural right fiber comparison for `reindex F`, the vertex
    equality `coherent.vertices` with `reindex_values`, and the natural identification
    of the realization of a simplicial set with that of its opposite. It asserts no
    simplicial map from every Kan complex to its opposite. `.preserves_weak` concerns
    the actual `unstraightening.map f` between the stated Kan-valued endpoints.
27. `CovBaseChangeData` gives the dual restrictions and natural base-change
    isomorphisms, with identity and composition equations. `CovConstantData` fixes
    the constant covariant diagram and its reindexing, and its `.opposite_comparison`
    fixes the actual comparison to the opposite of the contravariant constant map.
    Its source is `opFunctor ⋙ productFamily S`, hence `S × X.op`, and
    `.comparison_weak` tests its actual fibers for Kan `X`. All these constructions
    use the same `u`-small types; no total space or mapping object is resized.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, the existing realization/internal-Hom
  conventions, and the concrete ordered join reexported through the cone module.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases` reexports
  `Sheaf.CategoryTheory.InfinityFibrations`:
  `SSet.Enhanced.rightFibration`, `leftFibration`, and `fiber`. The dependency's
  recorded cocartesian extension is not substituted for these one-sided predicates.
- `Sheaf.AlgebraicTopology.PinchedCubeLatching`:
  `SSet.PinchedCube.coherentSimplex`, `rigidification`, `coherentSimplexUnit`, and
  their actual small coherent categories; its theorem is in the proof plan.
- `Sheaf.AlgebraicTopology.SimplicialBoundaryCollapseTest`:
  `CategoryTheory.simplicial_boundary_collapse_test`; its actual ModelCategory and
  functorial-factorization meanings are retained by `SimplicialModel`.
- `Sheaf.AlgebraicTopology.ConePresheafAdjunction`: the full `Presheaf`/component/
  projective-class/mapping interface and the exact concrete `left` and `right` functors.
- `Sheaf.CategoryTheory.ContravariantSliceModel`: `Enhanced.fiberMap`,
  `FiberwiseWeakEquivalence`, and the independently stated model used by the proof.
- `Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus`:
  `CategoryTheory.simplicialUnderlyingFunctor` and the projective-model proof input.
- `Sheaf.CategoryTheory.CoherentNerveComparison`: `CategoryTheory.DwyerKanEquivalence`.
  `SimplicialTensorCotensor` and `SimplicialModelLocalization.SatisfiesSM7` are the
  existing actual tensor/cotensor and corner-map interfaces; none is copied privately.
- `Sheaf.CategoryTheory.SpaceTransportClassification`: only the concrete
  `Enhanced.transportOverHomSubcomplex`, `transportOverHom`, and `transportHomVertex`.
- `Sheaf.AlgebraicTopology.UnmarkedStraighteningQuillen`: only `Diagram`,
  `DiagramHom.app`, its existing category, the projective classes, and `oppositeCategory`.
  Neither downstream classification theorem is used. Their owning theorem nodes have
  dependency paths back to this item, so adding them as mathematical prerequisites
  would be cyclic. Reusing their definitions agrees with the definition-only usage
  already documented by the landed cone-presheaf and projective-calculus modules.

Three independently landed prerequisite nodes are added to `stmt_deps`: the cone-presheaf
adjunction, contravariant-slice model and projective-model calculus. They already belong
to the item's proof dependencies; their dependency closures do not return to this item.
No existing definition or dependency interface needed replacement. The new helpers only
render the notions and clauses explicitly introduced by this item; there is no new
independent mathematical notion requiring a new DAG node.

Edge cases checked:

- Empty base: all strict fibers and all vertex conditions are vacuous; its slice and
  diagram constructions retain the empty total space and the terminal diagram category.
  No vertex is chosen in a definition or assertion.
- Point base: unstraightening is modeled by `Sing_Q`; no equality `U F = F(*)` or
  natural weak-equivalence arrow in the wrong direction is imposed.
- Empty Kan coefficient, disconnected Kan coefficients and non-Kan bases are allowed.
  Empty coefficients give empty total spaces; the constant-map assertion is conditional
  only on the stated Kan hypothesis.
- A specified equivalence need not be an isomorphism. The two endomorphism-complex
  edges retain actual homotopies, rather than adding strict inverse equations.
- Projective cofibrations are the lifting class, not objectwise monomorphisms; diagrams
  need not all be projectively cofibrant. Quillen tests require fibrant targets, not
  an extra cofibrancy hypothesis on the target.
- Covariance uses ordinary opposite equivalences. It does not confuse weak homotopy
  equivalence of underlying total spaces with equivalence of fibrations over the base.

Searches for existing declarations:

- `msearch.py ... leanfinder "Simplicial cone unstraightening gives a Dwyer Kan equivalence
  from enriched presheaves to right fibrations"`: 8 related ordinary-nerve/model results;
  no declaration states the requested presentation.
- `msearch.py ... leansearch "Simplicial unstraightening identifies cofibrant fibrant
  simplicial presheaves and right fibrations over a simplicial set"`: 8 related model
  cofibrant/fibrant and homotopy results, with no exact presentation theorem.
- `msearch.py ... loogle "Unstraightening"`: no hits.
- `msearch.py ... loogle "SSet.opFunctor, GradedNatTrans, EnrichedFunctor"`: no hits;
  the service reports unknown identifier `GradedNatTrans`. Local source inspection
  supplies the existing graded-natural-transformation interface.
- `msearch.py ... grep "unstraight|contravariantModel|DwyerKan" AlgebraicTopology`:
  no Mathlib hits for the combined construction.
- `rg` over Mathlib's enriched and simplicial-category/set sources found and reused
  `EnrichedCategory.opposite`, `EnrichedFunctor`, `GradedNatTrans`,
  `enrichedNatTransYoneda`, `SSet.opFunctor`, the opposite equivalence and internal Hom.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for straightening,
  unstraightening and right adjoints found no exact presentation declaration.
  `grep -rn "lem-coef-simplicial-right-fibration-presentation"` there has no hits.
- `rg` in `lean/Sheaf` found the existing cone-presheaf adjunction, coherent cone
  construction, projective calculus, slice model, actual over-base mapping complex,
  and generic covariant-diagram wrapper. Those definitions are reused directly.
  Searching for `IsOverHomotopyEquivalence`, `OverHomotopyEquivalence`,
  `HomotopyEquivalenceOver`, `slicePrecompose` and `overHomPrecompose` in all three
  source trees found no existing specified-arrow-over-base predicate or restriction map.

Validation: the prescribed `scompile.py` wrapper has compiled the complete module
successfully, both in the scratch namespace and at its final module path, with no errors
or warnings. The delivery dry run is recorded below once it completes. No source
statement was changed, and no `STATEMENT-DISPUTED` issue remains.

## Second reading by Q27

I opened the node, its HTT source place (Sections 2.1.4, 2.2.1--2.2.3, A.3.3), every
recorded statement dependency, and the complete Lean module.  The following is the
independent item-by-item match.

1. The fixed universe and base are rendered by the outer `u` and by `S : SSet.{u}` in
   `Diagram`, `RightData`, `SliceData`, `CovariantData`, and `Presentation`.  Values,
   joins, cones, mapping complexes, strict fibres, and total spaces are all `SSet.{u}`;
   only collections of such data are in the next universe.  No Kan or quasicategory
   hypothesis on `S` is introduced.  `SSet.opFunctor`, `opObjEquiv`, and the existing
   `EnrichedCategory.opposite` render the stated opposite conventions.  Verdict: exact.
2. The enriched category \(\mathsf D_S\), full enriched arrows, objectwise weak
   equivalences, objectwise Kan fibrations, projective cofibrations, and objectwise
   fibrancy are rendered respectively by `Diagram`, `ConePresheaf.Hom`, and the fields
   `ProjectiveData.weak`, `.fib`, `.cof`, and `.fibrant`.  `SimplicialModel` supplies the
   model axioms, limits and colimits, both functorial factorizations, enrichment,
   tensors/cotensors, and SM7 with both triviality alternatives.  `ProjectiveData.mapping`,
   `.mapping_vertex`, and `.mapping_comp` give the stated enriched natural maps in every
   degree, their ordinary vertices, and common-parameter composition.  `DiagramCF` is
   exactly the full cofibrant-fibrant subcategory.  Verdict: exact.
3. The cone adjunction and its explicit data are the already recorded
   `ConePresheaf.left` and `.right`.  `ConePresheaf.RightSimplex`, `.rightRestrict`,
   `.rightSet`, `.rightProjection`, and `.rightSetMap` give precisely the dependent sum
   over \(\sigma:\Delta^n\to S\), enriched maps from the cone module, the projection,
   and all simplex operators.  The module does not replace these canonical constructions
   by a choice.  `RightData.quillen` records the ordinary adjunction and the exact
   Quillen criterion; `.enriched`, `.enriched_objects`, `.enriched_maps`, and
   `.presentation` give the simplicial functor and its DK equivalence on `DiagramCF`.
   `RFib` and `SliceData.mapping` use the actual right-fibration full subcategory and
   `Enhanced.transportOverHom`, whose degree-n simplices are maps over `S` from
   `X × Δ^n`.  Verdict: exact.
4. The objectwise-Kan fibre comparison, weak preservation, restriction/base-change,
   and constant-product clauses are rendered by `RightData.fiber_comparison`,
   `.fiber_comparison_natural`, `.fiber_comparison_weak`, `.preserves_weak`,
   `BaseChangeData`, and `ConstantData`.  The comparison has the node's direction
   `F(s) → Enhanced.fiber ... s`, and `ConstantData.comparison` is the actual map from
   `productFamily S` (\(S×X\to S\)); `.comparison_weak` is exactly its vertex-fibre
   weak-equivalence assertion for Kan `X`.  The identity and composition equations use
   `Over.pullbackId` and `Over.pullbackComp` as required.  Verdict: exact.
5. The contravariant slice clauses are rendered by `SliceData` and `RightData.weak_test`:
   cofibrations are monos, weak equivalences are exactly all mapping tests against right
   fibrations via `slicePrecompose`, fibrations lift against trivial cofibrations, all
   objects are cofibrant, and fibrant objects are exactly right fibrations.  Its
   `mapping_kan` and `equivalence` fields give Kan mapping complexes and the equivalence
   (explicit inverse and two over-base simplicial homotopies) iff strict vertex-fibre
   weak equivalence.  `RightData.quillen` gives the stated Quillen-equivalence test.
   Verdict: exact.
6. The covariant clauses are rendered by `CovDiagram`, `CovProjectiveData`,
   `CoherentReversal`, and `CovariantData`.  The projective weak/fibration/cofibration
   classes and Kan condition are objectwise; `slice : SliceData S true` gives the same
   Cartesian tensor and mapping objects, all cofibrant objects, left-fibration fibrant
   objects, and the left-fibration fibrewise criterion.  `transported_weak` and
   `transported_fib` transport the classes along the actual ordinary `Over.post
   opFunctor`; the cofibration class is independently fixed to monos on both sides.
   `reindex_values`, `.reindex_action`, `.reindex_components`, and `.opposite_formula`
   render the opposite-base formula for `U_cov`; `quillen`, `.left_fibration`,
   `.preserves_weak`, `.fibers`, and the three `.space_comparison` fields render the
   derived functor, left-fibration, fibre, and space-comparison assertions.  The
   `derived` field is the localization universal-property formulation.  Verdict: exact.
7. `CovRestrictionData`, `CovBaseChangeData`, `CovConstantData`, and
   `ConstantBaseChangeData` render covariant restriction, identity/composition base
   change, the opposite constant-product map, its fibrewise weak equivalence, and the
   two Cartesian product projections and identity coefficient components.  `Presentation`
   packages these data simultaneously for all `u`-small bases; projecting to a fixed
   `S` gives every clause in the node, while arbitrary `A → B → S` base-change chains
   require exactly this shared family.  Verdict: exact.

Edge cases were checked directly against the definitions and quantified fields: `S = ∅`
and `S = Δ⁰`; empty and disconnected coefficient simplicial sets; non-Kan bases;
degree `n = 0`; empty slice total spaces; identity and composite base maps; and the
opposite involution on degree-zero vertices.  No field chooses a vertex, assumes a
nonempty base, identifies a strict fibre with a value, or requires a strict inverse in
place of the stated homotopies.  All index and coefficient types remain in `Type u`.

For the independent existing-declaration search I ran:

* `msearch.py Q27 lem-coef-simplicial-right-fibration-presentation leansearch
  'Cone unstraightening is a Quillen equivalence and presents the enriched category
  of right fibrations'`: eight ordinary cone or conical-limit results; no match.
* `msearch.py Q27 lem-coef-simplicial-right-fibration-presentation leanfinder
  'simplicial right fibration presentation unstraightening'`: only right Kan-extension,
  strict Segal, and ordinary model-category results; no match.
* `msearch.py Q27 lem-coef-simplicial-right-fibration-presentation loogle
  'rightFibration'`: the identifier query is unavailable (unknown identifier).  I
  replaced it by the valid quoted name-substring query `'"unstraight"'`: zero hits.
* `msearch.py Q27 lem-coef-simplicial-right-fibration-presentation grep
  'Unstraightening|rightFibration|DwyerKan'`, plus `rg` over Mathlib,
  `WeilConjectures/`, and the repository's `lean/Sheaf/`: no existing presentation
  theorem or duplicate declaration.  The `rg` hits are the canonical dependency
  declarations used above.

I found no mathematical statement mismatch, extra hypothesis, weakened clause, universe
restriction, second definition, or hollow data.  I repaired one conventions defect: the
`derived` field introduced its Kan subcategory and weak-equivalence class by local `let`
binders.  The project forbids these in statements because Lean elaborates them as opaque
`have` binders.  I replaced them with the named definitions `covKanProperty`
and `covKanWeak`, each with source and blueprint docstrings, and recorded both names
in `lean.declarations`.  This changes no mathematical clause.  The node's
`lean.statement` is verbatim `theorem simplicial_right_fibration_presentation :
Nonempty Presentation.{u}`.  `scompile.py` compiled the module at its final path with
no errors or warnings.

## Maintainer review fix (cc reviewer, 2026-10-17)

The statement, helper structures and DAG record are accepted unchanged. One conventions
repair (stages/2-statements.md §3 rule 7): the stated proof dependencies
`lem-coef-cone-boundary-projective-cells` and `lem-coef-unstraightening-homotopy-descent`
had no import. The module now has the private imports
`Sheaf.AlgebraicTopology.ConeBoundaryProjectiveCells` and
`Sheaf.CategoryTheory.UnstraighteningHomotopyDescent`; it compiles cleanly with
`tools/nt_compile.py`. Nothing else changed.

Import cycles left out and listed (rule 7): `lem-coef-unmarked-straightening-quillen`
and `lem-coef-space-transport-classification` list this item as a proof dependency, but
this module imports their modules (`Sheaf.AlgebraicTopology.UnmarkedStraighteningQuillen`,
`Sheaf.CategoryTheory.SpaceTransportClassification`) for definitions only, so the import
of this module into those two must be left out. Their stage-3 proofs will need the
theorem moved out of, or the definitions split from, those modules.
