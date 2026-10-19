## Worker report

Item: `lem-coef-grothendieck-classifier-localization`.
Module: `Sheaf.CategoryTheory.GrothendieckClassifierLocalization`.
Main declaration:
`SSet.Enhanced.GrothendieckClassifierLocalization.grothendieck_classifier_localization`.

The theorem states `Nonempty ClassifierStatement.{u}`. The structure spells out the
classification and comparison constructions, their normalization equations and their
universal properties. All definitions and structure declarations are real constructions
or types of the displayed data. The only postponed theorem is the main theorem, whose
docstring follows all ten proof steps of the DAG node. No data are selected from this
existence assertion by a definition.

The node is unchanged except for `lean`. There are no new nodes, dependency repairs,
statement corrections or disputed statements. All helper declarations belong to this
node, are recorded in `lean.declarations`, and have source/blueprint docstrings.

### Hypotheses, one by one

- **Small ordinary C and strict H.** Every interface explicitly binds
  `{C : Type u} [Category.{u} C] (H : C ⥤ Cat.{u,u})`. The common small universe contains
  base and fibres; their coherent category of small categories and diagram categories
  live in `u+1`. The indexing nerve is lifted by `uliftFunctor.{u+1}` when mapping into
  the recorded `CatInfinity.{u}`. No nonempty, finite or groupoid condition is imposed.
- **The fibre systems and their transition preservation.** `RelativeData.W` is a
  Mathlib `MorphismProperty` on each original ordinary fibre. Its `multiplicative`
  field means identities and compositions are included. `isomorphisms` includes every
  isomorphism, and `transitions` says exactly that `(H.map f).toFunctor` preserves W.
  `nerveSystem W c a := W.W c a.hom` reads the same arrows in the ordinary nerve.
- **The specified total ordinary category and chosen lifts.** The statement uses
  Mathlib's `Grothendieck H`, `Grothendieck.Hom`, `Grothendieck.comp`, `forget`, `ι` and
  `toTransport`; it does not construct another total category. Its objects are dependent
  pairs and its arrows have components `(base,fiber)`, exactly `(f,v)` in the node.
  `comp` is `H(g)(v)` followed by `w`, with equality transport accounting for strict
  functor laws. `toTransport x f` has vertical component the identity. Its nerve edge
  is used literally in `ClassifierStatement.compare`.
- **Intrinsic p.** `compare` explicitly takes `P : SSet.{u}`, `Quasicategory P`,
  `p : P ⟶ nerve C`, and `CocartesianStraightening.IsIntrinsicFibration p`. It does
  not require p to be an inner fibration. `q : nerve (Grothendieck H) ⟶ P` has the
  exact over-base equation `q ≫ p = nerveMap (Grothendieck.forget H)`.
- **Preservation of the chosen ordinary lifts.** The next hypothesis of `compare`
  is `IsIntrinsicEdge p (yonedaEquiv.symm (ComposableArrows.mk₁
  (Grothendieck.toTransport x f)) ≫ q)` for every x and f. No preservation or
  localization condition on all total arrows is assumed.
- **Retained classification representatives.** `Replacement` contains a vertex of
  the existing `coCart` and a total equivalence from the original P, over `nerve C`,
  with the existing intrinsic/horn cocartesian-edge identification. The field
  `ClassifierStatement.replacements` asserts existence for every intrinsic input.
  `compare` works for every such retained representative. Thus this is a choice of
  model for intrinsic pullbacks, rather than an added assumption on p. The same
  straightening and its normalized ordinary classifications are used throughout.
- **The intrinsic fibres and restriction q_c.** `LocalData.restriction c` lands in
  the existing `fiber` of the retained representative. `restriction_eq` says its
  composite with the actual fibre inclusion is literally
  `nerveMap (Grothendieck.ι H c) ≫ q ≫ r.map`. This determines the restriction, including
  its higher simplices. Since `r.map` is an equivalence over the base, these strict
  fibres represent the intrinsic fibres of the original p, as in the dependency.
- **The localization units.** `LocalData.localized c`, `quasi`, `unit c`, `inverts`
  and `universal` are the fibre localization values and units. `universal` uses
  `markedFunctorSubcomplex` and the exact inclusion equation from the recorded
  system-localization theorem: the restriction on the entire functor simplicial set
  is an equivalence. It is not just an equivalence of homotopy categories or cores.
- **The specified J_c and factorization.** `LocalData.J c` is an actual functor to
  that same intrinsic fibre model, and `J_equivalence` uses the dependency's
  `IsFunctorEquivalence`. `factorization`, `factorization_source`,
  `factorization_target`, `factorization_equivalence` retain an equivalence edge
  from the actual q_c to `unit c ≫ J c` in the whole coherent functor category.
  Hence the specified homotopies have not been truncated to propositions of mere
  agreement of objects or homotopy classes.

### Conclusions, one by one

- **NT is classified by NH.** `ClassifierStatement.ordinary H` returns
  `OrdinaryClassification`. Its `total` is a vertex of the existing coherent
  `coCart(nerve C)`; `total_eq` fixes its total simplicial set to the ordinary nerve
  of the original `Grothendieck H`, and `base_eq` fixes the original projection.
  `marking` identifies its marking exactly with invertibility of the vertical
  component, in particular including every `(f,1)`. Its `comparison` is an
  equivalence edge from `ordinaryDiagram H` to the straightened total family.
  `ordinaryDiagram` is the existing `strictCoherentDiagram` applied to Mathlib's
  functorial ordinary nerve, retaining the full strict diagram and every simplex.
- **H_infinity is localization of the relative diagram.**
  `Comparison.localizedDiagram` and `localizationUnit` have source `ordinaryDiagram H`.
  `localized_objects` fixes their values to the supplied fibre localization objects;
  `unit_components` fixes the component functors to the supplied units. In addition,
  `localizationVertex` is a vertex of the entire coherent `localizingUnder W`, its
  arrow is exactly `localizationUnit`, and `localization_initial` makes it initial.
  This is the universal-arrow formulation of L applied to the relative diagram,
  using the formulation of L already adopted by `SystemLocalizationUniversal`.
  It asserts the universal property in a full coherent undercategory containing
  all target diagrams, all functors of target diagrams and all compatibility
  simplices; it is not a collection of independent choices of localized transitions.
- **q induces the transformation before localization.** `totalArrow` has endpoints
  the classified ordinary total and the retained representative of p, and
  `totalArrow_normalization` identifies its underlying simplicial map with the
  original q followed by the specified representative equivalence. The literal
  `straightening_triangle` composes the retained ordinary classification with
  straightening of that exact arrow to give `straightened`. Its components are
  q_c followed by the fibre classification equivalence (`straightened_components`).
- **The coherent equivalence with specified fibre components.** `comparison` is an
  edge from `localizedDiagram` to `classified S r`, and `comparison_equivalence`
  is equivalence in the entire coherent diagram category. `comparison_components`
  identifies its component with `L.J c ≫ fibreComparison c`, where the latter
  is the retained equivalence from the intrinsic fibre to its straightened value.
  Thus the component is precisely J_c under the required fibre identification.
- **The composite with the localization unit is the original transformation.**
  `factorization` is a two-simplex in that same entire diagram category; its three
  faces are `localizationUnit`, `comparison`, and `straightened`. This is the
  coherent triangle exhibiting the composite. `factorization_components` records
  the exact specified local factorization homotopy after the fibre identification.
  The helper `triangleCoherence` reads it from the actual inclusion of the endpoint
  path `{0,2}` into `{0,1,2}` in the coherent nerve. Its orientation is from q_c
  (the long edge) to lambda_c followed by J_c (the two short edges), matching the
  direction of `LocalData.factorization`.
- **Transport and all higher naturality.** Both the pointwise unit and the comparison
  are single simplices of `Fun(nerve C,CatInfinity)` with their full simplicial data.
  Restriction to any base arrow gives the transport square, and restriction to any
  longer simplex gives its compositional and higher coherence. Initiality of the
  unit in `localizingUnder` is the coherent localization-adjunction universal
  property, so it identifies the target transport with the localized H(f).
- **Unstraightening and the specified fibre functors.** `totalEquivalence` is an
  equivalence edge in the actual `coCart` from unstraightening `localizedDiagram`
  to the retained representative of p. `unstraightening_triangle` specifies it as
  unstraightening of `comparison` composed with the coherent inverse-equivalence
  comparison of straightening/unstraightening. `totalMap` is its actual underlying
  map over the base, fixed by `totalMap_normalization`. `unstraightenedFibre` gives
  the fibre identifications and `total_fibres` identifies the fibre functors with
  the original `L.J`. The replacement equivalence gives the stated intrinsic
  equivalence with the original P over NC.
- **Natural constructions and contractible retained choices.** `localization_choices`
  says the core of all initial objects in the full coherent system-inverting
  undercategory is contractible, with each unit and all its compatibility simplices
  retained. `comparison_space` is the core of the fixed-edge triangle space.
  `triangles` fixes both given edges throughout every parameter simplex, not only
  on vertices. `allFibers` is the actual simplicial map induced by evaluation at all
  base vertices. `retained_fibre_spaces` says its homotopy fibre over every prescribed
  tuple of local factorizations is contractible, retaining their comparison paths.
  These are the mapping-space universal formulations of the natural extension and
  uniqueness assertions in proof steps 6--10. They include naturality in targets and
  functors of the displayed data, rather than merely pointwise extension of maps.
  Naturality of the retained classification over base changes is already part of
  the recorded straightening structure used here. Classification choices themselves
  retain the `classification_space` assertion of that structure.

`HEq` occurs only to transport source/target identifications that are already fixed
by preceding endpoint or object equalities. For example, the unit component's source
is the fibre of the ordinary nerve diagram and its target is `localized_objects`.
It never compares unrelated choices of categories or substitutes an arbitrary map.

### Dependency declarations read and used

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `IsEquivalenceEdge`, `core`,
  `fullSubcomplex`, `diagramVertex`, `evaluation`, `comma`, `homotopyFiber`,
  `IsInitial`, `IsContractible`, `IsFunctorEquivalence`, `AreNaturallyEquivalent`.
- `Sheaf.CategoryTheory.CocartesianStraightening`: `Statement`, `coCart`, `object`,
  `diagrams`, `classify`, `IsIntrinsicFibration`, `IsIntrinsicEdge`,
  `cocartesian_straightening`. I read the full `Statement` and the normalization,
  fibre transport, base naturality and intrinsic replacement declarations.
- `Sheaf.CategoryTheory.SystemLocalizationUniversal`: `markedFunctorSubcomplex`,
  `IsEnhancedSystem`, and `coef_system_localization_universal`. Its universal-arrow
  formulation is used without introducing a second abstract localization adjunction.
- The source of `CatInfinity`, `StrictQuasicategoryFunctor`, `strictCoherentDiagram`
  is `EnhancedCartesianFibration`; the object and arrow decoders are from
  `CatInfinityOppositeInvolution`; `fiber`, `IsCocartesianEdge` and
  `Marked.Over.fiberMap` are the existing interfaces imported by straightening.
  `coreMap` is the existing construction from `IsofibrationPullbackLimit`.
- Mathlib: `CategoryTheory.Grothendieck` and its `forget`, `ι`, `toTransport`,
  `CategoryTheory.nerve`, `nerveMap`, `nerveFunctor`, the ordinary nerve quasicategory
  instance, `MorphismProperty.IsMultiplicative`, internal Hom and simplicial pullbacks.
- Every recorded proof dependency is imported in the required visibility except
  `lem-cbc-marked-relative-nerve-quillen`, which currently has no Lean record.
  Its explicit relative-nerve argument remains in the main theorem's proof docstring.
  The other imports are `CoherentNerveComparison`, `MarkedPointCartesianModel`,
  `EnhancedFunctorConeCalculus`, `InfinityAdjunctionMappingEquivalence`,
  `IsofibrationExponentiation`, `MarkedRelativeCartesianModel`; straightening and
  system localization are public statement imports.

### Edge cases and source checks

- Empty C is allowed: `ordinary`, `compare`, `RelativeData` and `LocalData` have no
  nonemptiness hypotheses; `allFibers` then lands in the empty product, the terminal
  space. The naturality and homotopy-fibre assertions still have their usual meaning.
- Empty fibres are allowed; all objects and equivalences use existing simplicial
  definitions with no artificial vertex or inhabitance assumption.
- Terminal C reduces to the fully faithful extension of one localization functor,
  with the specified factorization homotopy retained. The orientation of the
  two-simplex coherence was checked on the explicit endpoint/composite paths.
- W consisting of isomorphisms includes the identity-localization case. W containing
  all arrows is allowed and gives groupoid completion. Transition arrows and identity
  transitions are treated by the same strict functor and coherent unit.
- q is required to preserve only the displayed `(f,1)` lifts. Its preservation of all
  cocartesian arrows is a conclusion used to form `totalArrow`, not an extra hypothesis.
- None of the hypotheses is a placeholder `True` or an unconstrained comparison map.
  The representative, fibre restriction, straightened arrow, unit, comparison and
  unstraightened arrow all have their stated normalization equations.
- Read Haugseng arXiv:1312.3881v4 online, including Theorem 4.6 / Remark 4.7,
  Lemma 4.8 and Corollary 4.22. The node is the extracted coherent classifier argument,
  not the stronger total-localization hypothesis of Corollary 4.22. Also read the
  ancestor's current main-20261015 proof at
  `sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`
  and the recorded master-snapshot second proof paragraph. No blueprint unit changed.

### Searches

The exact machine-readable wrapper outputs are in the sandbox `searches.jsonl`.

- `msearch.py ... leanfinder`: “A cocartesian functor between Grothendieck constructions
  which is a localization equivalence on every fiber induces a coherent equivalence
  of classifying diagrams”. Eight hits, including `Grothendieck.preEquivalence` and
  `compAsSmallFunctorEquivalence`; these are ordinary equivalences, not this statement.
- `msearch.py ... loogle`: `CategoryTheory.Grothendieck, SSet.nerve` returned the unknown
  identifier `SSet.nerve`; corrected query
  `CategoryTheory.Grothendieck, CategoryTheory.nerve` returned zero hits.
- `msearch.py ... grep`: `Grothendieck|[Cc]ocartesian|[Ss]traighten`, subdirectory
  `CategoryTheory`, returned ordinary fibre-category and Grothendieck APIs. I read
  Mathlib's Grothendieck construction and the cocartesian-arrow signatures; they supply
  the ordinary objects used here, not the coherent localization comparison.
- `msearch.py ... leansearch`: “Coherent equivalence of infinity categorical classifying
  diagrams from localizations on every fibre of a cocartesian functor”. Eight hits
  concern ordinary fibre equivalences, localizer morphisms, ordinary localization
  universal properties and coherent sheaf topologies; no exact match.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for Grothendieck,
  classifier localization, `IsEdgeLocalization`, system localization and the exact
  item/declaration names: no existing version of this theorem. Nearby project
  declarations are `GrothendieckPresheafCoherentStraightening` (a presheaf/sieve
  statement) and `GrothendieckFibreLocalization` (a downstream Cartesian total
  localization theorem). Neither says the present classifier comparison, and neither
  is imported to avoid replacing the proof by a downstream result. The required
  system-localization and straightening declarations are reused directly.
- Queried `dag/lean_names_upstream.json` for the item and the new qualified helper
  names; there is no matching upstream declaration.

### Validation

The final module compiled with `scompile.py Q41
lem-coef-grothendieck-classifier-localization` in both sandbox and library-path modes,
under the default file limit, with no warnings. All universe variables and term
variables are explicitly bound; `autoImplicit` is disabled. There are no diagnostic
commands left, and all lines are at most 100 characters. Only the main theorem has
`sorry`. `deliver2.py Q41 lem-coef-grothendieck-classifier-localization --no-push`
reported OK: the commit passes server preflight and compiles. The final delivery
repeats these same checks.

## Second reading by Q41

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
