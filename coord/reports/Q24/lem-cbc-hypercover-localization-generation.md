## Worker report

Item: `lem-cbc-hypercover-localization-generation`, group Q24, 2026-10-17.
The item is stated in `Sheaf.CategoryTheory.HypercoverLocalizationGeneration` as
`CategoryTheory.DerivedHypersheaf.hypercover_localization_generation`. The only
postponed proof is that named theorem, whose docstring contains all nine proof
steps and their DAG dependencies. Definitions have real data. The item's natural
statement, source, proof and proof dependencies are unchanged.

Hypothesis and clause correspondence:

- The small category is `{C : Type u} [SmallCategory C]`. The arbitrary topology
  is `J : GrothendieckTopology C`, Mathlib's covering-sieve topology. There is no
  pullback, subcanonical, point, or finiteness assumption on C or J.
- `R : Type (max u w)` with `[CommRing R]` is the coefficient ring within the
  common chosen small universe. `ModulePresheaf C R` is the recorded
  `Cᵒᵖ ⥤ ModuleCat.{max u w} R`; `Complex C R` is its unrestricted integer
  cochain category. The unused bound w permits arbitrarily larger coefficients
  and presheaf values than the site, without identifying w and u. This is the
  universe convention of the existing hypersheaf presentation dependency.
- The enhancement is `L : SSet.{max u w + 1}` and the map
  `q : nerve (Complex C R) ⟶ L`. Its hypothesis `hq` is the existing
  `CoefficientFlatModel.IsEnhancedLocalization` at
  `HomologicalComplex.quasiIso (ModulePresheaf C R) (.up ℤ)`. Quasi-isomorphisms
  in this functor category are exactly objectwise quasi-isomorphisms. The
  hypothesis specifies the enhanced localization already named D(P) by the
  node: its factorization on entire coherent functor categories is an
  equivalence. It is not a hypothesis about arbitrary chosen mapping spaces,
  and is independent of the theorem's conclusion. Any such presentation gives
  the same statement under the localization equivalence. `hq.1` supplies the
  quasicategory instance for the presentability predicate; no extra horn-filler
  hypothesis is added.
- Representables, semirepresentability, augmented simplicial operators and the
  target are those of the recorded `AugmentedOver C T` and
  `augmentedOverToAugmented U`. The latter has right presheaf exactly
  `uliftYoneda.obj T`. `IsHypercover J` from the existing presentation node
  requires semirepresentable levels and the proper-face matching arrow in the
  presheaf slice to be epi after sheafification. Its degree-zero matching
  object is terminal in that slice, hence h_T. No representable intersections
  are requested. Hypercovers with a target merely isomorphic to h_T are
  represented here by transporting the augmentation along that isomorphism;
  this changes no hypercover or augmentation up to isomorphism.
- `hypercoverAugmentation R` is reused, not reconstructed: apply the free-module
  presheaf functor, the alternating-face augmentation, and
  `ComplexShape.embeddingDownNat`. Thus degree -n is the free module on U_n,
  equivalently the coproduct of L_S for its representable summands; positive
  degrees are zero, the differential is the alternating face sum, and the
  target is L_T[0].
- Local quasi-isomorphism is written inline in both conclusion clauses as
  `∀ r : ℤ, IsIso ((presheafToSheaf J (ModuleCat R)).map
  ((HomologicalComplex.homologyFunctor ... (.up ℤ) r).map f))`.
  This uses actual module-valued sheafification of the cohomology presheaf.
  No second definition of the local-quasi-isomorphism predicate is introduced.
  The size-transport instance `moduleForget_preservesSmallFilteredColimits`
  applies Mathlib's `preservesFilteredColimitsOfSize_shrink`; it resizes only
  the indexing categories for the existing forgetful-functor instance. This
  lets Mathlib construct sheafification at different site and module universes.
- Presentability is the first conjunct, the recorded
  `SSet.Presentability.IsPresentable.{max u w, max u w + 1} L hq.1`.
  It includes accessibility and every small coherent colimit, not ordinary
  categorical presentability.
- The small set of hypercovers is represented by an existential index
  `I : Type (max u w)` and family `H : I → Σ T : C, AugmentedOver C T`.
  The following conjunct requires every member to satisfy `IsHypercover J`.
  Targets may vary. Neither injectivity of the family nor a density conclusion
  is imposed: an indexed set presents its image, as required by this node.
- `shiftedHypercoverEdges R q H` is exactly the range indexed by `I × ℤ` of
  `q.app _ (ComposableArrows.mk₁ ((shiftFunctor ... k).map e_U))`.
  Both zero and negative shifts are included. These are actual edges in L.
- For every unrestricted P,Q and f:P→Q, the second clause is an `↔` between
  the all-degree sheafified cohomology test and membership of the actual edge
  represented by f in `SSet.Enhanced.strongSaturation` of that generator set.
- The new saturation definition is an intersection of every class containing
  the generators and equivalences with the five specified closure operations.
  Two-out-of-three tests all faces of every triangle. Retracts use a triangle
  in the coherent arrow category with identity long edge, so include homotopy
  retractions rather than only strict endpoint retractions. Pushout closure
  uses the recorded `CoefficientFlatModel.IsHomotopyPushout`. Small arrow
  colimits are actual coherent colimits in `(ihom Δ[1]).obj L`, tested on all
  small simplicial indexing sets, with apex allowed to vary. These are the
  pointwise arrow colimits; ordinary Hom-set bijections are not substituted.
- The final conjunct ranges over every T and every U over T, not just H,
  and asserts the same local quasi-isomorphism test on its augmentation.
  Every cohomology degree is quantified. P and Q have no lower or upper bound.

Dependencies read and used (full signatures and source docstrings inspected):

- `def-weil-size-convention`: metatheoretic universe convention, no Lean object.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, the cochain and quasi-isomorphism conventions. The
  enhanced category is specified separately; this ordinary derived category
  is not used in place of it.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`,
  `toSheafify`, `sheafificationAdjunction`.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `IsEquivalenceEdge`,
  `coconeCategory`, `IsColimiting`, and coherent mapping/cone conventions.
- `Sheaf.CategoryTheory.PresentableInfinityCategory`:
  `SSet.Presentability.IsPresentable` and `IsSmall`. Its record was initially
  missing in the shared checkout; `scompile.py --source` supplied the live
  source. It subsequently appeared in the refreshed shared DAG. No dependency
  repair or duplicate definition was needed.
- `Sheaf.CategoryTheory.DerivedHypersheafPresentation`: `ModulePresheaf`,
  `Complex`, `IsHypercover`, `hypercoverAugmentation`.
- `Sheaf.CategoryTheory.BoundedRepresentableHypercover`: `AugmentedOver`,
  `augmentedOverToAugmented`. These two landed definition nodes were added
  to stmt_deps to record the existing notions now used directly.
- `Sheaf.Paper.SheafFlatModel`: `CoefficientFlatModel.IsEnhancedLocalization`,
  `vertexDiagram`, `square`, `IsHomotopyPushout`. Its landed node is added to
  stmt_deps for these existing canonical interfaces.
- The only presently recorded proof dependency is
  `Sheaf.CategoryTheory.DenseRepresentableHypercovers`,
  `exists_small_dense_representable_hypercovers`, imported without public.
  The other eight proof dependencies currently have no Lean records and so
  have no import lines. They are retained in the proof and in the docstring;
  their proofs are not needed to state this theorem.

Edge cases checked before writing: empty C gives no targets and permits I empty;
no nonempty assumption on I; zero coefficient ring is allowed; the zero complex
and identities are covered; every integer r and k including zero and negative
values is retained; the degree-zero matching condition is over h_T; the chaotic
and empty-cover topologies are allowed; ordinary sites with no fibre products
and non-subcanonical topologies satisfy all binders. The arrow-colimit closure
includes empty diagrams. No data is chosen from a mere existence theorem.

Searches for an existing statement: `msearch.py` LeanSearch with
"hypercover augmentations generate local quasi isomorphisms in derived infinity
category" returned eight hits, including `DerivedCategory.isIso_Q_map_iff_quasiIso`
and `GrothendieckTopology.instIsGeneratedByOneHypercovers`, none the enhanced
hypercover generation theorem. LeanFinder with "module presheaf hypercover local
quasi isomorphisms small generators" returned eight sheaf-of-modules local
presentation/generator hits, none this result. Loogle with
"SSet, Quasicategory, Localization" returned no hits (unknown Quasicategory).
Mathlib grep `StronglySaturated|strongSaturation|IsPresentable` returned only
ordinary presentability. Direct rg on WeilConjectures and lean/Sheaf found the
already-used hypercover and enhanced-localization interfaces; rg on the exact
item id in upstream WeilConjectures found no statement. The new definition's
three kinds of search and DAG/blueprint searches are recorded in its node.
A source probe for `Sheaf.CategoryTheory.InfinitySmallLocalizationSaturation`
found no live module; no replacement theorem was asserted.

The source was read online at
[arXiv:1511.02828v1](https://arxiv.org/html/1511.02828v1), specifically the dense
hypercover and homology clauses and the small-family localization theorem.
Archive WANTED: arXiv:1511.02828v1, DHI math/0205027v2, and HTT at the source
places recorded in the DAG. Repository literature is read-only for this worker.
No statement correction or disputed-statement flag is needed.

Validation: every delivered Lean module was compiled individually by the required
`scompile.py Q24 lem-cbc-hypercover-localization-generation <both files>` in
sibling dependency order. Expected theorem sorry only; no warnings or errors.
The first compile exposed a product-category endpoint inference issue in
squareRow, fixed by annotating its product hom type. A subsequent compile
exposed the filtered-colimit indexing-universe mismatch, fixed by the real
Mathlib shrinking instance, not a new hypothesis. The required final dry run is `deliver2.py Q24
lem-cbc-hypercover-localization-generation --no-push`, which also performs
server preflight and per-file compilation.

## New nodes

`def-cbc-enhanced-strong-saturation` defines the strong saturation of a collection
of enhanced arrows, by intersection of classes closed under the operations
specified in the item. Source: HTT Definition the project server, with the item's explicit
retract convention. Module: `Sheaf.CategoryTheory.EnhancedStrongSaturation`.
Its helpers only implement the coherent arrow category, its edge/vertex
identification, the triangle witnessing a retraction, and the rows of the
existing coherent square. All are actual constructions. LeanSearch found
covering-sieve saturations; LeanFinder found ordinary small-object-argument
and ordinary morphism-property results. Mathlib and both project trees had no
matching definition. DAG searches found uses in theorem statements but no
independent definition node or recorded Lean declaration. The blueprint
search found no corresponding definition. The new node is cited directly
by the item, and its natural statement cites exactly its three dependencies.

## Second reading by Q24

I independently reread the node statement, its source place, every recorded dependency
signature, and both delivered modules. The source is Choudhury--Gallauer Alves de Souza,
arXiv:1511.02828v1, Facts 5.2 and 5.5, Theorems 5.7 and 5.11 (Section 5, pp. 17--21),
with the strong-saturation convention supplied by HTT Definition the project server.

Statement list and Lean verdicts:

1. A small site category `C` and arbitrary Grothendieck topology `J` are rendered by
   `{C : Type u} [SmallCategory C]` and `J : GrothendieckTopology C`. No pullbacks,
   subcanonicity, points, or finiteness are assumed: matches.
2. A commutative coefficient ring and the presheaf category of modules, with the
   stated cochain and objectwise-quasi-isomorphism conventions, are rendered by
   `R : Type (max u w)`, `[CommRing R]`, `ModulePresheaf C R`, and `Complex C R`:
   matches the size convention and does not identify the site and coefficient
   universes.
3. The enhanced localization at objectwise quasi-isomorphisms is rendered by
   `q : nerve (Complex C R) ⟶ L` and
   `hq : CoefficientFlatModel.IsEnhancedLocalization
   (HomologicalComplex.quasiIso (ModulePresheaf C R) (.up ℤ)) q`. This is the
   recorded full coherent localization universal property, not ordinary derived
   category data: matches.
4. Presentability of the enhanced category is the first conjunct,
   `@SSet.Presentability.IsPresentable ... L hq.1`: matches the node's
   accessible/all-small-colimits meaning.
5. Hypercovers over representables, their semirepresentable levels, and matching
   epimorphisms after sheafification are rendered by
   `H : I → Σ T : C, AugmentedOver C T` and
   `IsHypercover J (augmentedOverToAugmented (H i).2)`, using the canonical
   dependency definitions. The target is fixed to `h_T` by `AugmentedOver`:
   matches, including non-subcanonical sites.
6. The free alternating hypercover complex and augmentation are rendered by the
   canonical `hypercoverAugmentation R (augmentedOverToAugmented U)`, with no
   private reconstruction: matches.
7. A small varying-target family is rendered by
   `∃ I : Type (max u w), H : I → Σ T, AugmentedOver C T`; no nonemptiness,
   injectivity, or density hypothesis is added: matches.
8. The generator set of all integer shifts is rendered by
   `shiftedHypercoverEdges R q H`, whose range is indexed by `I × ℤ` and uses the
   actual shifted augmentation edges in `L`: matches all positive, zero, and
   negative shifts.
9. For every complexes `P,Q` and map `f`, the local quasi-isomorphism test is the
   all-integer-degree isomorphism test after module-valued presheaf sheafification,
   and the conclusion is membership of `q.app _ (ComposableArrows.mk₁ f)` in
   `SSet.Enhanced.strongSaturation ...`: matches the two directions and quantifier
   order of the node.
10. The strong saturation is the intersection predicate from
    `SSet.Enhanced.strongSaturation`; its module contains equivalences,
    two-out-of-three, coherent-arrow retracts, coherent homotopy pushouts, and all
    small coherent arrow colimits computed on endpoints. This renders exactly the
    node's closure convention.
11. The final universal clause quantifies every target `T` and every augmentation
    `U`, not merely the selected family, and asserts the same sheafified homology
    isomorphism in every `r : ℤ`: matches. No boundedness condition occurs.

Edge cases checked: the index `I` may be empty; `C` and its target collection may be
empty; the chaotic and empty-cover topologies are allowed; the zero ring and zero
complex are allowed; identity maps and `n = 0` are included; all integer degrees and
shifts, including negative and zero, are retained; matching degree zero is over the
representable target; and empty coherent arrow-colimit diagrams are included by the
small-colimit closure. No universe binder is independent of the site/ring bound.

Searches were repeated with `msearch.py` (hypercover/local-quasi-isomorphism and
strong-saturation queries), LeanFinder/Loogle, and `rg` over Mathlib, the source
`WeilConjectures/` tree, and repository `lean/Sheaf`. Results were ordinary derived
category/sheafification, covering-sieve saturation, or model-category closure only;
none has this enhanced hypercover-generation statement or the strong-saturation
notion. The exact declaration name is absent upstream. The dependency declarations
`ModulePresheaf`, `Complex`, `IsHypercover`, `hypercoverAugmentation`,
`AugmentedOver`, `augmentedOverToAugmented`, `IsEnhancedLocalization`,
`IsPresentable`, and `IsHomotopyPushout` were opened and match their node records.

No mismatch was found. Therefore no Lean or node repair, statement correction, citer
audit, or disputed-statement flag was needed. The only worker fixes (the typed product
endpoint in `squareRow` and the genuine filtered-colimit size-shrink instance) remain
in the delivered modules and introduce no extra hypothesis. Both files compile with
`scompile.py`; only the intended theorem proof is postponed.
