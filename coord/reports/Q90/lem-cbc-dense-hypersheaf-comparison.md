## Worker report

Q90 states `CategoryTheory.DerivedHypersheaf.dense_hypersheaf_comparison` in
`lean/Sheaf/CategoryTheory/DenseHypersheafComparison.lean`. Its only theorem has proof
`by sorry`. Its docstring contains all twelve mathematical proof steps from the DAG.
The item's statement, proof and proof dependencies are unchanged. The sole added
statement dependency is the new definition node described below. No dependency record
is repaired and no source assertion is silently corrected.

The statement uses an explicit complex presentation of the coherent presheaf category,
rather than an arbitrary map between unspecified enhanced categories. Every definition
has real data. In particular, neither a derived category nor a Kan extension is selected
from a mere unproved existence claim. A `Presentation` includes the published full
coherent localization universal property, and the theorem asserts these presentations
exist as part of its conclusion before quantifying over all presentations.

The correspondence with EACH hypothesis and clause is as follows.

| Node text | Lean rendering |
| --- | --- |
| Small categories with covering-sieve Grothendieck topologies; no fibre products required | `{C D : Type u} [Category.{v} C] [Category.{v} D]`, `J : GrothendieckTopology C`, `K : GrothendieckTopology D`. There is no `HasPullbacks` or `Subcanonical` binder. Mathlib's topology has the maximal-sieve, pullback-sieve and transitivity axioms. |
| All sizes follow the convention | Explicit `universe u v w`, coefficient and presheaf values in `max u v w`; enhanced categories in `max u v w + 1`. Object and morphism universes remain independent. `AsSmall.up/down` only enlarges the comma index and coefficient-complex category to the common enhanced universe. |
| A commutative ring and enhanced derived coefficients | `(R : Type (max u v w)) [CommRing R]`; `CoefficientPresentation R` is the full coherent localization of cochain complexes of `ModuleCat R` at quasi-isomorphisms. `HasWeakSheafify` supplies the recorded sheafification API for sets on each small site; it is available for all sites here, not an additional geometric condition. |
| Hypercovers are augmented simplicial families with locally surjective matching arrows after sheafification | `IsHypercover`: actual augmentation over a presheaf isomorphic to `uliftYoneda.obj T`; `IsSemirepresentable` for every level; `SimplicialObject.IsProperFaceMatchingArrow` in the presheaf slice; `Epi ((presheafToSheaf J ...).map μ.left)` in every degree, including zero. |
| A hypersheaf sends each hypercover to its homotopy-limit diagram; family evaluation is a product | `HasHyperdescent` tests `QuasiIso (CoefficientFlatModel.homMap (hypercoverAugmentation R X) (𝟙 M))` for EVERY semirepresentable hypercover. `hypercoverAugmentation` applies the actual sectionwise free module functor, alternating-face chain construction and extension to degrees `-n`. The full Hom complex has products over all source degrees and over the representable family. Its free source terms are coproducts of projective representables, in nonpositive degrees, so ordinary Hom from these bounded-above complexes computes the derived Hom and hence the hypercover homotopy totalization. This is all-degree hyperdescent, rather than only degree-zero sheafness. |
| Hypersheaves have the SAME fixed pointwise lower bound | `IsPointwiseGE M a := ∀ T i, i < a → IsZero ((M.asFunctor.obj (op T)).homology i)`. It is a cohomology bound at every object, not a bound on the terms of a complex or an object-dependent integer. |
| The FULL enhanced category, coherent transformations, derived ends | `Representatives` is Mathlib's full subcategory of all strict complex representatives satisfying the two predicates; `weakEquivalences` is their objectwise quasi-isomorphisms. `Presentation.localization` and `CoefficientFlatModel.IsEnhancedLocalization` retain the ENTIRE coherent functor-category universal property, not merely its ordinary homotopy category. Strict complex diagrams at objectwise quasi-isomorphisms present coherent derived diagrams; the existing rectification and hypersheaf-model nodes remain proof inputs, not assumptions on the theorem. |
| A functor `p` | `(p : C ⥤ D)`. |
| It sends covering families to covering families | `LocalEquivalence.coverPreserving : CoverPreserving J K p`. Generated covering sieves and their image sieves give the family formulation. |
| Every cover of `p(C)` refines an image cover of `C` | `LocalEquivalence.coverRefining : p.IsCocontinuous J K`, exactly the covering-sieve refinement condition. |
| Every arrow between image objects lifts locally on its source | `LocalEquivalence.locallyFull : ∀ A B b, p.imageSieve b ∈ J A`. Membership in `imageSieve` is the existence of an actual local lift after precomposition. |
| Arrows with equal image agree locally | `LocalEquivalence.locallyFaithful : ∀ A B f g, p.map f = p.map g → Sieve.equalizer f g ∈ J A`. |
| Every object of D is covered by image objects | `LocalEquivalence.coverDense : p.IsCoverDense K`. |
| No global full faithfulness on original hom sets | There is no `[p.Full]` or `[p.Faithful]`; only the two local covering-sieve clauses above. |
| Precomposition gives the enhanced equivalence | The existential `hres` proves that the actual `restriction p R` preserves representatives. `IsRestrictionModel` specifies the localized `f` by its coherent agreement with `nerveMap (restrictRepresentatives ...)`. The two `AreNaturallyEquivalent` clauses for `f ≫ g` and `g ≫ f` are the published enhanced-equivalence definition. |
| Quasi-inverse is homotopy right Kan extension | `hran` proves the actual termwise `rightKan p R` preserves hyperdescent and the bound on K-injective representatives. The enhanced natural equivalence between `nerveMap (ranRepresentatives ...) ≫ HD.localization` and `nerveMap (forgetKInjective ...) ≫ HC.localization ≫ g` specifies this very inverse on those representatives. K-injective replacements compute the right derived functor on all objects. |
| Value at D is the homotopy limit over the OPPOSITE comma category | `rightKanCone p R I T` has index `StructuredArrow (op T) p.op`, canonically `(p ↓ T)ᵒᵖ`, with all arrows (not just covering arrows) and apex `(rightKan p R).obj I` evaluated at `T`. Its legs are restriction followed by the actual Kan counit. `IsDerivedLimit (largeRightKanCone ...) L.localization` requires the image of that specific cone to be terminal in the published coherent cone category for every coefficient localization model. `strictDiagramComparison` carries the entire strict cone transformation, including naturality simplices. |
| The inverse is a hypersheaf | The first conjunct of `hran I` is `HasHyperdescent K R ((rightKan p R).obj I.obj.obj)`, and the localized right Kan functor lands in `Representatives K R a`. |
| Equivalence on derived mapping complexes | The final quantified clause asserts a quasi-isomorphism of the WHOLE Hom complex from restriction followed by the canonical postcomposition map into a K-injective replacement. For arbitrary `X,Y`, `i : Y.obj ⟶ I` is any K-injective quasi-isomorphic replacement, and `j : restriction I ⟶ I'` is any further K-injective quasi-isomorphic replacement. The source `HomComplex X I` and target `HomComplex (restriction X) I'` compute derived ends in the presheaf categories. The maps are the actual additive-functor map and `CoefficientFlatModel.homMap`; their underlying additive quasi-isomorphism detects the same quasi-isomorphism of the naturally R-linear complexes. `IsFullyFaithful f` also states equivalence on all enhanced mapping spaces. |
| Naturality for commutative squares of these functors | `IsSquareNatural` quantifies over `p', α, β` satisfying the same five site hypotheses and `α ⋙ p = p' ⋙ β`. The enhanced vertical maps and `f'` must each be models of their ACTUAL restrictions, and `g'` has its coherent inverse witnesses. The two conclusions are `AreNaturallyEquivalent (f ≫ r) (s ≫ f')` and `AreNaturallyEquivalent (r ≫ g') (g ≫ s)`, for restriction and its inverse. These are equivalences in full coherent functor categories. |
| Both directions preserve the specified pointwise bound a | `hres` and `hran` each include the same `IsPointwiseGE ... a`; both enhanced categories in the equivalence are `Presentation ... R a`. |

The new module defines all its canonical maps directly. `rightKanPresheaf_additive`
is the instance derived from the Kan adjunction and the existing theorem that a
product-preserving functor between preadditive categories is additive. The categorical
law fields in definitions are discharged with Mathlib's existing functor/adjunction laws;
there is no new mathematical theorem besides the item's postponed statement.

Dependency declarations read and used:

- `def-weil-size-convention` is a universe convention without a Lean module. Its
  independent site/value universes are implemented explicitly, not collapsed.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `HomologicalComplex.quasiIso` and `CochainComplex` conventions.
  The ordinary `DerivedCategory` is not substituted for its enhanced localization.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.AreNaturallyEquivalent`,
  `IsFullyFaithful`, `coneCategory`, `IsLimiting`, `diagramVertex`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf` and its adjunction,
  applied to matching arrows of set presheaves.
- `Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic`:
  `FormalCoproduct`; `FormalCoproduct.uliftYoneda` from the existing presheaf embedding
  of formal families, rather than a private copy of the formal-family category.
- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`: `SimplicialObject`, its operators
  and the augmented-object structure, with the existing alternating-face construction.
- `Sheaf.CategoryTheory.SiteHypercoverDisjointUnion`:
  `SimplicialObject.IsProperFaceMatchingArrow` in its FULL general-category signature.
  Only this general matching definition is reused: the subcanonical/fibre-product
  hypotheses of that module's separate theorem are not imposed here.
- `Sheaf.Paper.SheafFlatModel`: `CoefficientFlatModel.homMap` and
  `CoefficientFlatModel.IsEnhancedLocalization` in their general-category signatures.
  Its theorem's ringed-site model assumptions are not imposed on these definitions.
- The theorem imports the already stated proof dependencies:
  `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`,
  `Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv`,
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Preserves`,
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective`,
  `Mathlib.CategoryTheory.Sites.Abelian`, and
  `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
  The bounded hypersheaf-model, enhanced-localization theorem, and Quillen
  rectification nodes have no recorded modules yet. No statement of those theorems
  is needed to type this item: the concrete presentation is defined here, while those
  nodes remain the named proof dependencies in the unchanged twelve-step proof plan.

Edge cases checked against the signatures and definitions:

- The empty category is allowed. Then the pointwise bound and descent tests indexed
  by objects have their expected empty meanings; no `Nonempty C` was introduced.
- The zero ring, zero modules and zero complexes are included; no characteristic,
  nontriviality or finite-dimensionality condition was introduced.
- Empty covering families are retained on sites where the empty sieve covers.
  An empty representable family linearizes to zero, and the full Hom/product
  construction gives the empty product (the zero module) as required.
- Degree-zero matching is terminal IN THE SLICE, hence the base presheaf, rather
  than terminal in the unsliced category. Degree one is the corresponding fibre
  product in PRESHEAVES; no fibre products in the original site are assumed.
- Non-subcanonical sites are included: representables are presheaves and only their
  matching arrows are sheafified. No Yoneda-to-sheaves embedding is assumed.
- Any integer `a`, negative as well as positive, is allowed. Vanishing is quantified
  over every integer below it, not a nonnegative-degree substitute.
- The comma category may be empty; the coefficient cone criterion then asks for its
  genuine terminal object, without a hidden nonempty-index condition.
- Identity site functors and identity commutative squares are allowed. The Kan
  counit and restriction maps are their actual canonical constructions.
- Locally full/faithful functors need not be globally full/faithful. For example,
  on a one-object group category with the topology in which every sieve covers,
  the functor to the terminal category satisfies the local equalizer and lifting
  conditions even when it identifies different arrows. No hom-set injectivity
  could be inferred from the binders used here.

Searches were made through the required msearch wrapper and direct read-only searches.
The main-node LeanFinder query about restriction/right Kan along a locally full,
locally faithful cover-dense functor returned only ordinary sheaf/dense-subsite maps,
including `Functor.IsDenseSubsite.sheafEquiv`, not this enhanced theorem.
The Loogle query `"GrothendieckTopology", "IsDenseSubsite"` returned four ordinary
site instances. Mathlib grep `hypersheaf|hypercomplete|hyperdescent` returned zero.
The source `WeilConjectures/` and `lean/Sheaf/` searches found no existing statement
of this node, and the upstream node-id search found none. LeanSearch for hypercomplete
bounded coherent presheaves returned ordinary one-hypercover/sheaf and cohomology-bound
lemmas. The new definition's exact searches and results are reproduced below and in
its `mathlib_searches`; they did not find an existing definition of this presentation.

No `STATEMENT-DISPUTED` flag or known statement fault remains. Tag 03A0 was read in
`literature/stacks-project/sites.tex`; it is explicitly only the ordinary prototype,
not falsely cited as a proof of the enhanced assertion. The blueprint ancestor is
`thm-cbc-finite-level-proetale`, in the current main-20261015 snapshot.

Validation: both delivered modules compiled separately in dependency order through
`scompile.py Q90 lem-cbc-dense-hypersheaf-comparison <both files>` on 2026-10-16 UTC,
including the wrapper's sandbox and library-name checks, with no errors or warnings.
The fixed limits were respected. The prescribed `deliver2.py Q90 lem-cbc-dense-hypersheaf-comparison --no-push`
dry run printed `OK (dry run)` on 2026-10-16 UTC: both modules compile and pass
preflight except for the independent second reading, which the assigned reader supplies.
Nothing was pushed. A second reading is intentionally left to
the separately assigned second reader.

## New nodes

`def-cbc-derived-hypersheaf-presentation` provides the explicit strict-complex
presentation of the hypersheaf category introduced in the item's prose, and the
canonical restriction, right Kan, full-Hom and cone constructions needed to state its
clauses. Its source is the semirepresentable hypercover convention of Stacks Tags
01G5 and 0DB2, extended to arbitrary covering-sieve sites exactly as specified by the
item's agent-formulated foundation. It does not assert a new comparison theorem or
claim the Stacks tags already give the enhanced statement. The original DAG has no
DEFINITION node for this concrete presentation. In particular,
`lem-cbc-bounded-below-hypersheaf-model` is the separate equivalence theorem between
derived sheaves and hypersheaves, not the definition of this presentation; it is
neither copied nor assumed in place of defining data. Similarly the existing
`lem-cbc-presheaf-dg-function-complex`, `lem-cbc-cosimplicial-complex-holim`,
`lem-cbc-hyperdescent-local-orthogonality` and
`lem-cbc-hypercover-localization-generation` are mathematical identification theorems,
not recorded declarations of the data constructions supplied here. Their statements
were read to verify the free-resolution/full-Hom presentation agrees with the shared
mathematical conventions. They presently have no usable Lean declaration to import.
The new node reuses the existing formal coproduct, matching-arrow, sheafification,
cochain, full-Hom and coherent-localization definitions; it introduces none of those
notions a second time. All 27 declarations in its module belong to this single
presentation and are listed in `lean.declarations`, with individual source/blueprint
docstrings. No new postponed theorem occurs in it.

New-notion searches (raw wrapper result records):

```json
{
 "t": "2026-10-16T20:42:50Z",
 "tool": "grep",
 "query": "hypercoverAugmentation|HasHyperdescent|IsSemirepresentable|hypersheaf",
 "sub": "",
 "ok": true,
 "n_hits": 0,
 "note": "",
 "top": [],
 "digest": "4f53cda18c2baa0c"
}
```

```json
{
 "t": "2026-10-16T20:42:50Z",
 "tool": "leansearch",
 "query": "A derived module presheaf is a hypersheaf if the augmented free module complex of every semirepresentable hypercover induces a quasi-isomorphism on its full Hom complex",
 "sub": "",
 "ok": true,
 "n_hits": 8,
 "note": "",
 "top": [
  "PresheafOfModules.Derivation",
  "PresheafOfModules.Derivation'",
  "PresheafOfModules.Derivation.ctorIdx",
  "CategoryTheory.Presheaf.isSheaf_iff_of_isGeneratedByOneHypercovers",
  "SheafOfModules.mk",
  "PresheafOfModules.Derivation'.app",
  "PresheafOfModules.Derivation.ext",
  "PresheafOfModules.Derivation.d"
 ],
 "digest": "1d4ce29adcdcda30"
}
```

```json
{
 "t": "2026-10-16T20:42:56Z",
 "tool": "leanfinder",
 "query": "The category of uniformly bounded below hypercomplete derived module presheaves presented by complexes satisfying hypercover descent",
 "sub": "",
 "ok": true,
 "n_hits": 8,
 "note": "",
 "top": [
  "CondensedMod",
  "instAbelianCondensedMod",
  "LightCondensed.instIsGrothendieckAbelianLightCondMod",
  "CondensedMod.ofSheafCompHaus",
  "CategoryTheory.GrothendieckTopology.HOneHypercover",
  "CategoryTheory.GrothendieckTopology.OneHypercoverFamily",
  "CategoryTheory.GrothendieckTopology.OneHypercover.instCategory",
  "CondensedMod.ofSheafProfinite"
 ],
 "digest": "0537cdb0fda4e64c"
}
```

Additional read-only searches: `python3 tools/blueprint_refs.py search hypersheaf`
returned zero blueprint matches; `python3 tools/blueprint_refs.py ancestor
lem-cbc-dense-hypersheaf-comparison` returned `thm-cbc-finite-level-proetale`.
`rg -n "def-cbc-derived-hypersheaf-presentation" dag/nodes` found no existing node.
`rg -n "hypercoverAugmentation|HasHyperdescent|IsSemirepresentable|hypersheaf"`
on the source `WeilConjectures/` and side-project `lean/Sheaf/` found no matching
published declaration. Grep of the DAG found the theorem nodes discussed above,
which were read; none supplies an existing definition of the constructed presentation.

Resume validation (2026-10-16 UTC): reread both sandbox modules and compared the
item record with the current read-only DAG. Only `lean` and the added definition's
`stmt_deps` entry differ; the statement and all twelve proof steps are unchanged.
There is no repair note or Q90 return entry for this item. Fresh LeanFinder search
`A locally full locally faithful cover dense functor of sites gives an equivalence
on bounded below derived hypersheaves with homotopy right Kan inverse` returned
eight ordinary sheaf/dense-subsite results and no enhanced comparison. Fresh
Loogle search `"GrothendieckTopology", "IsDenseSubsite"` returned the four ordinary
site instances already noted. Read-only `rg` for
`hypersheaf|hypercomplete|hyperdescent|HasHyperdescent|hypercoverAugmentation` in
the source `WeilConjectures/` and current `lean/Sheaf/` returned no match. Both
modules were recompiled separately through `scompile.py`, with no errors or
warnings; the construction module took about five seconds and the theorem module
about three seconds. The existing implementation needed no Lean changes.

## Second reading by Q90

I reread the node statement, its dependency declarations, the Stacks source place, and both delivered modules. The item-by-item comparison is:

1. **Sites and size.** The node's two small categories with Grothendieck topologies and no fibre-product or subcanonical hypothesis are rendered by `{C D : Type u}`, `[Category.{v} C]`, `[Category.{v} D]`, and `J K : GrothendieckTopology`; no pullback or subcanonical instance is assumed. The explicit `u`, `v`, and coefficient universe `max u v w` implement the common larger size convention while keeping object and morphism levels independent.
2. **Coefficients and enhanced complexes.** The commutative coefficient ring is `(R : Type (max u v w)) [CommRing R]`. `Complex`, `CoefficientPresentation`, `Presentation`, `weakEquivalences`, and `CoefficientFlatModel.IsEnhancedLocalization` give the coherent complex localization, including derived mapping data and higher composition data. No ordinary `DerivedCategory` is substituted for the enhanced presentation.
3. **Hypercover data.** `IsSemirepresentable`, `augmentedSlice`, and `IsHypercover` encode an augmented simplicial family, representable target, semirepresentable levels, and sheafified locally epi proper-face matching arrows in the presheaf slice. Degree zero uses the terminal slice object through `IsProperFaceMatchingArrow`; no fibre products of the underlying site or subcanonicity are required.
4. **Hyperdescent and family products.** `freePresheaf`, `hypercoverAugmentation`, and `HasHyperdescent` use the actual alternating-face free-module complex and `CoefficientFlatModel.homMap` on the full Hom complex. Thus the source-to-totalization map has all cohomological degrees and products over family components, rather than only degree-zero sheafness.
5. **Pointwise lower bound.** `IsPointwiseGE K a` is `∀ T i, i < a → IsZero (...)`, using cohomology at every object and every integer below the one fixed `a`; it is not a termwise or object-dependent bound.
6. **Full enhanced hypersheaf category.** `Representatives` is the full subcategory on hyperdescent and the pointwise bound, and `Presentation` retains the complete coherent localization universal property. `weakEquivalences` is objectwise `QuasiIso`, as required.
7. **The five hypotheses on `p`.** `LocalEquivalence` renders cover preservation by `CoverPreserving`, cover refinement by `Functor.IsCocontinuous`, local fullness by `p.imageSieve b ∈ J A`, local faithfulness by `Sieve.equalizer f g ∈ J A`, and density by `Functor.IsCoverDense K`. These are exactly the node's sieve formulations and impose no global `Full` or `Faithful` instance.
8. **Restriction and inverse.** `restriction` is literal precomposition by `p.op`; `rightKan` is the actual ordinary presheaf right Kan extension applied termwise, with `rightKanCounit` its canonical counit. `rightKanCone` uses `StructuredArrow (op T) p.op`, which is the opposite comma category `(p ↓ T)ᵒᵖ`; `largeRightKanCone` only applies the stated `AsSmall` universe transport.
9. **Preservation and enhanced equivalence.** `PreservesRepresentatives` supplies the same descent and bound for restriction. The theorem existentially supplies `hres`, `hran`, and for every coefficient/presentation pair the maps `f`, `g`, inverse natural equivalences, and full faithfulness. `IsRestrictionModel` ties `f` to the actual strict restriction through the localization maps; `ranRepresentatives` ties the inverse to the actual right Kan functor on K-injective representatives.
10. **Derived-limit clause.** `IsDerivedLimit` fixes the apex to the localized actual Kan cone and fixes every localized cone leg through `strictDiagramComparison`; terminality is in the coherent cone category. It does not replace the cone by an arbitrary map or assert a final object in the comma category.
11. **Mapping complexes.** The final quantified clause ranges over arbitrary representatives, K-injective replacements `i` and `j`, and asserts `QuasiIso` for the canonical `mapHomComplex` followed by the coefficient Hom comparison. This is the node's equivalence on derived mapping complexes, with the full Hom differential and composition retained.
12. **Naturality and lower bounds.** `IsSquareNatural` quantifies commutative squares of the same five local-equivalence hypotheses and concludes both restriction and inverse coherent naturality equations. The same `a` occurs on both representative categories and in both preservation witnesses.

Edge cases checked: empty site or empty index categories are allowed; the pointwise and descent quantifiers then have their ordinary empty meanings. Zero rings, zero modules, zero complexes, and empty families are admitted. The empty comma category is handled by the actual Kan limit/cone, without a nonempty-index assumption. Negative, zero, and positive values of `a` are all allowed. Non-subcanonical sites and sites without fibre products remain in scope because matching is formed in presheaves and only sheafified afterward. Identity functors and identity squares are allowed, and local fullness/faithfulness do not imply global full faithfulness.

I reran the required searches with `msearch.py` (LeanFinder, Loogle, and LeanSearch) and direct `rg` searches in Mathlib, `WeilConjectures/`, and the project's `lean/Sheaf/`. They found only ordinary dense-subsite/sheaf equivalences and primitive simplicial, nerve, and hypercover declarations; no declaration states this enhanced comparison or the concrete presentation. The dependency declarations were opened and checked: Mathlib `presheafToSheaf`, `FormalCoproduct`, and `SimplicialObject`, the project's proper-face matching definition, the enhanced cone/localization interfaces, and the coefficient Hom map all are the declarations actually used. No repair note exists, no existing declaration matches, and no citer requires a correction audit.

No mismatch was found. I changed no Lean or DAG statement text. Both modules recompiled separately through `scompile.py` with no errors or warnings; the node copy's `lean.statement` remains verbatim equal to the theorem signature.
