## Worker report

Item: `lem-coef-simplicial-localization-comparison-calculus`, Q02, 2026-10-17.
Module: `Sheaf.CategoryTheory.SimplicialLocalizationComparisonCalculus`.
Namespace: `CategoryTheory.SimplicialLocalizationCalculus`.

The main declaration is `simplicial_localization_comparison_calculus`. It asserts
existence of the combinatorial Bergner model, functorial enriched localization by
the specified derived pushout, localization at equivalences, the bifibrant comparison
and its two naturality cases, both mapping-limit assertions, and the Kan-tower clause.
The definitions used to express these clauses are transparent constructions or
explicitly characterized data structures. No object or map is chosen from a postponed
existence theorem. The two named theorem proofs are `sorry`, as required for stage 2:
the main theorem and the preservation proof `fibrantMap_preserves` used by the explicit
restriction `fibrantMap`. The latter is the item's own functoriality clause, specifically
the vertex calculation of proof step 6; its docstring gives that calculation.

The node's statement and all its other fields are unchanged; only `lean` is set.
No statement correction, new node ordependency-module repair was needed.
No repair note for this item exists in `coord/repair-notes/`.

### Hypotheses and clauses matched to Lean

| Node text | Lean rendering |
| --- | --- |
| Enlarge universes so categories are small | The independent universes `w` for model objects and `u` for their enriched mapping simplicial sets are retained. `liftBundle C : SCat.{max u w}` uses objects `ULift.{u} C`, mapping sets `SSet.uliftFunctor.{w}.obj (x.down ⟶[SSet.{u}] y.down)`, and lifted identities/composition. This is only size transport, with an explicit inverse on every simplex, not a replacement of mapping spaces by derived ones. |
| Simplicial model category, combinatorial as in the projective dependency | `Category.{u} M`, `ModelCategory M`, `SimplicialCategory M`, `SimplicialTensorCotensor M`, `CombinatorialModelCategory.{w,u,u} M`, and `SimplicialModelLocalization.SatisfiesSM7 M`, in `ModelComparisons`. For naturality these same hypotheses are imposed on both model categories. |
| Small simplicial categories and enriched functors | The recorded `SCat`, `sCatCategory` and `underlying` from `CoherentNerveInfrastructure`, already used by the interval-lifting dependency. Homs in `SCat` are enriched functors with arbitrary object maps. |
| DK equivalence: mapping weak equivalences and equivalence on components | Existing `DwyerKanEquivalence`, read in `CoherentNerveComparison`: mappingwise `Enhanced.IsWeakHomotopyEquivalence` and `PiZeroEquivalence`, whose clauses are bijectivity on mapping components and essential surjectivity on the component category. No local Kan assumption is added. |
| Derived limits and pushouts for the DK model | The theorem supplies `B : BergnerModelData`, including the real Mathlib model axioms and its weak-equivalence identification. `IsDerivedLimit` explicitly compares the given cone with the ordinary limit of an objectwise weakly equivalent injectively fibrant replacement. `IsInjectivelyFibrant` is its lifting condition against all objectwise trivial cofibrations. `LocalizationPresentation.pushout` uses the existing `IsBergnerHomotopyPushout` predicate, defined via a projectively cofibrant span replacement and its colimit comparison. |
| Fibrant categories have Kan mapping sets | `∀ C, IsBergnerFibrant B C ↔ IsLocallyKan C`. The first predicate is precisely Mathlib's fibrant-object predicate for `B.model`; the second is the dependency's Kan condition on every mapping set. |
| Fibrations between fibrant categories: local Kan fibrations and equivalence lifting | The explicit theorem conjunct, under `IsLocallyKan C` and `IsLocallyKan D`, identifies the fibration class with `SSet.Bergner.IsLocalFibration p ∧ SSet.Bergner.LiftsEquivalenceVertices p`. These are the dependency's full signatures, including strict equality of the lifted target object and of the prescribed vertex. |
| Any set W of vertex arrows | `Pair.marked : MorphismProperty (underlying category)`, with no multiplicativity, identity, saturation or two-out-of-three assumptions. `Marks P` is exactly the dependent sum of endpoints and an arrow satisfying that predicate. |
| Walking arrow [1] and walking groupoid J | `walkingArrow = SSet.Bergner.bundle (SSet.Bergner.U (𝟙_ SSet))`; `walkingGroupoid` has the same two labels and terminal mapping simplicial sets for all four ordered pairs; `adjoinInverse` preserves labels and sends each mapping set to its unique map to the terminal mapping set. |
| Localization is the derived pushout of the displayed coproduct span | `LocalizationPresentation` supplies each marked walking-arrow functor, fixes its source/target and its entire forward simplicial map (`forward`), and supplies coproduct cocones with `IsColimit`. It first factors `adjoinInverse` through `resolvedGroupoid`, with a cofibration `inclusion`, weak equivalence `resolution`, and exact factorization equality. Its coproduct thus represents the original walking-groupoid leg up to objectwise weak equivalence. The `pushout` field specifies the model homotopy pushout of this equivalent span, with the localization unit as its C-leg. This is the derived pushout of the original span; requiring a strict map from the discrete walking groupoid into the localized category would prematurely impose strict inverses. All maps from the coproducts are fixed summand by summand. |
| Functoriality for enriched functors preserving marked arrows | `PairHom.functor` and `PairHom.preserves` form `pairCategory`. `LocalizationSystem.functor : Pair ⥤ SCat` and its `unit : forget ⟶ functor` give identities, composition and the natural canonical maps; every unit has its specified `LocalizationPresentation`. These data are existentially asserted, never extracted by a `Nonempty` choice. |
| Marked arrows already invertible in pi-zero imply unit DK | The first localization conclusion quantifies every `P`, assumes `∀ x y f, P.marked f → IsPiZeroIso f`, and concludes `DwyerKanEquivalence (L.unit.app P)`. The existing invertibility predicate requires a two-sided inverse modulo mapping components, not a strict inverse. |
| Fibrant objects and exactly their weak equivalences | `fibrantPair M` uses the actual Mathlib `FibrantObject M` full subcategory, size-transported by `liftBundle`. Its marking reads the vertex, removes `ULift`, applies `homEquiv'.symm`, then tests the original model weak-equivalence predicate. |
| Bifibrant full enriched subcategory and canonical comparison | `liftBundle (BifibrantObject M)` retains the actual full-subcategory mapping simplicial sets. `bifibrantInclusion` includes objects and is identity on all these mapping sets; `comparison L M` is literally this inclusion followed by `L.unit.app (fibrantPair M)`. The first conjunct of `ModelComparisons` says this particular map is DK. |
| Naturality if T preserves bifibrant, fibrant and weak-equivalence objects/arrows | `T` is an enriched functor; `hF` preserves fibrant objects; `hW : PreservesFibrantWeakEquivalences T` tests each weak equivalence with fibrant endpoints. With `hBF`, the final equation of `ModelComparisons` is the comparison square, using the actual `restrict T ... hBF` on bifibrant objects and `L.functor.map (fibrantMap T hF hW)` on localized fibrant categories. Weak equivalences outside the fibrant subcategory are irrelevant to this restriction; the node explicitly permits this smaller preservation hypothesis in the next sentence. |
| If T only preserves fibrant objects and their weak equivalences, it still localizes | `fibrantMap T hF hW` is an explicit marked enriched functor with the same mapping maps as T, transported by `ULift`. `L.functor.map` supplies its induced localization map before any `hBF` is bound. The first equation in the naturality conjunct records its commuting unit square. There is no bifibrant restriction without `hBF`, no Quillen condition on T, and no compatibility with a chosen cofibrant replacement. |
| Any small diagram H and enriched cone alpha | `HomotopyLimitClauses` quantifies `J : Type u`, `Category.{u} J`, `H : J ⥤ SCat`, and `c : Cone H`. This encodes exactly an enriched cone, without adding a chosen strict limit. For any strict limit, its universal property identifies the cone with the node's map `alpha : C ⟶ lim H`. |
| beta makes alpha beta homotopy limiting | The recognition conjunct binds `A : SCat`, `β : A ⟶ c.pt`, and assumes `IsDerivedLimit ... (c.extend β)`. Beta is neither assumed DK nor essentially surjective on C. |
| Iff every mapping cone is homotopy limiting | The conclusion is exactly `IsDerivedLimit ... c ↔ MappingLimitCondition c`. `MappingCone` retains every `H(j)(alpha_j x,alpha_j y)`, every transition map, the source `hom c.pt x y`, and every mapping-cone leg. Equality of the endpoint-dependent types is handled solely by `HEq`. `MappingLimitCondition` asserts existence of the actual mapping-cone presentation for each pair and the derived-limit property for every such presentation, so it cannot hold vacuously due to a missing mapping-cone interface. |
| In particular, mapping sets in a homotopy limit | The first conjunct of `HomotopyLimitClauses` is necessity without any auxiliary beta, exactly the separate mapping-set assertion. |
| Strict inverse limit of a Kan-fibration sequence computes its homotopy limit | `KanTowerClause` quantifies every `X : ℕᵒᵖ ⥤ SSet`, assumes `KanComplex` at every stage and `Fibration` of each successor transition, and says every strict limiting cone `c` satisfies `IsDerivedLimit ... c`. The index universe is independent of the mapping-set universe in the derived-limit interface, so ordinary `ℕᵒᵖ` is included. |
| No coherent-nerve theorem or slice-model assumption | Neither occurs in the theorem's binders, conclusions or proof input. Existing definitions imported through the projective and inversion modules are reused without invoking their downstream theorems. |

### Dependency declarations read and used

- `Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus`:
  `CategoryTheory.simplicial_projective_model_calculus`, full signature and proof
  docstring read. Its shared notions `CombinatorialModelCategory`,
  `SimplicialTensorCotensor`, `SatisfiesSM7`, `DwyerKanEquivalence`, and
  `simplicialUnderlyingFunctor` are reused; no copy is defined.
- `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`:
  `SSet.Bergner.simplicial_interval_lifting`, full signature and proof docstring read.
  Reuses `SCat`, `Two`, `U`, `bundle`, `IsLocalFibration` and
  `LiftsEquivalenceVertices`, including all endpoint equalities.
- `Sheaf.CategoryTheory.CoherentNerveInfrastructure`: existing `SCat`, `underlying`,
  `IsLocallyKan` and ordinary enriched-functor category structure.
- `Sheaf.CategoryTheory.CoherentNerveComparison`: definitions only,
  `DwyerKanEquivalence`, `PiZeroEquivalence`, `IsPiZeroIso`, `BergnerModelData`.
  The coherent-nerve comparison theorem is not used.
- `Sheaf.CategoryTheory.CofibrantSimplicialInversion`: existing
  `CofibrantSimplicialInversion.IsBergnerHomotopyPushout`, whose full definition was
  read; no inversion theorem is used.
- `Mathlib.AlgebraicTopology.ModelCategory.Bifibrant`: `FibrantObject`,
  `BifibrantObject`, `fibrantObjects`, `bifibrantObjects`; also Mathlib full-subcategory
  enriched instances and `homEquiv'` from the simplicial enrichment interface.
- Proof-only imports: `Sheaf.AlgebraicTopology.KanQuillenRightProper`,
  `Sheaf.AlgebraicTopology.SimplicialIntervalCellStability`,
  `Sheaf.CategoryTheory.EnrichedFunctorialFactorizations`, and
  `Sheaf.CategoryTheory.ReedyModelStructure`. Their relevant theorem signatures and
  source docstrings were read. The three proof nodes
  `lem-coef-simplicial-inversion-universal-property`,
  `lem-coef-simplicial-inversion-product-parameter`, and
  `lem-coef-combinatorial-injective-diagram-model` have no recorded Lean modules at
  writing time, so no nonexistent imports are added. Their proof steps are fully
  retained in the main theorem's docstring. Their absence is not a statement dependency.

The imported downstream modules supply already existing definitions, not assumptions.
Adding this item as a proof import to those modules would create import cycles and
must be skipped by the maintainer's usual proof-import cycle check. This delivery
changes none of those shared modules.

### Edge cases checked before and during writing

- Empty marking, empty simplicial category, coincident endpoints, identity markings,
  arbitrary nonsaturated/nonmultiplicative markings, and already pi-zero-invertible
  arrows. `Marks` and the empty coproducts admit these cases without hypotheses.
- Empty diagram J: the mapping condition alone is vacuous for an empty C, which is
  why the auxiliary beta hypothesis must be retained in the recognition direction.
  The actual Lean retains it. A homotopy-terminal B cannot map to an empty C.
- A singleton diagram and an identity beta give the expected necessity and sufficiency.
- Empty Kan mapping sets and empty tower stages are included. Kan fibrations need
  not be surjective on vertices. No `Nonempty` hypothesis on mapping sets appears.
- A noncofibrant fibrant object is included in `fibrantPair`; the comparison domain is
  only the actual bifibrant subcategory, as in the source.
- A functor preserving fibrants but not cofibrants obtains its localized functor
  without access to `restrict` on bifibrants. The latter is only supplied after hBF.
- Object universe w larger or smaller than mapping universe u: the explicit object
  and simplex lifts transport both to `max u w`, without imposing w = u. All
  quantification over model objects and their model structures keeps those universes
  separate. No mere small object-type model category with equally large tensor size
  is silently substituted for an ordinary large combinatorial model category.

### Searches and source checks

Prescribed msearch searches (also recorded by the wrapper in `searches.jsonl`):

1. LeanFinder: `simplicial enriched localization comparison bifibrant objects homotopy limit mapping spaces`.
   Eight hits, all ordinary cofibrant homotopy-category localization interfaces;
   none gives this enriched localization or mapping-limit theorem.
2. Loogle: `DwyerKanEquivalence`. Zero hits, unknown Mathlib identifier. The project's
   existing predicate was found and reused instead.
3. Mathlib grep: `DwyerKan|Bergner|homotopyLimit`, `CategoryTheory`.
   Zero hits.
4. LeanSearch: `Dwyer Kan simplicial localization bifibrant comparison homotopy limits`.
   Eight hits: Mathlib bifibrant/fibrant object interfaces, ordinary cofibrant
   localization and a pointwise Kan-extension-derived-functor limit. No exact match.

Additional `rg` searches of the read-only upstream `WeilConjectures/` for
`DwyerKan|simplicial.*localization|homotopyLimit`, and the required recursive item-ID
search, found no matching upstream declaration. Searches in `lean/Sheaf` found
ordinary/infinity localization statements, existing DK free-resolution and cofibrant
inversion interfaces, the coherent-nerve definitions, and a path model for space
homotopy limits. Their statements were read: they do not give this node. In particular
`FibrantSubcategoryLocalization` localizes an ordinary nerve rather than the actual
simplicial enrichment; `SimplicialIntervalLocalization` has the coherent-nerve conclusion;
`DkCofibrantLocalizationComparison` concerns ordinary relative categories; and
`CofibrantSimplicialInversion` concerns degreewise localization of cofibrant pairs.
Its model homotopy-pushout definition is reused, not copied.
Name searches in `dag/lean_names_upstream.json`, upstream, and project Lean found no
collision with the new namespace or main declaration.

The cited HTT PDF was opened online at the source URL; the relevant definitions and
statements at A.3.2.27--28, A.3.5.1 and A.3.6.17 were inspected. A.3.5.1 resolves the
walking-arrow-to-groupoid map by a cofibration, exactly as the presentation here.
The source proof's ten steps are carried in full into the main theorem's docstring.
There is no statement dispute.

### Validation

All compilation used the prescribed `scompile.py Q02
lem-coef-simplicial-localization-comparison-calculus <module>` wrapper. The full
module compiles in both its sandbox and final module-path contexts, with explicit
universes and `autoImplicit false`; only the required theorem proofs are postponed.
The final dry-run result is recorded below after the prescribed delivery check.

Final validation: the prescribed `deliver2.py Q02
lem-coef-simplicial-localization-comparison-calculus --no-push` printed
`OK (dry run)` for commit `6c5fe758ad`: the module compiled cleanly and preflight
passed except for the independent second-reading section, which the next reader
must supply. Nothing was pushed. This worker has not written a second reading.

## Second reading by Q02

I read the node statement, its HTT source places (Notation A.3.5.1; Remark A.3.2.14 and
Example A.3.2.18; Proposition A.3.2.27 and Corollary A.3.2.28; Lemma A.3.6.17), both
recorded statement dependencies, and every declaration used by the module. The rendered
Lean clauses match item by item:

1. The theorem introduces `B : BergnerModelData.{max u w}`, with the independent object
   and mapping universes, and requires `CombinatorialModelCategory` for `B.model`.
2. It states fibrancy exactly as `IsBergnerFibrant B C ↔ IsLocallyKan C` and gives the
   fibration characterization for locally Kan `C,D` as
   `IsLocalFibration p ∧ LiftsEquivalenceVertices p`.
3. It existentially supplies `L : LocalizationSystem B`; `Pair`, `Marks`, the walking
   arrow/groupoid, the resolved cofibration/weak-equivalence factorization, coproduct
   colimits, and `IsBergnerHomotopyPushout` specify the derived pushout localization and
   its canonical unit. `PairHom` and `LocalizationSystem.functor` give functoriality.
4. For every marking whose arrows satisfy `IsPiZeroIso`, it concludes DK equivalence of
   `L.unit.app P`.
5. `fibrantPair` uses the actual full enriched fibrant subcategory and exactly model weak
   equivalences; `comparison` is the actual bifibrant full-subcategory inclusion followed
   by the localization unit. `ModelComparisons` states its DK equivalence and the two
   naturality equations, with the second restriction quantified only after `hBF`.
6. `fibrantMap` is available under preservation of fibrant objects and their fibrant weak
   equivalences alone, so no bifibrant or Quillen hypothesis is added in that clause.
7. `HomotopyLimitClauses` quantifies every small `J : Type u`, enriched diagram and cone,
   includes the auxiliary `β` hypothesis for recognition, and states both mapping-cone
   necessity and the iff criterion through `IsDerivedLimit`.
8. `KanTowerClause` quantifies every `X : ℕᵒᵖ ⥤ SSet`, assumes Kan stages and fibrational
   successor maps, and applies to every strict limiting cone. The final theorem packages
   all clauses in the same order and has no coherent-nerve or slice-model assumption.

Edge cases checked: empty markings and diagrams, empty/coincident simplicial-category
objects, identity and already-invertible markings, zero/empty mapping simplicial sets,
non-surjective Kan-tower transitions, singleton diagrams, `n = 0`, and independent
object/mapping universes. No `Nonempty` or saturation hypothesis is present; the auxiliary
`β` is retained so the recognition direction cannot become vacuous.

I repeated the required LeanFinder/Loogle/LeanSearch and Mathlib/upstream/project `rg`
searches. No exact declaration exists; the reused notions are the recorded `SCat`,
`DwyerKanEquivalence`, `IsLocallyKan`, Bergner interval predicates, model structures,
and `IsBergnerHomotopyPushout`. No repair note, statement correction, new node, or
dependency-module repair was needed. The module compiled with the prescribed `scompile.py`;
there were no errors or warnings beyond the two named postponed theorem proofs. No mathematical mismatch was found, and the Lean source is unchanged. I restored the
complete `lean` metadata after a transient review edit, with all 27 declarations and the
main signature copied verbatim; no other node field was changed.


Independent search details: LeanFinder query `simplicial enriched mapping spaces bifibrant
localization derived inverse limits` returned eight enrichment/nerve/bifibrant interfaces;
Loogle `IsLocalization` returned twelve ring-localization interfaces; LeanSearch `homotopy
limit of a tower of Kan fibrations enriched categories` returned eight product-fibration
and conical-limit interfaces. None states this result. The independent `rg` search used
`homotopy.?limit|derived.?limit|localiz.*fibrant|bifibrant.*localiz|walking.?groupoid|injectively.?fibrant`
on Mathlib algebraic topology, upstream WeilConjectures, and project category theory.
I opened `FibrantSubcategoryLocalization.fibrant_subcategory_localization` (ordinary-nerve
coherent localization), `SSet.Enhanced.kan_fibration_tower_limit` (a coherent space-valued
tower result), and `DerivedHypersheafPresentation.IsDerivedLimit` (the image of a strict
cone in a chosen coherent localization). None supplies the full node or the ground-model
replacement predicate used here. Name searches in upstream Lean, project Lean and
`dag/lean_names_upstream.json` found no collision.

The new helpers belong to the item's own constructions, and their source/blueprint
references are present. The model-fibrant predicate's `letI` is inside a definition,
not a hidden let binder in the theorem statement. `fibrantMap_preserves` postpones only
a proof field; all mapping data of `fibrantMap`, `restrict`, `liftBundle`, and the
comparison are explicit. The ten-step main docstring retains every node proof step.
There are no new definition nodes or dependency modules to audit. Characteristic,
schemes, and ring finiteness do not occur in this abstract simplicial-category node.

Hypothesis audit: `Category.{u} M`, `ModelCategory M`, and `SimplicialCategory M`
are the actual category/model/enrichment hypotheses. The comparison's implications
`SimplicialTensorCotensor M`, `CombinatorialModelCategory.{w,u,u} M`, and
`SatisfiesSM7 M` exactly reproduce the recorded projective dependency's binders
(lines 254--258); there is no extra properness, cofibrancy, or fibrancy assumption
on the whole model category. `hF`, `hW`, then `hBF` occur in that order, and `hW`
only tests arrows with fibrant endpoints, as allowed by the node's smaller naturality
clause. The common ambient universes for M and N are supplied by universe enlargement;
`liftBundle` lifts both objects and every mapping simplex, retaining their original data.
For limits, `J : Type u` and `[Category.{u} J]` allow all diagrams small in the same
universe as the simplicial categories; `IsDerivedLimit` itself has independent diagram
universes, including ordinary `ℕᵒᵖ`. The marked set has no closure axioms. Verdict for
each of the eight object/conclusion checks above and these hypotheses: exact match.

Validation after the second reading: the prescribed `scompile.py` compiled sandbox and
library contexts cleanly. `deliver2.py --no-push` printed `OK (dry run)` at `36d48fca99`:
preflight passed and nothing was pushed. A direct JSON comparison with the shared base
confirmed that only `lean` differs, and the signature in `lean.statement` occurs verbatim
in the module.
