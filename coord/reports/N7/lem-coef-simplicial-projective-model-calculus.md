## Worker report

The module `Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus` states
`CategoryTheory.simplicial_projective_model_calculus` with `sorry`.  It introduces concrete
helper declarations in the same module for the notions absent from Mathlib or the recorded
statement dependencies: the enriched mapping pullback map, the simplicial model axiom,
small generating sets, combinatorial simplicial model categories, Dwyer--Kan equivalences,
enriched-end presentations, projective simplicial model structures, relative cofibrancy and
fibrancy, and simplicial Quillen-equivalence witnesses.  These helpers contain data and
universal properties; no data is selected by `sorry`.

The theorem renders the source clauses as follows.

* The binders `C`, `[Category.{v,u} C]`, `[ModelCategory C]`, `[SimplicialCategory C]`,
  `T`, and `hC` are the fixed universe, simplicial model, tensor/cotensor, and
  combinatorial hypotheses.  `CombinatorialSimplicialModelCategory` records a regular
  cardinal, local presentability, two small generating lifting systems, and the mapping
  axiom.  `SimplicialModelAxiom` uses the induced map
  `simplicialMappingPullbackMap i p`, requiring a fibration and weak equivalence when
  either input is a weak equivalence.
* The first conjunct quantifies every small `I` (`I : Type u` with its category and
  simplicial enrichment) and gives `Nonempty` of
  `ProjectiveSimplicialModelStructure`.  Its fields state objectwise weak equivalences and
  fibrations; objectwise tensor/cotensor; an actual `HasEnd` presentation of each mapping
  simplicial set; evaluation preservation of cofibrations and trivial cofibrations;
  cofibrant-fibrant evaluation; and the enriched free-diagram/evaluation adjunction with
  value `T.tensor (sHom i j) X`.
* The second conjunct quantifies a simplicial functor `v` and
  `DwyerKanEquivalence v`, whose fields are weak homotopy equivalences on mapping sets and
  a path-component equivalence.  For projective structures `P` and `Q`, it supplies a left
  functor `L`, a right restriction witness, and a `SimplicialQuillenEquivalence`.  The latter
  has an adjunction, tensor compatibility, and the exact cofibrant/fibrant weak-equivalence
  criterion for `L.map f` and its adjoint.
* No local Kan-complex hypothesis occurs in the theorem binders or helper structures.

Recorded dependency declarations used (all imported):

* `Sheaf.AlgebraicTopology.SimplicialBoundaryCollapseTest`,
  `CategoryTheory.simplicial_boundary_collapse_test`;
* `Sheaf.CategoryTheory.SimplicialTensorCotensor`,
  `CategoryTheory.SimplicialTensorCotensor` and `CategoryTheory.SimplicialTensorCotensor.tensorMap`;
* `Sheaf.AlgebraicTopology.KanQuillenRightProper`,
  `SSet.KanQuillen.right_proper_kan_quillen` and its listed helper declarations;
* `Sheaf.CategoryTheory.EnhancedDiagramsCones`,
  `SSet.Enhanced.coneCategory` and its listed helper declarations.

Edge cases checked: the empty simplicial indexing category is covered by the universal
quantifier and empty products/ends; a one-object category gives the ordinary model category;
`n = 0` is covered by the Kan-model conventions in the boundary-collapse dependency; and
no nonemptiness or local Kan assumption is added for either indexing category.

Searches: the node's recorded LeanFinder, Loogle, grep, and LeanSearch searches were
reviewed.  They return ordinary projective-object preservation, simplicial thickening, and
existing localization declarations, but no enriched projective diagram model structure or
Dwyer--Kan change-of-index theorem.  Additional source searches were run with `rg` over
`WeilConjectures/` and `lean/Sheaf/`; no declaration mentioning
`lem-coef-simplicial-projective-model-calculus` or an equivalent theorem was found.

No statement correction, dependency-module repair, `STATEMENT-DISPUTED`, or new DAG node
was needed.  The helper declarations are listed in the item's `lean.declarations` record.

## Second reading by N7

I reread the node statement, its source place (Lurie, *Higher Topos Theory*,
A.3.3.2 and Remarks A.3.3.4--A.3.3.5, Propositions A.3.3.7--A.3.3.8,
pp. 870--873), and the complete module.  The source explicitly takes a
combinatorial simplicial-enriched model category and the category of simplicial
enriched functors from a small simplicial category; Proposition A.3.3.7 uses
composition, enriched left Kan extension, and restriction, and Proposition
A.3.3.8 gives the Quillen equivalence for an equivalence of small enriched
categories.

The statement is rendered item by item as follows.

* The ambient coefficient category is `C : Type w` with
  `[Category.{v,w} C]`, `[ModelCategory C]`, `[SimplicialCategory C]`, and a
  chosen `T : SimplicialTensorCotensor C`; `hC` is
  `CombinatorialSimplicialModelCategory C T`.  Its fields are a regular
  `Cardinal.{u}`, local presentability, two small generating lifting systems,
  and `SimplicialModelAxiom C T`.  Thus the small indexing universe `u` is
  independent of the ambient coefficient universe `w`.
* `simplicialMappingPullbackMap` is the enriched mapping pullback map.  The
  `SimplicialModelAxiom` field says it is a fibration for a cofibration and a
  fibration, and a weak homotopy equivalence when either input is a weak
  equivalence.
* For each `I : Type u` with `[Category.{v,u} I]` and
  `[SimplicialCategory I]`, `ProjectiveSimplicialModelStructure` is on
  `EnrichedFunctor SSet.{v} I C`, so its objects are genuinely simplicial
  enriched functors and its arrows are enriched natural transformations.  The
  structure records objectwise weak equivalences and fibrations, pointwise
  tensor/cotensor, the enriched-end mapping object, evaluation preservation of
  cofibrations and trivial cofibrations, bifibrant evaluation, and the actual
  enriched free/evaluation adjunction with value `T.tensor (sHom i j) X`.
  The first conjunct of the theorem universally quantifies this `I` and gives
  `Nonempty` of that structure.
* The second conjunct binds small `I,J`, a simplicial enriched functor
  `v : EnrichedFunctor SSet.{v} I J`, and the canonical
  `CategoryTheory.DwyerKanEquivalence v` from
  `Sheaf.CategoryTheory.CoherentNerveComparison`.  That predicate is local
  weak homotopy equivalence together with bijectivity on mapping-set `π₀` and
  essential surjectivity in the resulting path-component category, exactly
  the node's DK clause.  For projective structures `P,Q`, the existential
  `L,R,restriction` has `R = restriction`, an adjunction, tensor compatibility
  by an isomorphism, and the node's cofibrant-source/fibrant-target
  weak-equivalence criterion for the adjoint map.
* No local Kan-complex hypothesis is present.  `SimplicialModelAxiom` and the
  imported Kan-model conventions supply the simplicial-set model structure.

The first worker's ordinary `Functor I C` encoding was a real mismatch: it did
not state the enriched diagram category in the source.  I changed every diagram
category, free/evaluation functor, mapping object, relative cofibrancy/fibrancy,
and Quillen witness to use Mathlib's `EnrichedFunctor SSet.{v} I C`, and added
`enrichedComponent` to transport enriched natural-transformation components
through the canonical `ForgetEnrichment.equivFunctor`.  The worker also defined
private `PiZeroEquivalence` and `DwyerKanEquivalence` structures requiring an
ordinary equivalence `I ≌ J`; this was both a second definition and stronger
than the node's path-component equivalence.  I removed both and use the
existing canonical `CategoryTheory.DwyerKanEquivalence`, adding its landed node
`lem-coef-coherent-nerve-comparison` to `stmt_deps`.  The canonical superclass
instance from `SimplicialCategory` to `EnrichedCategory` is recorded as
`simplicialCategoryEnrichedCategory`.  I separated the small index universe
from the ambient coefficient universe and changed strict tensor equality in the
Quillen witness to tensor compatibility by an isomorphism.

Edge cases checked: the universal quantifier admits the empty indexing
category and empty mapping simplicial sets; a one-object simplicial category
reduces to the ordinary model-category case; empty products and ends are
allowed; `n = 0` follows the imported Kan-model conventions; the zero object
of `C` is not excluded; no characteristic, nonemptiness, or local Kan
assumption is introduced; and the independent universes `u`, `v`, and `w`
cover the node's small/ambient convention.

Searches were repeated with `rg` over `lean/Sheaf/CategoryTheory`, the
slopmaster2 `WeilConjectures` tree, and Mathlib, and with LeanFinder, Loogle,
and LeanSearch queries for enriched projective model structures, DK
invariance, and simplicial Quillen equivalences.  The only matching DK notion
is the existing `CategoryTheory.DwyerKanEquivalence` in
`Sheaf.CategoryTheory.CoherentNerveComparison`; no existing projective
simplicial diagram-calculus theorem or duplicate helper was found.  The
repaired module compiles via `scompile.py` with only the permitted `sorry`
proof.

### Resumed second reading, 2026-10-17

This continuation rechecked the retained file against current dependencies. The
preceding review is retained as history; its claims about the three independent
universes, the ordinary `EnrichedFunctor` arrow category, the arbitrary restriction
witness, the new combinatorial/SM7 definitions, and completed validation are
superseded by the following final review. There is no natural-language statement
correction: the node and HTT agree. Only `lean` and `stmt_deps` change.

Final clause-by-clause list and verdicts:

1. **Universes and objects.** The source's small universe is `u`; `I,J : Type u`,
   their homs, and their mapping simplicial sets all live there. The coefficient
   category is `C : Type w`, `[Category.{u} C]`, `[SimplicialCategory C]`.
   The object universe `w` is independent. This encodes arbitrary large categories
   enriched in small simplicial sets, with no equation between ambient and small
   universes. **Matches.** The earlier independent index and mapping universes did
   not encode the source's single meaning of small.
2. **Model, tensor, cotensor and SM7 hypotheses.** `[ModelCategory C]` is Mathlib's
   actual model structure. `T : SimplicialTensorCotensor C` has the dependency's
   universal elements and internal-Hom representing isomorphisms. The existing
   `SimplicialModelLocalization.SatisfiesSM7 C` uses the canonical pullback corner,
   Kan fibrations (`J.rlp`), and realization weak homotopy equivalences when either
   input is trivial. **Matches.** Removed the duplicate corner and SM7 definitions.
3. **Combinatoriality.** `CombinatorialModelCategory.{w,u,u} C`, read in
   `Sheaf.CategoryTheory.ModelColimitLocalizationComparison`, uses Mathlib
   `IsLocallyPresentable.{u}`, small generators via the correct `llp(rlp)`
   equalities, and functorial factorizations. This is the source's locally
   presentable cofibrantly generated model convention. **Matches.** The old
   `HasSmallGeneratingSets` incorrectly made the left class a right lifting
   class and the right class a left lifting class. Removed it and the duplicate
   combinatorial structure; added the landed owning node to `stmt_deps`.
4. **Small simplicial categories and DK equivalence.** Mathlib `SimplicialCategory`
   includes units and associative simplicial composition; ordinary arrows are its
   mapping vertices. `DwyerKanEquivalence v` is the existing predicate in
   `CoherentNerveComparison`: local realization weak equivalences, bijections on
   mapping pi-zero, and essential surjectivity with inverse composites equal on
   pi-zero. **Matches.** No ordinary-category equivalence or local Kan condition
   is required.
5. **The diagram category and its mapping end.** `SimplicialDiagramEnrichment`
   supplies an enrichment of the enriched functor objects. Its `represents` field
   is a presheaf isomorphism with Mathlib `enrichedNatTransYoneda F G`, which
   represents *graded enriched* natural transformations, including their full
   simplicial naturality. `represents_projection` pins this isomorphism to the end
   projections, and `projection_id`/`projection_comp` fix the actual identity and
   composition. `E.Diagrams` is `ForgetEnrichment` of this enrichment, so arrows
   are its vertices, genuinely enriched transformations. **Matches.** The earlier
   ordinary `HasEnd` of an arbitrary diagram with only object values specified
   imposed neither enriched naturality nor canonical diagram maps. Moreover,
   Mathlib's current ordinary category on `EnrichedFunctor` stores transformations
   of underlying functors; it must not be used here. Both mismatches are repaired.
6. **Existence of a combinatorial simplicial projective model.** The first theorem
   conjunct gives `E` and `Nonempty (ProjectiveSimplicialModelStructure T E)` for
   every small index. This class extends actual `ModelCategory E.Diagrams`,
   includes canonical `CombinatorialModelCategory` and `SatisfiesSM7`, and gives
   exact objectwise iff statements for weak equivalences and fibrations.
   **Matches.** The retained structure omitted the conclusion's combinatoriality
   and SM7; both are now present.
7. **Pointwise tensor and cotensor.** `tensorCotensor` has the dependency's full
   representing universal properties; `tensor_objectwise`, `cotensor_objectwise`,
   and the two universal-element normalization fields pin the objects and actions
   pointwise. `HEq` only accommodates the separately stated equalities of their
   codomain objects. **Matches.** Arbitrary object-valued operations have been
   replaced by actual tensors/cotensors with their universal elements.
8. **Evaluation.** `component` is induced by the canonical end projection.
   `evaluation_cofibration` and `evaluation_trivial_cofibration` give both asserted
   preservation statements. `cofibrant_fibrant_evaluation` gives both object
   properties. The evaluation functor is fixed on objects *and maps* by
   `evaluation_object`/`evaluation_map`. **Matches.** The prior functor had only
   its objects specified.
9. **Enriched free/evaluation adjunction.** `free_diagram_objectwise` gives
   `I(i,j) tensor X`; `free_diagram_left_adjoint` supplies the actual adjunction.
   Its unit is normalized by `free_diagram_unit_normalization` and the enriched
   adjunction is the canonical map formed from evaluation and precomposition by
   that unit, asserted `IsIso`. This specifies the entire simplicial adjunction,
   not an arbitrary isomorphism on vertices. **Matches.**
10. **Change of index.** The second conjunct binds an arbitrary DK simplicial
    functor `v`, both enriched-end presentations, and both projective structures.
    `SimplicialQuillenEquivalence v P Q` gives an enriched restriction pinned by
    `restriction_object` to `EnrichedFunctor.comp SSet v F`, and by
    `restriction_mapping` to evaluation at `v.obj i` on every mapping object.
    `simplicialUnderlyingFunctor` is exactly Mathlib's canonical transport of its
    forgetful functor. `adjunction` and `enriched_adjunction` characterize its
    enriched left adjoint, hence enriched left Kan extension. `left_quillen`
    explicitly preserves cofibrations and trivial cofibrations. **Matches.** The
    retained restriction was existentially arbitrary and did not mention `v`;
    the prior witness also omitted the Quillen preservation condition.
11. **Quillen-equivalence test.** `quillen_criterion` quantifies each source,
    target and map in the node's order, assumes cofibrancy for the source in
    `P` and fibrancy for the target in `Q`, and compares the weak equivalence of
    the map with that of its actual adjunct under the displayed adjunction.
    All model fields are explicitly those of `P,Q`. **Matches.**
12. **No local Kan requirement.** Neither index has a Kan-complex assumption.
    Only the coefficient model's SM7 and the canonical simplicial-set model
    conventions are used. **Matches.**

Edge cases: empty `I` and `J` are admitted, as are empty mapping sets; no
nonempty index or nonempty hom is assumed. The representable graded-transformation
presheaf gives the terminal mapping end for empty indices. A DK map out of the
empty category forces an empty target. The one-object *unit-hom* category gives
`C`; a general one-object simplicial category instead gives objects with its
endomorphism action (correcting the earlier overly broad sentence). Zero objects
are permitted; no coefficient field or characteristic occurs; degree zero and
all higher simplices remain in the full presheaf/SM7 formulas. No site or scheme
hypotheses occur in this generic node.

Independent searches in this continuation: LeanFinder query
"Combinatorial simplicial model category enriched functor projective model
structure enriched natural transformation object" returned simplicial-object
instances and the ordinary nerve, not this theorem. Loogle query
`"EnrichedFunctor", "comp"` returned the canonical composition and forgetful
transport, which are used. LeanSearch query "enriched natural transformations
representing presheaf graded natural transformations" returned `GradedNatTrans`
and the ordinary `EnrichedNatTrans`; reading their source exposed the crucial
arrow-category distinction. `rg` over Mathlib, slopmaster2 `WeilConjectures`, and
project `lean/Sheaf` found the landed `CombinatorialModelCategory`, `SatisfiesSM7`,
and DK predicate, all reused, and no full statement matching this node. Read
Mathlib `Enriched/Basic.lean` (especially `GradedNatTrans` and
`enrichedNatTransYoneda`), `Enriched/Ordinary/Basic.lean`,
`Enriched/FunctorCategory.lean`, `SimplicialCategory/Basic.lean`,
`ModelCategory/Basic.lean`, and `Presentable/LocallyPresentable.lean`.

The downstream `EnrichedRectification.IsFunctorEnd` was also opened: it is
specialized to bundled `SCat`, and importing its theorem-owning module would
reverse the proof dependency on this item. The helper here is instead a chosen
enrichment representing Mathlib's existing graded-transformation presheaf,
without copying that predicate or the graded-transformation notion. Similarly,
SM7 and DK are reused by **definition-only imports** from their existing owning
modules; their owning *theorems* are not mathematical prerequisites here. Adding
those theorem nodes to `stmt_deps` would close the explicit path through
coherent nerve, pinched rigidification, right straightening fibre comparison,
and unmarked straightening back to this item. No theorem from that path is used
in the statement or proof plan. The new acyclic `stmt_deps` addition is only
`lem-coef-model-colimit-localization-comparison` for its combinatorial definition.

No new DAG node, dependency-module repair, statement correction, or extra theorem
is delivered. The sole postponed proof is
`CategoryTheory.simplicial_projective_model_calculus`. Every helper has real
data or a universal property; every declaration has its source/blueprint
docstring. Expanded the theorem docstring to all eighteen node proof steps and
imported every currently stated proof dependency (Mathlib leaves included).
Removed the redundant superclass instance and all unused old helper records.
The final file has bound universes/variables, no lines over 100 characters,
and `lean.statement` is copied verbatim from its signature. Final `scompile.py`
validation passed both sandbox and library-file checks without warnings.

Final preflight race repair: the successful dry run used a base on which
`lem-coef-model-colimit-localization-comparison` did not reach this item.
The subsequent delivery preflight, on base `c6753b8e1`, detected that its current
proof dependencies now reach this item. Removed that `stmt_deps` addition as
well; the combinatorial *definition* is still reused by the same existing
import. Thus the final node's `stmt_deps` is unchanged from the original, and
**all three** canonical combinatorial/SM7/DK helpers are definition-only imports
whose owning theorem statements are not prerequisites. The earlier assertion
that the combinatorial node addition is acyclic is superseded by this current
server diagnostic. This removes the dependency cycle without restating a
notion or changing a Lean declaration. The compiled file is unchanged.
