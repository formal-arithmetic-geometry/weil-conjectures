## Worker report

The delivery adds `Sheaf.CategoryTheory.SimplicialSmallChunks.lean`.  Its main
statement is `CategoryTheory.simplicial_small_chunks`; the node's `lean` record
contains its exact Lean signature.  The module also records the notions needed to
render every clause of the source statement:

* `EnrichedModelFactorization` packages an enriched functor on the arrow category,
  its two factor maps, their composite equation, the left and right model classes,
  and both naturality equalities as equalities of simplicial maps.  This is the
  enriched-functorial choice required by the chunk definition, using the same
  `ComposableArrows`/`enrichedHomπ` interface as
  `CategoryTheory.exists_enriched_functorial_factorization`.
* `SimplicialChunk` has an object property `carrier`, a trivial-cofibration/fibration
  product factorization and a cofibration/trivial-fibration coproduct factorization,
  and closure under every finite `Fin n` family of maps.  The middle objects of the
  recorded factorizations are required to lie in `carrier`; the factorization fields
  supply the corresponding maps and class conditions.  `n = 0` is included by the
  `Fin n` quantification.
* `SimplicialChunk.cf` is the requested `U^{cf}` object property,
  `carrier X ∧ IsCofibrant X ∧ IsFibrant X`.
* `IsIChunk U T I E P` installs the enriched diagram category and the projective
  model structure `P`, and says that a `SimplicialChunk` has precisely the carrier
  `∀ i, U (F i)`.  Thus it is the full subcategory of diagrams whose values are in U.

The theorem hypotheses render the statement's fixed universe, model-category,
simplicial-enrichment, tensor/cotensor, combinatorial, and SM7 assumptions as
`[Category.{u} A]`, `[ModelCategory A]`, `[SimplicialCategory A]`, `T`, `hC`, and
`hSM7`.  `B : BergnerModelData` is the Bergner model data used by the explicit
cofibrancy premise on the small family `I : J → CoherentNerve.SCat`.  The first
conclusion quantifies every small simplicial indexing category and supplies its
enriched diagram enrichment and projective model structure, with `Set.univ` as the
carrier, proving that A itself is an I-chunk.  The second conclusion quantifies a
small family `J` of cofibrant simplicial categories and a small object property V,
then supplies a small U containing V, an I-chunk for every family member, and the
iff expressing equality of essential images in the localization at
`weakEquivalences A` via `MorphismProperty.Q`.

The helper declarations and the main theorem use the following dependency
interfaces: `CategoryTheory.SimplicialDiagramEnrichment`,
`CategoryTheory.SimplicialDiagramEnrichment.value`, and
`CategoryTheory.ProjectiveSimplicialModelStructure` from
`Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus`; and
`CategoryTheory.BergnerModelData` and `CategoryTheory.CoherentNerve.SCat` /
`underlying` from `Sheaf.CategoryTheory.CoherentNerveComparison`.  The enriched
factorization data follows the published
`CategoryTheory.exists_enriched_functorial_factorization` interface in
`Sheaf.CategoryTheory.EnrichedFunctorialFactorizations`.

Edge cases checked before writing and represented by the binders are: empty finite
families (`Fin 0`, hence the terminal product and initial coproduct), an empty V
(the essential-image iff then permits U empty), an empty indexing category (the
universal value condition is vacuous), and arbitrary zero/initial/terminal objects
(the model category supplies the finite limits and colimits).  No nonemptiness or
cofibrancy of A's objects is added.

Searches made:

* `msearch.py Q37 lem-coef-simplicial-small-chunks leanfinder` for enriched
  factorization-closed chunks: no declaration states simultaneous chunks;
  returned hits were ordinary model-category factorization or smallness facts.
* `msearch.py ... loogle "ModelCategory, Factorization"`: only ordinary
  `ModelCategory` factorization instances were returned.
* `msearch.py ... grep "chunk|enriched.*factorization|simplicial.*factorization"`:
  only unrelated graph/list chunk declarations were found.
* `rg` over `lean/Sheaf`, `WeilConjectures/`, and Mathlib for `Chunk`, enriched
  factorization, and simplicial model terms: no existing chunk notion or theorem.
  The existing project declarations found were the two dependency interfaces
  recorded above and the generic enriched-factorization theorem, which are imported
  and used rather than copied.
* `grep -rl "lem-coef-simplicial-small-chunks" dag/nodes` found only this node;
  no previously recorded Lean declaration exists.  `coord/repair-notes` has no
  repair note for this item.

The module compiles cleanly with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q37 lem-coef-simplicial-small-chunks`
(the expected `sorry` warning is suppressed by the module option).  No
`STATEMENT-DISPUTED` flag or node correction is needed.


## Second reading by Q37

I independently read the node, its eight proof steps, the delivered module, both
statement-dependency nodes and their actual source declarations. I also read the
recorded enriched-factorization theorem and the Mathlib interfaces used below.
The worker report above is retained as the account of the original draft; the
corrections in this section supersede its descriptions of global factorization
data, the objectwise essential-image iff, and the missing ambient chunk condition.

Source verification: the node cites no Stacks statement. I opened the cited
[HTT PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf), and read the beginning
of A.3.4, Definition A.3.4.1(a)--(b), Remark A.3.4.2, Example A.3.4.4,
Definition A.3.4.9, and Lemma A.3.4.15 with its construction, printed
pp.884--885, 888, 890--891 (PDF pages 901--902, 905, 907--908).
The source's excellent enriching category is specialized here to simplicial sets;
the ambient category is combinatorial, enriched, tensored and cotensored and
satisfies SM7. The DAG statement agrees with this specialization, including both
factorization classes, enriched functoriality, empty families, simultaneous
closure and the essential-image clause. No statement correction is needed.

Object/hypothesis/conclusion checklist, item by item:

1. Fix the small universe and an ambient combinatorial simplicial model category
   A. Lean: `{A : Type w} [Category.{u} A] [ModelCategory A]
   [SimplicialCategory A]`, `T : SimplicialTensorCotensor A`,
   `hC : CombinatorialModelCategory.{w, u, u} A`, and
   `hSM7 : SimplicialModelLocalization.SatisfiesSM7 A`. Verdict: matches the
   conventions of the projective-model dependency. Object universe w remains
   independent of the small mapping/index universe u; A need not be small.
2. A chunk is a FULL simplicial subcategory U. Lean: `SimplicialChunk.carrier`
   is Mathlib's `ObjectProperty A`; its full subcategory inherits the unchanged
   mapping simplicial sets by Mathlib's enriched-full-subcategory instance.
   Verdict: exact; no non-full subcategory data.
3. For each finite family X -> Y_i with all objects in U, choose a trivial
   cofibration X -> Z and fibration Z -> product_i Y_i with Z in U.
   Lean: `SimplicialChunk.productFamilies U n` is the property of wide-span
   diagrams all of whose objects lie in U. `SimplicialChunkProductFactorization`
   has `middle`, `left`, `right`, `fac`, `left_mem`, `right_mem`, `middle_mem`.
   The right leg is `Pi.lift (right F)`; the component equations `fac` say
   exactly that its composite with `left F` is the original product map.
   Verdict: exact after repair, including endpoints outside U for the product.
4. For each finite family Y_i -> X with all objects in U, choose a cofibration
   coproduct_i Y_i -> Z and trivial fibration Z -> X with Z in U.
   Lean: `coproductFamilies` uses wide-cospan diagrams;
   `SimplicialChunkCoproductFactorization` has the analogous fields, with
   `cofibrations M (Sigma.desc (left F))` and
   `trivialFibrations M (right F)`. Verdict: exact after repair. Component
   equations give the coproduct factorization, with no requirement that the
   coproduct itself belong to U.
5. Both choices are functorial by SIMPLICIALLY ENRICHED functors on the finite
   families. Lean: each `middle` is an `EnrichedFunctor SSet` on the full
   subcategory of families; each pair of `left_natural`/`right_natural`
   equations is an equality of simplicial maps using `enrichedHomπ`,
   `eHomWhiskerLeft`, and `eHomWhiskerRight`. The two new named instances
   `simplicialChunkWideSpan`/`simplicialChunkWideCospan` install Mathlib's
   actual `enrichedOrdinaryCategory` end, not an arbitrary enrichment.
   Verdict: exact after replacing global-all-arrow factorization data. For
   each fixed finite shape, this imposes naturality for all transformations
   between families in U; extension to families outside U is not assumed.
6. Empty families are included. Lean: both factorization fields quantify
   `n : ℕ` without a positivity assumption. For n=0 the star diagram still
   has its distinguished object, and the product/coproduct leg is the
   terminal/initial map. Verdict: matches Remark A.3.4.2, providing both
   replacements inside U.
7. U^{cf} is U intersect the ambient bifibrant objects. Lean:
   `SimplicialChunk.cf := C.carrier ⊓ bifibrantObjects M` uses Mathlib's
   existing bifibrant predicate. Verdict: exact; added its missing source
   and blueprint docstring instead of leaving an undocumented helper.
8. For a small simplicial category I, U is an I-chunk if U is a chunk and
   U^I is a chunk of the projective model category. Lean: `IsIChunk` now
   takes `U : SimplicialChunk A` and asks for a diagram chunk whose carrier
   equals `fun F => ∀ i, U.carrier ((value F).obj i)`. E is
   `SimplicialDiagramEnrichment I A`, P is the existing
   `ProjectiveSimplicialModelStructure T E`; the definition installs their
   actual enrichment/model structure. Verdict: exact after repair; both
   parts of Definition A.3.4.9 are present.
9. The whole A is an I-chunk for every small I, without cofibrancy of I.
   Lean: the first conjunct quantifies `(I : Type u) [Category.{u} I]
   [SimplicialCategory I]`, gives `U : SimplicialChunk A` with
   `U.carrier = Set.univ`, and E, P, and `IsIChunk U T I E P`.
   Verdict: exact, including the ambient chunk witness omitted before.
10. Given a small family of small COFIBRANT simplicial categories.
    Lean: `(J : Type u) (I : J -> CoherentNerve.SCat.{u})`, with
    `∀ α, @IsCofibrant _ _ B.model.categoryWithCofibrations
      (B.model.cm1b.out (Discrete PEmpty)) (I α)`.
    B is the recorded `BergnerModelData`, with characterized Bergner model
    classes. The initial-object instance comes from this very model's
    finite colimits; cofibrancy is Mathlib's initial-map definition, not
    cofibrancy of every object or of the underlying ordinary category.
    Verdict: exact. Removed `[Small.{u} J]`, which was automatic for
    `J : Type u`, and replaced the theorem-signature `letI` with the
    explicit model-class and initial-object arguments.
11. Given a small full V, obtain one small full U containing V, simultaneously
    an I_alpha-chunk for every alpha. Lean: `∀ V, ObjectProperty.Small.{u} V ->
    ∃ U : SimplicialChunk A, ObjectProperty.Small.{u} U.carrier ∧
    V ≤ U.carrier ∧ (∀ α, ∃ E P, IsIChunk U T ... E P) ∧ ...`.
    Verdict: exact; one U is outside the alpha quantifier and carries its
    ambient chunk structure even when J is empty.
12. U and V have the same essential image in A[W^-1]. Lean:
    `U.carrier.map (MorphismProperty.Q (weakEquivalences A)) =
      V.map (MorphismProperty.Q (weakEquivalences A))`.
    I opened Mathlib `ObjectProperty.map`, whose definition is
    `fun Y => ∃ X, P X ∧ Nonempty (F.obj X ≅ Y)`, and the canonical
    localization functor Q. Verdict: exact after repair, expressing
    equality of essential images, not equality of U with a saturation.

Mismatches repaired:

* The original iff `U X <-> ∃ Y, V Y ∧ Nonempty (Q.obj X ≅ Q.obj Y)`
  required U to contain EVERY weakly equivalent representative. This is
  stronger than equal essential images and generally destroys smallness:
  in simplicial sets, the many differently sized contractible Kan complexes
  are all equivalent to a point. Replaced by equality of the two existing
  Mathlib essential-image predicates. This is a Lean repair, not a change
  to the already correct DAG statement.
* `IsIChunk` originally only required the diagram chunk. It omitted that U
  itself be a chunk, and the simultaneous clause imposed no ambient chunk
  condition at all when J was empty. It now takes an actual ambient chunk,
  and both theorem clauses supply it explicitly.
* `EnrichedModelFactorization` originally required global enriched
  factorizations of ALL ambient arrows extending the chunk's choices.
  HTT A.3.4.1 asks for enriched choices only on finite families inside U.
  Replaced that stronger definition with exactly those two finite-family
  enriched factorizations, using existing Mathlib finite-star diagrams and
  enriched ends. The global factorization theorem remains a proof import:
  its restrictions construct these choices, as in the DAG proof.
* The theorem docstring originally compressed the eight proof steps into
  a short sketch. Expanded it to all eight steps, with their named inputs,
  regularity/smallness argument, restriction argument and empty-V case.
* Added the cf helper's missing source/blueprint docstring, removed the
  redundant Small-J instance and theorem-signature let, and retained direct
  non-public proof imports for the stated proof dependencies. No theorem
  has been proved; the sole postponed theorem is `simplicial_small_chunks`.

Edge cases checked:

* n=0: both shapes retain the distinguished object; unique maps to the
  empty product and from the empty coproduct give precisely the replacement
  clauses. Arbitrary finite indexing sets are represented by `Fin n` after
  a bijection, with no nonemptiness assumption.
* J empty: the result still supplies `U : SimplicialChunk A`; no clause is
  lost by the vacuous forall-alpha. V empty: the empty full subcategory
  may serve, since no finite family has a distinguished object inside it;
  both essential images are empty.
* I empty: there is the unique empty diagram, the all-values condition is
  vacuous, and there are no evaluations to add in the small-closure proof.
  The first clause imposes no nonempty/cofibrant condition on I.
* Zero, initial and terminal objects are unrestricted. The model structure
  supplies finite limits/colimits, and no pointedness or nonzero assumption
  is imposed. This is categorical, with no ring or characteristic parameter.
* u is the small object/mapping universe for indices and family J; w is the
  independent ambient object universe. All displayed universes are bound.
  A small type presented in a larger universe can be shrunk before use;
  A itself is not required to be u-small. The dependency's diagram objects
  live in max u w, with mapping simplicial sets still in u.

Independent searches (different wording from the first worker):

* `msearch.py Q37 lem-coef-simplicial-small-chunks leansearch
  "enriched functorial factorization finite families small full subcategory"`
  returned ordinary `MorphismProperty.FunctorialFactorizationData` and the
  ordinary small-object functor. These do not have simplicial naturality,
  finite-family chunk closure or the simultaneous essential-image theorem.
* `msearch.py ... leanfinder "finite cone enriched functorial factorization
  full subcategory closed fibrant replacement"` returned Brown factorization
  data and fibrant/cofibrant variants for individual arrows, not chunks.
* `msearch.py ... loogle "EnrichedFunctor"` reported that the service did
  not recognize the identifier. I therefore used the successful LeanSearch
  and LeanFinder searches, plus direct source searches and signature reads.
* Direct `rg` of the project's `lean/Sheaf`, upstream `WeilConjectures`,
  Mathlib AlgebraicTopology and CategoryTheory, and `dag/lean_names_upstream.json`
  for `SimplicialChunk|IsIChunk|small_chunks|EnrichedModelFactorization` and
  enriched-factorization vocabulary found only the already recorded generic
  enriched-factorization theorem and mentions of chunks in docstrings. No
  existing chunk definition or exact theorem was found.
* I searched Mathlib for finite star/cone/cocone shapes, full subcategories,
  `enrichedHomπ`, `enrichedOrdinaryCategory`, and essential images. Reused
  `WidePushoutShape`, `WidePullbackShape`, their existing functor categories,
  the canonical enriched-end implementation and enriched-full-subcategory
  instance, `bifibrantObjects`, `ObjectProperty.map`, `ObjectProperty.Small`,
  and `MorphismProperty.Q`. Thus the repair adds no copies of these notions.

Dependency reading: the actual `SimplicialDiagramEnrichment` end represents
`enrichedNatTransYoneda` with specified projections, identities and composition;
`value` forgets only the `ForgetEnrichment` type synonym. The actual
`ProjectiveSimplicialModelStructure` extends the model structure and fixes weak
equivalences/fibrations objectwise, with combinatoriality, tensors/cotensors and
SM7. These are precisely A^I and its projective model structure, not the ordinary
functor category with arbitrary transformations. `CoherentNerve.SCat` and
`underlying` are the recorded small enriched-category encoding and its underlying
ordinary category. `BergnerModelData` characterizes weak equivalences, fibrations
and cofibrations; its model provides the exact cofibrancy premise. Both dependency
records are usable and need no repair. The new finite-family declarations only
render this item's inline chunk notion; no independent missing notion, new DAG
node or dependency module is introduced.

Validation: every delivered Lean file is checked through the required
`scompile.py Q37 lem-coef-simplicial-small-chunks
lean/Sheaf/CategoryTheory/SimplicialSmallChunks.lean` wrapper. The final node
`lean.statement` is extracted verbatim from the theorem signature, and its
declaration list names all helpers. No `statement_change`, disputed statement,
hollow data, additional axioms, private copies, file-local notation or local
instances remain. The following delivery preflight supplies the final shape,
compilation and bookkeeping checks.
