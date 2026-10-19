## Worker report

The module `Sheaf.CategoryTheory.SimplicialBousfieldModelStructure` defines the
replacement-independent local-object predicates `tLocalObject`, `tEquivalence`, and
`tEquivalences`, then states
`simplicial_bousfield_model_structure` with `sorry` proof. The source is HTT
Proposition A.3.7.3, as recorded in the node.

The hypothesis `T : MorphismProperty M` together with
`[MorphismProperty.IsSmall.{v} T]` renders the small set of maps. The hypothesis `hT`
requires each member to be a cofibration with cofibrant source and target. The two
functorial-factorization typeclasses, `D`, `hSM7`, `hM`, and `hleft` render the old
combinatorial left proper simplicial model category. `tLocalObject T Z` renders the
weak-homotopy-equivalence enriched mapping test for each member of `T`; the theorem's
fibrant-object clause adds old fibrancy explicitly. `tEquivalence T f` quantifies all
cofibrant replacement squares `qA`, `qB` (fibrations and weak equivalences) and every
filler `g`, so its enriched map is precisely the derived mapping-space test without
choosing a replacement. `tEquivalences T` packages that predicate as a morphism
property.

The conclusion's existential `m` is the localized model structure on the same category.
`CombinatorialModelCategory` and `SatisfiesSM7` render combinatorial and simplicial
model structure; the displayed pushout clause renders left properness. The next two
equalities identify cofibrations and weak equivalences exactly. The terminal-map
biconditional gives precisely the old fibrant `T`-local objects. The two existential
functorial-factorization witnesses give both new model factorizations. The final two
clauses spell out that the identity preserves cofibrations and old trivial cofibrations,
which is the identity left Quillen adjunction; the existing enrichment, tensors,
and cotensors are carried by the unchanged `SimplicialCategory M` and `D` inputs.

Dependencies used: `def-coef-complete-algebroid` is not needed by the formal signature;
`def-weil-pbc-simplicial-set` is represented by Mathlib's `SSet` declarations
(`SSet`, `SSet.degenerate`, `SSet.nonDegenerate`, `SSet.Subcomplex`, `SSet.Finite`);
`lem-coef-simplicial-model-nerve-localization` is imported from
`Sheaf.CategoryTheory.SimplicialModelNerveLocalization`. Proof-plan modules imported
are `CofibrationLocalMappingTest`, `KanQuillenRightProper`,
`AccessibleSmallObjectFactorization`, `ModelLocalizationDetectsWeakEquivalences`,
`ModelWeakEquivalencesAccessible`, `AccessibleArrowInverseImage`, and
`SmithModelRecognition`; lifting-class closure is the recorded Mathlib dependency and
needs no project import.

Edge cases checked in the statement design: `T = ∅` makes `tLocalObject` vacuous and
recovers the old fibrant objects; a zero object and identity maps are covered by the
replacement-square quantifiers; terminal model categories are permitted; an empty underlying category is
excluded by the required terminal object; dimension-zero mapping tests remain included
because `SSet.Enhanced.IsWeakHomotopyEquivalence` is used without a positive-degree
restriction.

Searches made: `msearch.py Q92 ... leanfinder "Constructing a model structure whose fibrant objects are local objects for morphisms"` found only generic model-category and orthogonal-reflection declarations, not this theorem; `msearch.py ... leanfinder "A left proper combinatorial simplicial model category admits a left Bousfield localization at a small set of cofibrations"` found only Kan and generic model-category declarations; `msearch.py ... leansearch "Existence of a simplicial model structure whose cofibrations are unchanged ..."` found only generic `ModelCategory.mk'` and Kan declarations; `msearch.py ... loogle "Bousfield"` returned no hits; grep of Mathlib and `WeilConjectures/` found no Bousfield model-structure theorem. The existing project `CombinatorialModelCategory` structure was reused from `Sheaf.CategoryTheory.ModelColimitLocalizationComparison`.

## Resumed packet self-check

The initial dry run compiled the saved module cleanly and found exactly one
preflight defect: `lean.statement` included the terminating `:=`. The record now
contains the literal multiline signature up to, but excluding, that token. No
mathematical statement changed. The three helper docstrings now name the owning
node `lem-coef-simplicial-bousfield-model-structure`; they are definitions of the
local predicates introduced in this very node, not separate DAG notions.

Read the current dependency signatures and docstrings: `SimplicialTensorCotensor`
provides the existing enriched tensors and cotensors, and
`SimplicialModelLocalization.SatisfiesSM7` provides exactly the enriched
fibration corner axiom for the old and new model structures.
`HomotopicalAlgebra.CombinatorialModelCategory` provides local presentability,
small generating arrow families for both lifting classes, and both functorial
factorizations. Thus the explicit old factorization instances express the
model-category convention already assumed by the node, and the new witnesses
express its requested functorial factorizations. The same `D` and simplicial
enrichment remain fixed as the model structure varies. The identity adjunction
is canonical, so its two preservation clauses state the left Quillen condition.

For the derived test, cofibrant replacements exist for every object. A lift `g`
exists in each displayed square because its source is cofibrant and `qB` is a
trivial fibration; two such lifts represent the same derived map. Consequently
the universal quantification is neither vacuous nor an additional requirement
on the map, and uses the ordinary enriched precomposition map in the correct
direction. Old fibrancy of targets is explicit. Identity maps and the empty
localizing family satisfy these same tests.

No new nodes, dependency repairs, statement corrections or disputed statements
were required. The maintainer supplies the independent review.

## Return repair self-check

The return for immutable head `09f270671f39` reports a rejected path in the
reviewer's `--apply-fixes` packet. This delivery uses `deliver2.py` to package the
sandbox report, rather than supplying `coord/reports/...` as an apply-fixes input.
The resumed dry run passed preflight and compiled the saved module, producing
candidate `e8bad6db0d`. Its staged paths were exactly the owning module, the owning
node, and this report at the delivery report destination. The node differs from
the current shared base only in `lean`.

The final self-check confirmed the literal signature record, explicit binders,
100-character line limit, exactly one postponed theorem, and real data for all
three helper definitions. Reading the current tensor/cotensor, SM7 and
combinatorial-model interfaces confirmed the hypotheses and conclusion mapping
above. No mathematical change was needed for this packaging return.

## Second reading by Q92

Independent maintainer second reading of immutable delivery
`63a22540d96fcfa4bb086d00477a5c5fb38474dd`, performed on 2026-10-17.
I did not write or previously second-read this delivery. The original report's
placeholder has been replaced by this reading; no earlier independent reading is claimed.

I read the packet, the snapshot module and all four snapshot node records, including
all three statement dependencies. I read check-brief2.md in full, the stage-2 brief,
delivery-errors H, and the exact source declarations used below.

Source comparison: HTT A.3.7.3, printed pp. 908–910, gives the combinatorial simplicial
model structure with unchanged cofibrations, local weak equivalences, left properness,
and exactly the old fibrant local objects. The preceding definitions on printed
p. 906 give the derived mapping-space tests; A.3.7.1 gives the strict mapping test.
The restriction to cofibrations with cofibrant endpoints is explicitly in this item,
so enriched mapping spaces into fibrant targets compute those derived tests.
The blueprint ancestor's second paragraph is a derived coefficient-adjunction
calculation; it imposes no extra hypothesis on this abstract model-category lemma.

Hypotheses and conclusions, individually checked:

* The underlying category is arbitrary `M : Type u` with `Category.{v} M`.
  `ModelCategory M`, `HasLimits M`, `HasColimits M`, and the two functorial
  factorization instances render exactly the convention in the nerve-localization
  dependency. Mathlib's bare `ModelCategory` only supplies finite limits/colimits
  and factorizations, so the explicit instances are necessary, not extra assumptions.
* `SimplicialCategory M` is the existing ordinary-compatible enrichment over
  `SSet.{v}`. `D : SimplicialTensorCotensor M` specifies enriched representing
  tensor/cotensor objects and universal elements. The existing `SatisfiesSM7` uses
  the actual enriched corner map, Kan horn lifting and weak homotopy equivalence
  when either input is trivial. Thus these are the source's simplicial model data.
* `hM : CombinatorialModelCategory.{u,v,w} M` reuses the existing structure from
  ModelColimitLocalizationComparison. Its fields are local presentability, small
  arrow families generating both lifting classes, and functorial factorizations.
  Mathlib's local presentability means a regular cardinal with a small filtered
  generator of presentable objects. No Noetherian, field or finiteness assumption
  has been introduced.
* `hleft` tests precisely the pushout of a weak equivalence along a cofibration:
  `pushout.inr f i` has source the target of `i`. The conclusion uses the same
  orientation and explicitly the new model's classes.
* `T` is an actual morphism property with `IsSmall.{v} T`. Mathlib's
  `isSmall_iff_eq_ofHoms` identifies this with a small indexed arrow family.
  `hT` includes all three requested conditions: cofibration, cofibrant source,
  cofibrant target. Repetitions in an indexed presentation have no effect.
* `tLocalObject` tests `eHomWhiskerRight SSet t Z`, whose signature is
  `Map(B,Z) → Map(A,Z)`. Old fibrancy is supplied separately wherever the predicate
  is used in the theorem and in `tEquivalence`; the bare helper does not assert it.
* `tEquivalence` tests every old fibrant local `Z`, every pair of cofibrant
  replacements which are trivial fibrations, and every commuting lift `g`.
  Cofibrant replacements exist by factorization of initial maps. Such a `g` exists
  by lifting against `qB`. The replacement square represents the derived map of
  `f`; different lifts give the same derived map. Hence the universal test is
  equivalent to the stated derived precomposition test and is not vacuous.
  No fibrant replacement of `Z` is needed since it is already fibrant.
* `∃ m : ModelCategory M` changes the model structure on the same category.
  Its first two clauses assert new combinatoriality and SM7. The enrichment remains
  the fixed instance, and `D` is independent of model classes, so exactly those
  same tensors and cotensors remain available. It need not be reconstructed or
  existentially chosen in the conclusion.
* The next clauses give new left properness and literal equalities of the
  cofibration and weak-equivalence properties. The right side `tEquivalences T`
  is computed with the old model, not with `m`.
* The terminal-map biconditional says precisely new fibrant iff old fibrant
  and local. Terminal maps require no new choice of category or terminal object.
* The two existential typeclass witnesses assert both functorial factorizations
  for the new model. The terminal `True` merely packages these witnesses; it is
  not a replacement for either required structure.
* The last two clauses are preservation of cofibrations and trivial cofibrations
  by the identity. Together with the canonical identity self-adjunction, these
  say exactly that identity from old to new is left Quillen. No presheaf or
  infinity-category identification of the new model is asserted.

Dependency reading: the complete-algebroid node is cited only for size and space
conventions; the item never constructs or quantifies over an algebroid. I checked
its recorded `completeCategory` definition and universe-lift convention, without
substituting another coefficient category. The simplicial-set dependency's Mathlib
matches are the actual functor category `SSet`, lower-dimensional-image degeneracy,
its complement, subfunctors and finiteness of the sigma type of nondegenerate
simplices. I checked Stacks simplicial.tex, section 0174 and definition 0175.
The nerve-localization dependency was read with its actual SM7, mapping presentation,
replacement spans, inclusion comparisons, spaces clause and final theorem signature;
HA 1.3.4.16 and 1.3.4.20 corroborate this interpretation. Its recorded maintenance
note reopens its stage-1 proof, not its unchanged stage-2 statement/interface; this
review makes no claim that its postponed proof has been completed. No dependency
repair or missing independent helper is required to state the present item.

I matched all ten proof-docstring steps with the node: (1) old-to-local equivalences
and elementary closure; (2) the local cofibration test and lifting closure;
(3) old generators plus all tensor-boundary tests; (4) accessible small-object
replacement; (5) homotopy-category detection and accessible inverse image;
(6) Smith recognition and the retract argument; (7) the two simplicial triviality
cases; (8) fibrant detection including the zero-boundary test; (9) the two-pushout
left-properness argument; (10) identity Quillen preservation. The proof imports
correspond to recorded proof dependencies and are allowed even before stage 3.
The lifting-closure dependency is Mathlib, available through the imported lifting
interfaces. No local result is proved: the one theorem has precisely `by sorry`.
The three helper definitions contain real predicates and no postponed data.

Search audit: the worker records LeanFinder, LeanSearch, Loogle and grep queries and
results. I independently searched Mathlib, WeilConjectures and the group's Sheaf
sources using Bousfield, local objects/equivalences and the delivered identifiers.
I opened Mathlib CategoryTheory/Localization/Bousfield.lean: its ordinary Hom-set
bijection construction is not the simplicial model-existence assertion. Existing
BousfieldLocalFibrations and BousfieldQuillenDescent assume a localization rather
than construct one. HomotopyLocalEquivalencesAccessible uses a specified coherent
localization and evaluation maps, rather than this replacement-square/enriched
interface. I found no exact reusable declaration and no conflicting full names.
The delivered helpers introduce the tests of this node; they do not duplicate an
unusable dependency under private names.

Edge cases: empty `T` gives all old fibrant targets, so derived Yoneda recovers old
weak equivalences. Identity localizing maps impose no additional condition. All
objects, including initial/terminal or zero objects when present, are covered by
replacement factorizations; no endpoints of `f` must be cofibrant. Empty mapping
spaces are handled by the component-bijection part of weak homotopy equivalence.
The boundary of the zero simplex is included in the proof. An empty underlying
category is excluded by the node's completeness, not an extra Lean hypothesis.
There is no scheme, characteristic or coefficient-ring restriction here.
Universes `u`, `v`, `w` are explicit and remain distinct; no equality of object,
hom, site or coefficient universes was imposed. The source's small-space parameter
is the enrichment and localizing-family universe `v`; local presentability and
its generators retain their explicit `w` parameter.

Mechanical checks and repairs: `lean.statement` is character-for-character equal
to the full multiline theorem signature before `:=`; it remains so after the
comment-only fix. The declaration list records all four declarations. All Lean
lines are at most 100 characters; autoImplicit is disabled. Source and blueprint
docstrings are present. No statement_change, new node or dependency module is
needed. H1/H11: the original second-reading section was only a disclaimer; this
complete replacement report supplies the actual independent reading. H8/brief §3:
the original module omitted its main-definition/main-statement list; the complete
replacement module adds it. I also corrected the worker report's claim that an
empty underlying category is permitted. These are documentation repairs; definitions,
the theorem signature and all node records are unchanged.

Compiler evidence: the delivery report records a clean saved-file compile and a
successful preflight after removal of the stray `:=` from lean.statement. I
independently reran the exact immutable file using the prescribed scompile.py
wrapper: exit 0, clean sandbox 1.7 s and clean library 1.6 s. The installed wrapper
currently uses the server side overlay (nt_srv_compile.py --wire-confirm); no
manual ssh or alternate compiler was invoked. The documentation-fixed file was
also compiled separately through that wrapper: exit 0, sandbox 1.7 s and
library 1.7 s, with no errors or warnings. I ran no global build, delivery, merge or project mutation.
