## Worker report

The module `Sheaf.CategoryTheory.SystemLocalizationUniversal` states the universal
localization result for enhanced (quasicategory) systems. `EnhancedCategory` carries the
underlying simplicial set and universe convention; `EnhancedSystem` carries its marked
1-simplices; `IsEnhancedSystem` records inclusion of equivalences and closure under
2-simplex composition and homotopy. `EnhancedSystemMap` and
`markedFunctorSubcomplex` render coherent marked functors and the full marked functor
subcategory. `EnhancedLocalization` records the unit, inversion of every marked arrow,
and the coherent restriction equivalence for every enhanced target. The adjunction
structure records the fully faithful equivalence-system right adjoint, its left adjoint,
units, localization data, and terminal/binary product comparisons. The theorem
`SSet.coef_system_localization_universal` asserts existence of this adjunction and all
finite-product clauses (binary induction includes the empty product).

The theorem has no hypotheses beyond the fixed universes. Its conclusion has four clauses:
`right_fully_faithful` is the fully faithful right adjoint clause; `left_adjoint` is the
left-adjoint clause; `finite_product_comparisons.empty` is the terminal/empty product
comparison; and `∀ R T, ...binary R T` is the coordinatewise binary comparison, from
which finite products follow by induction. For each marked system, `EnhancedLocalization`
contains the unit `R.category.carrier ⟶ localized.carrier`, the `inverts` clause for each
`R.marked f`, and `restriction` as an `IsFunctorEquivalence` onto the full subcategory
of functors sending marked arrows to equivalences.

Dependencies used are `Sheaf.CategoryTheory.EnhancedDiagramsCones` (the recorded
`SSet.Enhanced.IsEquivalenceEdge`, `fullSubcomplex`, and `IsFunctorEquivalence`),
`Sheaf.CategoryTheory.SimplicialGroupoidLocalization`,
`Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`,
`Sheaf.CategoryTheory.IsofibrationExponentiation`, and
`Sheaf.AlgebraicTopology.JoyalModelStructure` for the proof plan. The dependency
`def-coef-complete-algebroid` has no Lean record in the DAG; its universe and
infinity-category conventions are rendered by the explicit helper declarations in this
module, as authorized for a missing interface.

Edge cases checked: `IsEnhancedSystem` includes identity/equivalence arrows; the
coordinatewise product handles an empty marked set; `enhancedSystemTerminal` is the
terminal category used for the empty product; binary induction covers the one-factor
case; and `n = 0` simplices are handled by the existing `SSet` internal-hom definitions.

Searches made: `msearch.py leanfinder` and `msearch.py loogle` for infinity-category
localization, marked-arrow systems, and finite-product localization (no exact match;
only ordinary-category localization declarations were found); `msearch.py grep` and
`rg` over Mathlib and `WeilConjectures/` for `WCat`, `quasicategory`, and localization
(unrelated ordinary localization and simplicial primitives only); and `rg` over
`lean/Sheaf` (the existing hammock localization is an ordinary-category construction
and does not state the present coherent adjunction). No exact existing declaration was
found.

The node is not marked `STATEMENT-DISPUTED`.

## Second reading by Q07

I read the current node in the shared repository and the sandbox node and Lean file,
then read HA Construction the project server, Proposition the project server, Notation the project server and its proof
at https://www.math.ias.edu/~lurie/papers/HA.pdf (printed pp. 485–486, PDF pages
484–485). The source is HA, not Stacks; there is no source-wide ring, scheme,
finiteness, presentability or nonemptiness hypothesis. The node already agrees with
this source. There is no node statement correction and no statement_change/citer
audit is needed. The Worker report above describes the superseded draft; in particular
its def-coef-complete-algebroid dependency and four-Prop conclusion are not the final
interface.

Object/hypothesis/conclusion inventory and matching Lean, with verdicts:

1. Infinity categories in a common containing universe: `C D E Q : SSet.{u}` and
   the actual Mathlib `Quasicategory` predicate. Verdict: exact. Removed the draft's
   `EnhancedCategory.quasicategory : Prop`, which imposed no horn-filling condition,
   and its product/terminal assignments `quasicategory := True`.
2. A collection of arrows W: `W : C _⦋1⦌ → Prop`. `IsEnhancedSystem C W` contains
   precisely equivalences, triangle composition closure, and invariance under left
   and right homotopies (triangles with the corresponding short edge degenerate).
   Verdict: exact wide subcategory of hC. The draft's equivalence between the two
   short faces of EVERY triangle was wrong: applied to a degeneracy of a noninvertible
   arrow, it equated membership of that arrow with membership of its identity. It
   would force every edge to be marked. Homotopies now compare the parallel long and
   short edges, only under the appropriate degenerate-edge condition.
3. Marked functors and the mapping spaces of WCat infinity:
   `markedFunctorSubcomplex C W D V` uses the dependency's `Enhanced.fullSubcomplex`
   of the actual internal hom, selecting exactly functors carrying W into V. It
   retains ALL coherent transformations. Its `Enhanced.core` is the node's mapping
   space, a union of components: a natural equivalence conjugates arrow images by
   equivalences, and V contains equivalences and is closed under composition and
   homotopy. Composition is the existing simplicial functor composition. Verdict:
   exact, without replacing WCat by an ordinary category or discarding higher data.
4. G is specifically the equivalence-system inclusion: the first theorem conjunct
   specializes both marking predicates to `Enhanced.IsEquivalenceEdge`. It asserts
   `markedFunctorSubcomplex ... = ⊤`, so its inclusion is the identity on the whole
   coherent functor category and therefore on the mapping cores. Verdict: exactly
   the fully faithful inclusion. The draft allowed an arbitrary object function
   `right` with unconstrained `right_on_equivalences` and `right_fully_faithful` Props.
5. G has a coherent left adjoint: the second conjunct supplies for EVERY actual
   quasicategory C and system W a quasicategory Q and unit q, with the universal-arrow
   property against EVERY target E. This is the equivalent universal-arrow
   formulation of the adjunction, rather than an unconnected assertion about an
   arbitrary functor. Taking cores represents
   `Map_WCat((C,W),G E)` by `Map_Cat(Q,E)`, naturally in E. The node's existing
   lem-coef-infinity-pointwise-adjoint-criterion says precisely that these universal
   arrows assemble into the coherent left adjoint, unit, counit and triangles.
   Its module is not yet recorded, so there is no fabricated import for it. No
   functorial choice of simplicial fibrant replacement is assumed. Verdict: an
   equivalent definition of the asserted adjunction, with no extra hypothesis.
6. The very same unit inverts every W-arrow: the second conjunct has
   `∀ f, W f → Enhanced.IsEquivalenceEdge Q (q.app _ f)`. Verdict: exact. This unit
   is now the map in the universal property, rather than the draft's unrelated
   `unit` and `localizations` fields.
7. Restriction is an equivalence of FULL functor infinity categories: the map r
   lands in `markedFunctorSubcomplex C W E (Enhanced.IsEquivalenceEdge E)` and
   `r ≫ ...ι = (MonoidalClosed.pre q).app E`, with
   `Enhanced.IsFunctorEquivalence r`. Verdict: exact, includes noninvertible
   transformations. The draft's arbitrary equivalence e had no equation with
   restriction. Naturality with postcomposition and simplicial parameters follows
   from this equation in every degree; the inclusion is monic, so it detects all
   those equalities, including higher simplices. No unrelated target equivalences
   can serve as witnesses.
8. Coordinatewise finite products and empty product:
   `enhancedProductSystem C W f = ∀ i, W i ((Pi.π C i).app _ f)` uses the actual
   simplicial product `∏ᶜ C`. The third conjunct quantifies over `I : Type u` with
   `[Finite I]`, every family of systems, and ANY family q of localization units.
   It asserts that `Limits.Pi.map q` inverts exactly this system and itself has the
   FULL restriction equivalence, with the explicit precomposition equation.
   Verdict: equivalent universal-property statement of preservation of every finite
   product. In particular, apply the second conjunct to the product system; compare
   that localization with the product units using the third conjunct. The two
   universal properties give mutually inverse comparison functors under the units.
   Their components are the localized projections. The space of lifts of the product
   unit is contractible because restriction is an equivalence, so this comparison is
   coherent and natural, independent of ordering, choices and parenthesization.
   This expresses exactly the node's natural product comparisons, and avoids an
   arbitrary map carrying an uninterpreted claim of naturality. The draft's empty
   and binary Props could simply be chosen True and had no products or comparisons.
9. There are no additional hypotheses on the main result. The hypotheses in its
   third conjunct merely say that the maps being multiplied are localization units;
   the second conjunct supplies them for every input. All maps, predicates and
   universes are explicitly bound, with `autoImplicit false`. Verdict: exact.

Dependency reading: I opened def-cbc-enhanced-diagrams-cones and its recorded module.
`SSet`, `Quasicategory` and the internal hom are Mathlib's actual simplicial notions.
`Enhanced.IsEquivalenceEdge` uses both inverse triangles;
`Enhanced.fullSubcomplex` tests every vertex; `Enhanced.IsFunctorEquivalence` uses
an actual quasi-inverse and natural equivalence edges; `Enhanced.core` retains exactly
simplices with equivalence edges. These are the notions used here, with no private
replacements. I also opened the recorded signatures/docstrings of
simplicial_groupoid_localization, enhanced_functor_cone_calculus,
isofibration_exponentiation, isofibration_pullback_limit, and
exists_joyal_model_structure. Their five modules are imported for the five recorded
proof dependencies. The pointwise-adjoint proof dependency has no recorded Lean module,
so only its node is cited in the seven-step proof docstring.

Edge cases: Empty C is permitted: quasicategory horn filling does not require a vertex.
The empty marking on an empty C is permitted; for nonempty C equivalences include
identities, as required. The system of just equivalences and the system of all arrows
are both covered. On the nerve of [1], just equivalences does NOT mark its nonidentity
arrow; the repaired homotopy clause preserves this essential case. For an empty finite
index I, `∏ᶜ C` and `∏ᶜ Q` are terminal, the marking is universally true, and the product
of the units is the canonical map between these terminal objects. This gives the empty
product comparison without a Nonempty assumption. Singleton and zero-factor products
are included. Degrees n=0 and all higher degrees are inherited from the existing full
subcomplex and internal-hom constructions; there is no truncation. Zero objects, schemes,
numerical characteristic and coefficient rings are not parameters of this theorem.
Universe u is arbitrary and common to the simplicial sets under discussion, following
the recorded enhanced-diagram convention. The category of such objects lies in the next
universe. Enlarging the common universe accommodates larger targets; no independent
smaller target universe or equality between site universes is introduced. Every finite
family has a finite ordinal representative in the containing universe, so the index
convention excludes no finite product.

Independent searches (2026-10-17):

- `msearch.py ... leanfinder "Universal arrow for localization of a quasicategory and
  cartesian product of marked quasicategories"`: no exact theorem. It returned simplicial
  primitives and ordinary `Localization.StrictUniversalPropertyFixedTarget.prod_fac₁`.
- `msearch.py ... loogle "SSet.Quasicategory"`: checked the actual horn-filling predicate;
  also found the existing left/right edge-homotopy conversion results.
- `msearch.py ... grep "marked|localization" AlgebraicTopology/Quasicategory`: zero hits.
- `rg` independently in Mathlib, upstream WeilConjectures and shared lean/Sheaf for
  systems, markings, arbitrary edge localization, inverting diagrams and the declaration
  names. Read Mathlib CategoryTheory/Localization/Prod.lean and Pi.lean: ordinary
  Category/Functor results, not arbitrary quasicategories. Upstream homotopy-category
  adjunctions likewise do not state this theorem. Read HammockInfinityLocalization:
  it requires an ordinary category as input. Read SheafFlatModel's similarly named
  localization predicate: again an ordinary-category nerve as source.
- Read EnrichedMarkedRealization.invertingDiagrams and IsEdgeLocalization. Its
  IsEdgeLocalization predicate does express localization for an arbitrary set of
  simplicial edges. It lives in a downstream module: the DAG path is
  lem-coef-enriched-marked-realization → lem-coef-coherent-nerve-comparison →
  lem-coef-model-colimit-localization-comparison →
  lem-coef-small-diagram-model-rectification → this item. I therefore removed the
  draft's new localization predicate entirely. The theorem states its universal
  property directly; there is no second definition of localization and no import
  or dependency cycle. The generic W-to-V marked functor subcomplex used to describe
  WCat is more general than that module's inverting subcomplex and uses the already
  recorded fullSubcomplex definition. No existing declaration states the present
  theorem, and no DAG node already defines systems on arbitrary quasicategories.

Changes: removed the hollow/unconstrained structures and duplicate enhanced-category
wrapper; repaired homotopy closure; supplied actual quasicategory and system hypotheses;
connected inversion and restriction to the same unit; replaced arbitrary truth-valued
adjunction/product fields by the explicit universal-arrow statement and arbitrary finite
products of units; added the missing recorded pullback-limit proof import; replaced the
incorrect source-convention reference; expanded the docstring to all seven proof steps;
updated lean.statement verbatim and lean.declarations to the four declarations actually
present. No new nodes, dependency modules, target changes, or node-statement changes.
There are no data sorries, theorem bodies other than the required sorry, file-local
instances/notation/private definitions, overlong lines, or unused/unbound variables.
The prescribed scompile.py compiled the final module as sandbox and library successfully
with no diagnostics (1.3 s / 1.4 s). The only postponed theorem is
SSet.coef_system_localization_universal, whose DAG node and full proof docstring match.
