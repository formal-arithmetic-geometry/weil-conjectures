## Worker report

The module `lean/Sheaf/SixFunctors/CoefGoodTreeIdempotentEnlargement.lean` states
`CategoryTheory.coef_good_tree_idempotent_enlargement` and gives the canonical auxiliary
constructions used by its statement. `coefGoodTreeSubdiagram` restricts the diagram
`Y : T ⥤ Under X` to a subtype `E : Set T`; `coefGoodTreeColimit` is its chosen Mathlib
colimit in `Under X`; `coefGoodTreeInclusion` is the functor induced by an inclusion of
subsets; `coefGoodTreeColimitMap` is the induced canonical map between chosen colimits;
and `coefGoodTreePredMap` is the canonical map from the colimit of strict predecessors
of `t` to `Y.obj t`. All of these are real definitions and contain no postponed data.

The theorem has the following correspondence with the node statement. The universe and
uncountability hypotheses are `{τ : Cardinal.{v}}`, `[Fact τ.IsRegular]`, and
`hτ_uncountable : ℵ₀ < τ`; Mathlib's `Cardinal.IsRegular` is the regular-cardinal
predicate. The ordinary category is `C : Type u` with `[Category.{v} C]`, and the
small-colimit / small-family generation assumption is
`[IsCardinalLocallyPresentable C τ]`; this Mathlib class includes all small colimits and
a small family of τ-presentable generators. The well-founded small poset is
`T : Type v` with `[PartialOrder T] [WellFoundedLT T]`. The hypothesis that every strict
predecessor set has size less than τ is
`hpred : ∀ t, Cardinal.mk {s : T | s < t} < τ`.

The fixed object and diagram in `X/𝒜` are `X : C` and `Y : T ⥤ Under X`. For each vertex,
`P Q : T → C`, `hP` gives τ-presentability of both `P t` and `Q t`; `top` is the map
`P t ⟶ Q t`, `left` is `P t ⟶ Y_{T_{<t}}`, and `right` is `Q t ⟶ Y_t`. The pushout
clause is `cell`, using `IsPushout (top t) (left t) (right t)
(coefGoodTreePredMap X Y t).right`; the final map is exactly the canonical predecessor
map rendered in `𝒜`.

The downward-closed fixed subtree is `B : Set T` with
`hB : ∀ ⦃s t⦄, s ∈ B → t ≤ s → t ∈ B`. The two idempotents are the endomorphisms
`eB` and `eT` of `coefGoodTreeColimit X Y B` and
`coefGoodTreeColimit X Y Set.univ`; `heB` and `heT` state their idempotence. The
compatibility `i_{B,T} e_B = e_T i_{B,T}` is rendered by `hcompat` as
`eB ≫ i_{B,T} = i_{B,T} ≫ eT`.

For each `E₀ : Set T`, the premise `Cardinal.mk E₀ < τ` is followed by an existential
`D : Set T` with the downward-closed predicate, `E₀ ⊆ D`, and
`Cardinal.mk D < τ`. The conclusion then existentially supplies `eD` on `Y_D` and
`eBD` on `Y_{B ∩ D}`. The four conjunction clauses are respectively
`eD ≫ eD = eD`, `eBD ≫ eBD = eBD`, compatibility of `eD` with `i_{D,T}`,
compatibility of `eBD` with `i_{B∩D,B}`, and compatibility of `eBD` with
`i_{B∩D,D}`. Every `i` is the explicit `coefGoodTreeColimitMap` for the corresponding
subset inclusion.

The statement uses the dependency node `def-weil-pbc-category-colimit` through the
Mathlib declarations it records: `CategoryTheory.Limits.colimit`,
`CategoryTheory.Limits.Cocone`, `CategoryTheory.Limits.IsColimit`, and
`CategoryTheory.Limits.colimit.desc`; the filtered-colimit terminology is represented
by the recorded Mathlib presentability class. No project declaration was copied.

Edge cases checked: `E = ∅` is allowed (the subtype diagram is empty and its chosen
colimit in `Under X` is the undercategory initial object), `B = ∅` and `D = ∅` are
allowed when the hypotheses permit them, `T = ∅` is covered by `WellFoundedLT`, and
`E₀ = ∅` is covered by the cardinal premise. Strict predecessor sets are subtypes in
`Type v`, so their cardinalities use the same universe as `τ`. The `T`-index can have
minimal elements, where `coefGoodTreePredMap` is the map out of the empty predecessor
colimit. The identity and arbitrary-idempotent cases are both represented by the
unrestricted endomorphisms `eB` and `eT` subject only to the stated equations.

Searches made before writing: `msearch.py Q49 lem-coef-good-tree-idempotent-enlargement
leanfinder "Idempotent endomorphism on a good cellular tree restricts to small downward
closed subtrees compatible with a fixed subtree and their intersection"` (no match;
only unrelated Profinite rooted-tree projections); `msearch.py ... leanfinder
"Presentable cellular diagrams have small subdiagrams invariant under two compatible
idempotents"` (no match; only SmallObject results); `msearch.py ... loogle
"CategoryTheory.IsCardinalPresentable, CategoryTheory.Idempotents"` (rejected because
`CategoryTheory.Idempotents` is unknown); corrected Loogle searches for presentability
and idempotents (no matching theorem); LeanSearch for “Small cellular subtrees closed
under compatible idempotent maps” (unrelated rooted-tree hits); and grep for
`idempotent|Idempotent` in Mathlib `CategoryTheory/Presentable` and
`CategoryTheory/SmallObject` (no hits). `rg` over `WeilConjectures` and `lean/Sheaf`
found no declaration for this theorem or its good-tree restriction notion. The module
therefore defines the needed constructions and statement.

No `STATEMENT-DISPUTED` flag or node fault was found. The file compiles cleanly with
`scompile.py`; the required dry run is the final validation.

## Earlier second reading (a previous round; superseded)

I reread the node and the module independently. The universe, regularity, presentability,
predecessor-size, cellular pushout, downward-closedness, idempotence, and all three
compatibility clauses are present with the same direction of composition. The helper maps
are the canonical colimit maps induced by subset inclusions, and the predecessor map uses
the strict predecessor subtype. No mismatch was found.


## Second reading by Q49

I independently opened the current shared DAG node, its complete eight-step proof,
the sandbox Lean module, the category-colimit dependency node and its Mathlib source,
and the landed `def-coef-good-cellular-tree` node and module. There is no repair note
for this item and no `statement_change`. The earlier report describes the superseded
sandbox implementation; this section records the final delivery.

Source reading: HTT Definition A.1.5.1 and Notation A.1.5.2, printed pp. 799-800,
and Lemmas A.1.5.8-9, pp. 802-805, opened at
https://people.math.harvard.edu/~lurie/papers/HTT.pdf (PDF pages 816-822, zero based).
This is an HTT result, not a Stacks lemma. Definition A.1.5.1 supplies the well-founded
poset, the undercategory diagram, and the pushout cells; goodness bounds both cell
endpoints and the predecessor sets. Notation A.1.5.2 takes colimits in the
undercategory, including the empty colimit. Lemma A.1.5.9 assumes compatible
idempotents there and produces both restricted idempotents and all three commuting
squares. No compactness of the root or of the fixed large subtree is assumed.
The node additionally specifies its ordinary-category presentability convention;
Mathlib's locally tau-presentable class renders exactly that convention.

My object/hypothesis/conclusion checklist, made from the node before changing Lean:

| Node item | Final Lean rendering | Verdict |
| --- | --- | --- |
| Fixed small universe; ordinary category with small Hom sets | `{C : Type u} [Category.{v} C]`; `v` is the small universe and `u` remains independent | Exact; no equality of object and Hom universes |
| Uncountable regular small cardinal | `{τ : Cardinal.{v}} [Fact τ.IsRegular]` and `hτ_uncountable : ℵ₀ < τ` | Exact |
| All small colimits and a small family of tau-presentable objects generating by small tau-filtered colimits | `[IsCardinalLocallyPresentable C τ]` | Exact: read `LocallyPresentable.lean:41`, `CardinalFilteredPresentation.lean:77,153`; its parents are `HasColimitsOfSize.{v,v}` and `HasCardinalFilteredGenerator`, the latter supplying an essentially small generator and local smallness |
| Meaning of tau-presentability and tau-filteredness | `IsCardinalPresentable` and `IsCardinalFiltered` used by that class and by `hP` | Exact: read `Presentable/Basic.lean:149` (accessible coyoneda) and `IsCardinalFiltered.lean:44` (cocones for diagrams whose arrow set has cardinal less than tau) |
| Small well-founded poset | `{T : Type v} [PartialOrder T] [WellFoundedLT T]` | Exact, including branching posets |
| Each strict predecessor set has cardinal less than tau | `hpred : ∀ t, Cardinal.mk {s : T \| s < t} < τ` | Exact; the subtype and the cardinal have universe `v` |
| Root and diagram under the root | `(X : C) (Y : T ⥤ Under X)` | Exact; morphisms in `Under X` fix the root |
| Restricted colimits Y_E and canonical subset transitions | `CellularTree.subsetObj Y E`, `CellularTree.subsetMap Y hEF` | Exact: they use `colimit (subsetDiagram Y E)` and `colimit.desc` with the canonical cocone legs; defined also for arbitrary subsets, hence in particular for all required lower subsets |
| Canonical predecessor arrow | `CellularTree.predecessorMap Y t` | Exact: `colimit.desc` of the cocone with legs `Y.map (homOfLE s.property.le)`; not an arbitrary arrow |
| Two tau-presentable cell objects for every vertex | `(P Q : T → C)` and `hP : ∀ t, IsCardinalPresentable (P t) τ ∧ IsCardinalPresentable (Q t) τ` | Exact; supplying the chosen witnesses as parameters is equivalent to the stated existence hypothesis |
| Specified top, left, right arrows and pushout square in the original category | `top`, `left`, `right`, and `cell : ∀ t, IsPushout (top t) (left t) (right t) (CellularTree.predecessorMap Y t).right` | Exact; bottom arrow and orientation checked |
| Fixed downward-closed subtree | `B : Set T`, `hB : ∀ ⦃s t⦄, s ∈ B → t ≤ s → t ∈ B` | Exact |
| Two idempotents under X on Y_B and Y_T | `eB`, `eT` with the respective `CellularTree.subsetObj` endomorphism types; `heB`, `heT` | Exact; these are actual undercategory endomorphisms |
| Compatibility on the fixed subtree | `hcompat : eB ≫ CellularTree.subsetMap Y (Set.subset_univ B) = CellularTree.subsetMap Y (Set.subset_univ B) ≫ eT` | Exact; Lean composition reads left to right |
| Every initial small subset, with no lower-closedness hypothesis on it | `∀ (E₀ : Set T), Cardinal.mk E₀ < τ → ...` | Exact quantifier order |
| A small downward-closed enlargement containing the initial subset | `∃ D : Set T, (∀ ⦃s t⦄, s ∈ D → t ≤ s → t ∈ D) ∧ E₀ ⊆ D ∧ Cardinal.mk D < τ ∧ ...` | Exact; no requirement to contain all of B |
| Idempotents on Y_D and Y_(B intersection D) | Existential `eD`, `eBD`, with their respective endomorphism types and equations `eD ≫ eD = eD ∧ eBD ≫ eBD = eBD` | Exact |
| Compatibility of eD with eT | First concluding `CellularTree.subsetMap Y (Set.subset_univ D)` equation | Exact |
| Compatibility of eBD with eB | Second concluding map equation using `Set.inter_subset_left` | Exact |
| Compatibility of eBD with eD | Third concluding map equation using `Set.inter_subset_right` | Exact |
| No presentability of X or Y_B | Neither object has an extra instance or hypothesis | Exact |

Dependency inspection: `def-weil-pbc-category-colimit` records
`Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit` and
`colimit.desc`, with `Cocone` and `IsColimit`. I read their signatures and universal
property fields in `HasLimits.lean`, `Cones.lean:133` and `IsLimit.lean:62`.
`def-coef-good-cellular-tree` is already landed; its node statement explicitly includes
restricted colimits and their canonical maps, and its source module is
`lean/Sheaf/CategoryTheory/CellularTree.lean`. I read every helper used here, its
universe parameters, and `CellularTree.IsGood`; they express these exact objects.
The theorem keeps its existing unpacked cell data rather than imposing any arrow-class
membership hypothesis. No dependency module or new definition node is needed.

The current node's proof dependencies are all Mathlib leaves. I read the
small-colimit presentability signature (`Presentable/Limits.lean:185`), the cardinal
square signature (`Cardinal/Arithmetic.lean:45`), and the filtered-set representative
and equality signatures (`Limits/Types/Colimits.lean:241` and `Filtered.lean:141,153`).
Their modules are imported as proof-only imports, while the statement interfaces
are public imports. The final docstring contains all eight proof steps verbatim in
content: undercategory colimits; small-subtree presentability; the small lower-set
poset and tails; factorization and eventual equality; the partial-map induction
invariant; its construction with all equality witnesses; countable union and
idempotence; and verification of the three compatibility equations. In particular
there is no cancellation of potentially nonmonic transition maps.

Edge cases: `T = ∅`, `B = ∅`, and `E₀ = ∅` are all admitted; no nonempty instance
is required. The empty restricted colimit is initial in `Under X`, canonically
isomorphic to `Under.mk (𝟙 X)`, not an initial object of C. Minimal vertices use
that same empty predecessor colimit. `B = T`, empty intersections, identity
idempotents, and arbitrary idempotents satisfying the hypotheses are covered.
`D` may be empty when the data permit it; the conclusion does not force it to be
nonempty. The zero-object case needs no extra structure. There is no integer degree,
ring, scheme, or characteristic parameter. Tau equal to aleph-zero is deliberately
excluded by the source. All cardinal subtypes and diagram indices are in `Type v`;
no bound on `u`, presentability of X, finiteness, or linearity assumption is added.

Independent searches (using words different from the first worker's):

- `msearch.py Q49 lem-coef-good-tree-idempotent-enlargement leanfinder "Accessible category cellular presentation closure under compatible retracts on small lower subsets"`: eight hits, including `isPresentable_eq_retractClosure`, `Retract.isCardinalPresentable`, and small-object iteration. None is this simultaneous restriction statement.
- `msearch.py ... loogle '"retract", "presentable"'`: five hits, all presentability under retracts or generator/retract comparisons. Opened `Presentable/Retracts.lean:28-45` and `ObjectProperty/ColimitsCardinalClosure.lean:76`; neither supplies compatible subtree restrictions.
- `msearch.py ... leansearch "Two commuting retractions of cellular colimits restrict to small downward closed subdiagrams"`: eight hits concerning cellular colimits, attached cells, colimit legs, and closure under retracts; no matching theorem.
- `msearch.py ... grep 'good.?tree|good.?poset|invariant.{0,20}retract' CategoryTheory`: zero Mathlib hits.
- Independent `rg -n -i 'good.?tree|good.?poset|cellular.{0,40}(idempoten|retract)|idempoten.{0,40}(cellular|subtree)'` over Mathlib CategoryTheory, `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, and shared `lean/Sheaf` found the landed `WeakSaturationTreePresentation` consumer. Opening its imports led to `CellularTree.lean`, whose shared subtree helpers duplicate the sandbox definitions. The theorem itself is absent. Searched the upstream name index for `coefGoodTree|coef_good_tree` with no result. Searched DAG definition nodes for `CellularTree|cellularTree` and opened `def-coef-good-cellular-tree` and its declaration record.

Mismatches found and repaired:

1. H4: the sandbox defined five local replacements for existing subtree constructions.
   Removed all five, imported the landed `Sheaf.CategoryTheory.CellularTree`, and used
   `CellularTree.subsetObj`, `subsetMap`, and `predecessorMap` throughout. Added only
   `def-coef-good-cellular-tree` to `stmt_deps`, as the standing brief permits for a
   landed notion. No mathematical statement correction is involved.
2. H8: the short generic proof paragraph did not carry the current node's eight-step
   proof. Replaced it with the complete proof and its explicit dependency names.
3. H9: removed every `show ... from` from the theorem signature; subset proofs are
   the direct `Set.subset_univ`, `Set.inter_subset_left`, and `Set.inter_subset_right`
   terms. Moved this ordinary-category result from `Sheaf/SixFunctors` to
   `Sheaf/CategoryTheory/CoefGoodTreeIdempotentEnlargement.lean`.
4. The sandbox node predated the current stage-1 landing (`status: unsplit`, empty
   proof and proof dependencies). Restored every non-delivery field from the current
   shared node, retaining its complete proof, provenance, searches and review. The
   final node differs from the shared base only in `lean` and the added `stmt_deps`.
5. Synchronized `lean.statement` verbatim with the final theorem signature and removed
   the deleted helper names from its declaration record.

Validation: `scompile.py Q49 lem-coef-good-tree-idempotent-enlargement
lean/Sheaf/CategoryTheory/CoefGoodTreeIdempotentEnlargement.lean` passed both its
sandbox and library checks, each in 1.0 seconds, with no errors or warnings. By-eye
binder review found every universe and variable bound; the signature uses no `let`
or `show`. All lines are at most 100 characters. There is exactly one theorem,
whose proof is `sorry`, and no new definitions or axioms. No mathematical mismatch,
statement correction, new node, dependency repair, or disputed statement remains.
