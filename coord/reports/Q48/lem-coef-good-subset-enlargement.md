## Worker report

The delivery states CategoryTheory.exists_good_subset_enlargement in
lean/Sheaf/CategoryTheory/GoodSubsetEnlargement.lean. It uses the existing
CategoryTheory.CellularTree and CellularTree.IsGood notions and the recorded
CategoryTheory.weakSaturation_good_tree_presentation declaration. The hypotheses
are rendered as follows: κ and τ are regular cardinals with aleph0 < κ < τ
(hκ, hκτ, hτ); hp is the stated cardinal-power bound; A is a category with
IsCardinalLocallyPresentable A τ; hC and hCW give weak saturation of C and
C ⊓ W; hWiso gives closure of W under isomorphisms; hW is Mathlib's exact
HasTwoOutOfThreeProperty; and happrox quantifies over every τ-filtered poset
and arrow diagram with τ-presentable endpoints, requiring the specified small
κ-filtered enlargement of every τ-small seed. L ≤ C is hLC.

The tree clause is tree : CellularTree L X T with tree.IsGood τ (hgood) and
W (colimit tree.diagram).hom (htotal). A good A₀ is represented by
hA₀ : IsLowerSet A₀ ∧ W (CellularTree.subsetObj tree.diagram A₀).hom; the seed
B₀ is hB₀ : HasCardinalLT B₀ τ. The conclusion's five clauses are, in order,
IsLowerSet B, HasCardinalLT B τ, B₀ ⊆ B, IsLowerSet (B ∩ A₀), and
W (CellularTree.subsetObj tree.diagram (B ∩ A₀)).hom.

The item imports Sheaf.CategoryTheory.WeakSaturationTreePresentation for the
recorded weak-saturation/tree interface and the dependency module below for the
compact-root approximation input. The proof is sorry, with its five source steps
recorded in the declaration docstring: increasing-union closure, the small-good
rule from the approximation property, its pushout/saturation application, the
alternating enlargement, and the countable-union/intersection argument.

Searches for an existing declaration were made with:

* msearch.py ... leanfinder "small good subset enlargement cellular tree weak saturation intersection":
  no matching declaration; only unrelated Nöbeling and shrinking-lemma results.
* msearch.py ... loogle "CellularTree, IsGood, MorphismProperty, IsCardinalPresentable":
  no hits (the names are project declarations, not Mathlib matches).
* msearch.py ... grep "good.*subset|cellular.*tree" CategoryTheory:
  no hits.
* rg over WeilConjectures/ and lean/Sheaf for the item id and the good-subset
  terminology: no existing item declaration; the only relevant project declarations
  are CellularTree, CellularTree.IsGood, and weakSaturation_good_tree_presentation.

Edge cases checked before writing include T = ∅, A₀ = ∅, A₀ = T, B₀ = ∅,
an initially non-downward-closed seed, and identity arrows. The statement keeps the
whole-tree goodness hypothesis, permits a non-presentable root, and uses HasCardinalLT
for empty and nonempty small subsets without imposing a nonempty index set.

## Dependency modules

lem-coef-cellular-tree-presentable-approximations had no lean record or Mathlib
match, so it is repaired under §1(B) by
Sheaf.CategoryTheory.CellularTreePresentableApproximations. The module defines
CellularTreeApproximation, recording the τ-filtered arrow diagram, τ-small
downward-closed supports, τ-presentable endpoints, specified cell presentations,
root pushout maps, support compatibility, seed coverage, and the restricted-filtered
subcolimit pushout/tree clause. It then states
CategoryTheory.exists_cellularTreeApproximation with sorry. This is exactly the
stage-1 dependency notion and is the input used by proof step 2 and step 3 of the
item. The dependency node's lean.note records why the old record was unusable and
what this module states.

## Earlier second reading (a previous round; superseded)

I reopened both node JSON files and both Lean modules and compared each clause with
the source statements. The item has every cardinal hypothesis, both weak-saturation
hypotheses, the isomorphism and two-out-of-three conditions on W, the full
τ-filtered approximation property, the L ≤ C condition, the good whole tree, and
the good A₀/small B₀ inputs. Its conclusion preserves downward closure, τ-smallness,
containment, and goodness of the intersection. No extra hypothesis or weakened
conclusion was found. The dependency module records all support, presentability,
pushout, compatibility, coverage, and restricted-colimit clauses; its helper
predicate is used only to make those clauses explicit and has no hollow data. Both
files compile cleanly with scompile.py; no statement dispute or node correction was
needed.

## Second reading by Q48

This independent reading supersedes the earlier second-reading paragraph and the
worker report's descriptions of the superseded signatures. I opened both sandbox
node records and both Lean modules, the recorded CellularTree and
WeakSaturationTreePresentation modules, and Mathlib's regular-cardinal,
locally-presentable, filtered-category, and morphism-property definitions. There
is no repair note for this item. Neither natural-language node statement was
changed; the repairs make the Lean say what the existing nodes already say.

Source check: these nodes cite HTT, not Stacks. I opened the published HTT PDF at
https://people.math.harvard.edu/~lurie/papers/HTT.pdf and read A.2.6.9, printed
pp. 821--823, especially observations (i)--(ii), claim (*), and its alternating
construction; I also read A.1.5.11, printed pp. 806--807. Claim (*) explicitly
requires both B and B intersect A₀ to be good. The cardinal-filtered subposet in
the approximation input is κ-filtered. A.1.5.11 constructs compatible trees after
changing the root, with the same cell arrows, not merely unrelated total arrows.
The auxiliary node explicitly expands that construction into a compatible
filtered system and its filtered restrictions; I checked against its complete
12-step proof as well as the cited source. No stronger hypotheses from the
ambient model-recognition application have been imported into this helper.

The object's/hypothesis/conclusion checklist for the item is:

1. Small universe and ordinary locally τ-presentable category with small Hom sets:
   `universe v u`, `{A : Type u} [Category.{v} A]`, `τ : Cardinal.{v}` and
   `[IsCardinalLocallyPresentable A τ]`. Mathlib's class supplies all v-small
   colimits and a v-small presentable generating family. The object universe u
   remains independent of v. Verdict: exact.
2. Infinite regular κ < τ and uncountable regular τ: `[Fact κ.IsRegular]`,
   `[Fact τ.IsRegular]`, `hκτ : κ < τ`, `hτ : Cardinal.aleph0 < τ`.
   Mathlib's IsRegular already includes aleph0 ≤ κ. The former extra strict
   `aleph0 < κ` excluded κ = aleph0 and was removed. Verdict: repaired.
3. Cardinal exponent bound: `hp : ∀ a b : Cardinal.{v}, a < τ → b < κ → a ^ b < τ`.
   This has exactly the node's quantifiers. Verdict: exact.
4. Arrow classes C,W: `(C W : MorphismProperty A)`. Weak saturation of C and
   C intersect W is respectively `hC` and `hCW`, with isomorphisms, cobase
   change, v-small transfinite composition and retract closure. This uses the
   same formulation as the recorded tree-presentation dependency. Verdict: exact.
5. Isomorphism invariance of W and two-out-of-three: `hWiso : W.RespectsIso`
   and `hW : W.HasTwoOutOfThreeProperty`. I read the Mathlib declarations:
   RespectsIso is pre/postcomposition with isomorphisms, equivalently invariance
   under arrow isomorphisms, and the latter class includes all three implications
   for composable f,g,fg. The former hWiso only stated inclusion of isomorphisms;
   replaced it by the literal node notion. Isomorphisms in W still follow from
   hCW, so no identity-arrow case is lost. Verdict: repaired interface.
6. Approximation hypothesis: `happrox` quantifies over every `P : Type v`,
   PartialOrder P, IsCardinalFiltered P τ, and D : P ⥤ Arrow A, with both
   endpoints τ-presentable at every index and W on its arrow colimit. It then
   quantifies every τ-small E, and produces Q containing E, τ-small,
   `IsCardinalFiltered Q κ`, with its restricted arrow colimit in W. The old
   signature required Q to be τ-filtered, incorrectly strengthening the input;
   repaired to κ. Inherited order is the subtype order. Verdict: repaired.
7. L contained in C, with τ-presentable sources and targets:
   `(L : MorphismProperty A)`, `hLC : L ≤ C`, and the added
   `hL : ∀ ⦃P Q⦄ (f : P ⟶ Q), L f → IsCardinalPresentable P τ ∧
   IsCardinalPresentable Q τ`. `tree.IsGood τ` only bounds the actual chosen
   cells, not every arrow of L, so it did not render this hypothesis by itself.
   Verdict: repaired missing hypothesis.
8. Root X, small well-founded poset T, τ-good L-tree: `{X : A}`, `{T : Type v}`,
   `[PartialOrder T] [WellFoundedLT T]`, `tree : CellularTree L X T`, and
   `hgood : tree.IsGood τ`. I read CellularTree: its predecessor map is the
   canonical map of the diagram; its pushout squares use actual L-arrows.
   IsGood bounds both cell endpoints and strict predecessor sets, without
   presentability of the root. Verdict: exact recorded notions, no private copy.
9. Good whole tree: `htotal : W (colimit tree.diagram).hom`, where the colimit
   is in Under X. Verdict: exact, retained.
10. Given good A₀: `A₀ : Set T` and `hA₀ : IsLowerSet A₀ ∧
    W (CellularTree.subsetObj tree.diagram A₀).hom`. Verdict: both clauses exact.
11. Given arbitrary small seed B₀: `(B₀ : Set T)` and `hB₀ : HasCardinalLT B₀ τ`.
    No downward closure or goodness is required of the seed. Verdict: exact.
12. Existence of B after those inputs: `∃ B : Set T`. Its goodness is now
    `IsLowerSet B ∧ W (CellularTree.subsetObj tree.diagram B).hom`; the second
    conjunct was completely absent before. `HasCardinalLT B τ` and `B₀ ⊆ B`
    render the size bound and containment. Finally `IsLowerSet (B ∩ A₀)` and
    `W (CellularTree.subsetObj tree.diagram (B ∩ A₀)).hom` render goodness of the
    intersection. Verdict: repaired omitted conclusion; every clause is present.

Dependency reading, lem-coef-cellular-tree-presentable-approximations:

- Its category, uncountable regular τ, arbitrary L, root X and τ-good tree are
  the binders of `exists_cellularTreeApproximation`, using the same recorded
  CellularTree. No W is introduced, and no condition on the root or all of L
  is added. The resulting existential P, PartialOrder P, cardinal-filteredness,
  S, F and R retain their original quantifier order. Verdict: exact.
- The first conjunction in CellularTreeApproximation gives the τ-small lower
  supports and τ-presentable endpoints. The existential `tp` is a chosen
  L-tree on each support; `e` is now an isomorphism in Under M_p, identifying
  its actual root arrow with F_p. Verdict: exact, stronger typing of the
  previously unbased arrow isomorphism.
- `CellularTreeLabelledMap` is a constituent of this datum, not a new independent
  mathematical node. It stores vertex maps, their root and order compatibility,
  predecessor maps characterized on their root and every colimit leg,
  compatibility with the predecessor-to-vertex map, equality of both cell
  labels, and commutation with the cell, attaching and target legs. These are
  real structure fields, not a choice from a postponed existence theorem.
  This replaces the old HEq-only data, which did not compare attaching squares.
- The comparison `c p` to the original tree, together with the vertexwise
  IsPushout fields, renders the objectwise pushout identification of trees.
  The stage total pushout map `n` is characterized on all descended-tree colimit
  legs, so it is the specified induced map. The previous predicate supplied
  only an unrelated total pushout square. Verdict: repaired.
- The witness hS renders inclusion-increasing supports. The maps m extend
  F.map to the labelled trees on the common cells; their root maps are exactly
  F.map.left, and the colimit-leg equality identifies their total maps with
  F.map.right. The identity, composition and comparison equalities state the
  required functorial compatibility. Predecessor maps are characterized uniquely
  on the root and all legs, so they inherit these laws too, including empty
  predecessor diagrams. These data were previously absent. Verdict: repaired.
- The natural transformation `a : F ⟶ (Functor.const P).obj
  (Arrow.mk (colimit tree.diagram).hom)` with `Nonempty (IsColimit (Cocone.mk _ a))`
  is exactly the specified colimiting cocone. Its left legs equal R and its
  right legs agree with the labelled comparisons on every cell's colimit leg.
  The old datum contained no assertion that F had this colimit. Verdict: repaired.
- `∀ E, HasCardinalLT E τ → ∃ p, E ⊆ S p` is exactly seed coverage. Retained.
- The final quantifiers are now `∀ Q : Set P, Q.Nonempty → IsFiltered Q → ...`,
  exactly the node's nonempty filtered inherited subposets. They formerly
  required τ-filteredness, losing the subposets the main proof needs. RQ is
  characterized on every root colimit leg. The tree tq on the support union
  has the specified original cell arrows, and its total is isomorphic in the
  undercategory to the restricted arrow colimit. The final IsPushout renders
  the required square to X → Y_union. Its right leg n is characterized on
  every stage's vertex colimit legs, so it is the canonical map, not an
  arbitrary square. Membership in every weakly saturated class containing L
  explicitly renders the node's final weak-saturation assertion. Verdict: repaired.
- I expanded the theorem docstring to all twelve proof steps and imported the
  recorded Mathlib proof interfaces (presentable density and small colimits,
  directed reindexing, elementwise filtered colimits, well-ordering and
  transfinite recursion). The item's docstring now carries all five steps,
  including the role of κ-filteredness and the non-presentable-root argument.

Edge cases: T empty, A₀ empty or all of T, B₀ empty, and seeds not initially
lower are all admitted. Under-X colimits retain Y_empty isomorphic to X.
Empty predecessor diagrams are covered by predecessor_root, not a vacuous
colimit-leg-only condition. Empty supports give identity root arrows; the root
can be zero, initial, or non-presentable. The auxiliary final clause excludes
only Q empty, exactly as its node does, and includes ordinary filtered Q that
are not τ-filtered. κ = aleph0 is admitted; finite κ are already excluded by
IsRegular, exactly as the node requires. τ remains uncountable. The index and
Hom universe is v; u is unrestricted. There are no scheme, characteristic or
cohomological-degree parameters to restrict. No file-local notation, instance,
private declaration, unbound variable or universe was introduced.

Independent searches used different phrases from the first worker:

- msearch leanfinder "weak equivalence closed cellular subposet small enlargement
  compatible intersection": only topological CW subcomplex constructors, not
  this category-theoretic statement.
- msearch loogle "CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty":
  found exactly the Mathlib class already used; opened its source.
- msearch leanfinder "compatible labelled cellular tree descents from presentable
  roots filtered diagram pushout": RelativeCellComplex.Cells and AttachCells,
  which are linear cell-complex data rather than this fixed-label good-poset
  descent system.
- msearch leansearch "Compatible systems of cellular trees over presentable
  objects with prescribed cells and pushout to the original root": AttachCells
  constructors and pushout fields only, not the compatible descent interface.
- msearch grep "descent|subcomplex" in CategoryTheory/Presentable: no hits.
- rg in Mathlib, WeilConjectures, the project's lean/Sheaf and
  dag/lean_names_upstream.json for all four proposed declaration names: none
  already exists. Concept searches used "compact.root", "labelled.*tree",
  "labeled.*tree", "subtree", "good.*subset" and "subcomplex". Only the
  recorded CellularTree and WeakSaturationTreePresentation interfaces and the
  consumer AccessibleIntersectionGenerators were relevant. No exact existing
  statement or missing independent definition node was found.

No natural-language statement correction, new DAG node, target change or citer
audit is needed: both existing node statements are preserved. The dependency's
lean.note and declarations list record the full repaired interface, including
CellularTreeLabelledMap; both lean.statement fields are copied verbatim from
the corresponding theorem signatures. All definitions have real data; the only
two theorem proofs remain sorry. Both files passed the required scompile.py
wrapper with no errors or non-sorry warnings before the final added explicit
weak-saturation clause; final compilation and server preflight are recorded below.

Final validation: scompile.py compiled both delivered modules separately after
all repairs, including the explicit weak-saturation clause, with no errors or
non-sorry warnings. deliver2.py --no-push then printed OK: the delivery passes
the server preflight and compiles (dry-run commit ca0e48286e). The final packet
contains exactly the two Lean modules, their two node records (only lean changed),
and this report. No mathematical statement change or new node is included.
