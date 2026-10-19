## Worker report

The theorem `CategoryTheory.weakSaturation_good_tree_presentation` states all three
conclusions of `lem-coef-weak-saturation-tree-presentation`. Its only postponed proof
is `sorry`. The definition module contains real data and no `sorry`. The original
item statement and proof are unchanged; its statement dependencies gain the new
node `def-coef-good-cellular-tree`. There is no statement correction or disputed clause.
No repair-note entry was found for this item.

Source checked: [Lurie, Higher Topos Theory](https://people.math.harvard.edu/~lurie/papers/HTT.pdf),
Definition A.1.5.1 and Notation A.1.5.2 (printed pp. 799–800), Remark A.1.5.5 and
Lemma A.1.5.6, and Proposition A.1.5.12/Corollary A.1.5.13 (pp. 808–809).
The source gives trees in the undercategory and specifies the diagram-induced
predecessor pushout leg. Its remark gives the relative tree on the inherited
complement poset. The theorem uses those exact notions.

Hypotheses and definitions, clause by clause:

- The fixed small universe is `v`. `A : Type u` is unrestricted in object size;
  `[Category.{v} A]` has small Hom sets. All index types, cardinal and generating
  sets use `v`, so there is no unrelated smaller index universe.
- The cardinal is `κ : Cardinal.{v}`, regularity is `[Fact κ.IsRegular]`, and
  uncountability is `hκ : Cardinal.aleph0 < κ`.
- All small colimits and the small family of presentable generators under small
  cardinal-filtered colimits are exactly `[IsCardinalLocallyPresentable A κ]`.
  This is Mathlib's class extending `HasCardinalFilteredGenerator A κ` and
  `HasColimitsOfSize.{v,v} A`. Its generator class also supplies local smallness.
- The arrow class is `C : MorphismProperty A`. The four conjuncts of `hC` give
  containment of all isomorphisms, arbitrary cobase change (pushouts), small
  continuous transfinite composition, and arrow-category retract closure.
  The underlying Mathlib `TransfiniteCompositionOfShape` carries continuity,
  a bottom-stage identification and a colimit cocone; `RetractArrow` is used by
  `IsStableUnderRetracts`.
- The node's class `K` is written directly as
  `fun {P Q : A} (k : P ⟶ Q) ↦ C k ∧ IsCardinalPresentable P κ ∧
  IsCardinalPresentable Q κ`. There is no substitute compactness predicate.
- `hgen` quantifies a class `I`, with `MorphismProperty.IsSmall.{v} I` and
  membership implying exactly membership in `K`. Its last clause says every
  weakly saturated class `W` containing `I` contains `C`. Together with `hC`
  and `I ⊆ K ⊆ C`, this says exactly that `C` is the weakly saturated closure
  of a small subset of `K`. No lifting-class replacement is assumed.
- An `L`-tree is `CellularTree L X T`, with `T : Type v`, `[PartialOrder T]`
  and `[WellFoundedLT T]`; the latter means the strict order is well-founded,
  equivalently every nonempty subset has a minimal element. The root is an
  arbitrary `X : A` and the actual diagram is `T ⥤ Under X`.
- `source`, `target`, `cell`, and `cell_mem` specify each `P_t → Q_t` in `L`;
  `attach` specifies its attaching arrow, and `targetMap` the other pushout leg.
  `isPushout` uses Mathlib's universal-property predicate on these three arrows
  and `(CellularTree.predecessorMap diagram t).right`. The last arrow is
  `colimit.desc` of the cocone with maps `D.map (homOfLE s.property.le)`.
  Thus an arbitrary map from the predecessor colimit cannot replace this leg.
- `CellularTree.subsetDiagram D E` restricts along the subtype inclusion with
  its inherited order. `subsetObj` is its Mathlib colimit in `Under X`.
  `subsetMap` is `colimit.desc` of the cocone formed from the coprojections into
  the larger restricted colimit. No arbitrary connecting arrow is supplied.
- `tree.IsGood κ` says every cell's source and target are
  `IsCardinalPresentable` and `HasCardinalLT (Set.Iio t) κ`. Presentability is
  Mathlib's Hom-functor preservation of cardinal-filtered colimits. Neither the
  root nor any diagram vertex is required to be presentable.

Conclusions, clause by clause:

- The first conjunct quantifies every `f : X ⟶ Y` with `C f`, and supplies an
  actual small type `T`, its partial order, its well-foundedness, and a tree
  with the precise `K` cell predicate. `tree.IsGood κ` is required, and
  `Nonempty (colimit tree.diagram ≅ Under.mk f)` identifies its root-to-total
  arrow with `f` in the undercategory, rather than only identifying codomains.
- The second conjunct quantifies arbitrary `L`, root, indexing poset and tree.
  `IsLowerSet E`, `IsLowerSet F` and `hEF : E ⊆ F` are precisely downward-closed
  nested subsets. For every weakly saturated `W` containing `L`, it asserts
  `W (CellularTree.subsetMap tree.diagram hEF).right`. This is membership of
  that canonical transition in the intersection defining weak saturation.
- Under `tree.IsGood κ`, the final clause supplies
  `relative : CellularTree L (CellularTree.subsetObj tree.diagram E).right ↥(F \ E)`.
  The subtype inherits its order from `T`; no replacement order is quantified.
  `relative.IsGood κ` and the isomorphism of its colimit with
  `Under.mk (CellularTree.subsetMap tree.diagram hEF).right` give exactly a good
  `L`-tree presentation of the canonical transition with root `Y_E`.

Dependency declarations read and used:

- Recorded statement dependency `def-weil-pbc-category-colimit`:
  `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit`,
  `colimit.desc`, `Cocone`, `IsColimit`. The full declarations/docstrings in
  `HasLimits.lean` and `IsLimit.lean` were read; `colimit` is generated by duality
  from the displayed chosen-limit declaration. Colimits and canonical induced
  maps are used directly, including in the undercategory.
- Mathlib `CategoryTheory.Under`, `Under.mk`, undercategory colimit instances
  (`Limits.Constructions.Over.Basic`), `Monotone.functor`, `IsPushout`,
  `IsCardinalPresentable`, `IsCardinalLocallyPresentable`,
  `MorphismProperty.IsSmall`, `IsStableUnderCobaseChange`,
  `IsStableUnderTransfiniteComposition`, and `IsStableUnderRetracts` are reused.
- The new node's module is publicly imported. All already stated proof dependencies
  are imported without `public`, using their recorded module or Mathlib-match file:
  `Sheaf.CategoryTheory.PresentableCellularFactorization`
  (`SmallObject.exists_cellular_factorization_of_isLocallyPresentable`),
  `Mathlib.SetTheory.Cardinal.Order` (`exists_wellFoundedLT`),
  `Mathlib.Order.RelClasses` (`WellFoundedLT.fix`, `fix_eq`),
  `Mathlib.CategoryTheory.Limits.Types.Filtered` (elementwise colimit lemmas),
  `Mathlib.CategoryTheory.Presentable.Directed` (filtered poset reindexing),
  `Mathlib.CategoryTheory.Presentable.Limits` (small-colimit presentability),
  `Mathlib.CategoryTheory.MorphismProperty.LiftingProperty` (lifting closure),
  and `Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting`.
  `lem-coef-good-tree-idempotent-enlargement` and
  `lem-coef-compact-pushout-retract-descent` have neither a recorded Lean
  declaration nor a Mathlib match in the read snapshot; they are proof-only
  dependencies, not objects needed to type this statement, so no import is invented.
  Their proof steps remain in the theorem's full ten-step docstring.

Edge cases checked mathematically before writing:

- Empty `T` is allowed: no bottom element or nonemptiness is required. All cell
  and goodness conditions are vacuous, and the empty undercategory colimit is
  the initial object `Under.mk (𝟙 X)`, hence the identity root arrow.
- Empty predecessor sets likewise use the undercategory colimit, not an initial
  object of `A`. A minimal cell is attached to the root.
- Empty `E`, empty `F` and `E = F` are admitted. For equality the inherited
  difference poset is empty and its root-to-total arrow is an isomorphism,
  as is the canonical transition. No nonempty-difference hypothesis appears.
- An empty generating subset `I` is allowed; the least weakly saturated class
  is the isomorphisms, and their presentations may use empty trees.
- Roots may be large/nonpresentable even though cell endpoints are presentable.
  Discrete and branching well-founded posets are allowed; no linear-order or
  ordinal assumption was substituted for a partial order.
- The uncountable bound excludes `κ = ℵ₀` and smaller cardinals, as required.
  No characteristic, pointedness or additive structure is relevant or imposed.

Searches for existing notions/statements:

- `msearch.py` LeanFinder, “weak saturation morphism class good cellular tree
  presentation locally presentable category”: eight hits, including
  `HomotopicalAlgebra.RelativeCellComplex` and small-object construction data;
  none is the good-poset tree statement.
- Loogle, “CategoryTheory.MorphismProperty, IsCardinalPresentable”: no hits;
  service reported the latter unqualified name unknown. This unsuccessful
  query was supplemented by the successful semantic searches and direct reads.
- LeanSearch, “good cellular tree well founded poset category”: unrelated
  well-founded order and Noetherian-object hits; no cellular tree.
- For the new definition, LeanFinder “good cellular tree diagram of pushouts
  indexed by well founded poset” and LeanSearch “cellular tree under category
  good predecessor sets” both returned `RelativeCellComplex` and related
  declarations. Reading `RelativeCellComplex/Basic.lean` showed linear-order,
  bottom and successor hypotheses; it does not provide this general tree data.
- `msearch.py grep` with `GoodTree|CellularTree|WeaklySaturated|weaklySaturated`,
  `CellularTree|GoodTree|good.tree|cellular.tree`, and
  `weaklySaturated|WeaklySaturated|CellularTree|GoodTree` in CategoryTheory:
  zero hits. The new node retains the actual final three tool-result JSON lines.
- Direct `rg` of Mathlib, upstream `WeilConjectures`, shared `lean/Sheaf` and
  upstream-name inventory: no general good cellular tree declaration.
  Searching the item id upstream also returned no match. The existing
  `SSet.Enhanced.WeaklySaturated`, `markedWeakSaturation` and `markedSaturation`
  apply to simplicial-set categories, and are not general tree definitions.
  The generic recognition theorem expresses weak saturation inline; this
  delivery follows that convention rather than making a second closure API.
- DAG search found the target and other theorem nodes describing trees inline,
  but no definition node for the general tree. `blueprint_refs.py search
  'cellular tree'` returned zero blueprint nodes; the ancestor command identified
  `prop-coef-integral-exceptional-adjoint`, which is retained in the new node.

Validation: both delivered files are compiled separately through `scompile.py`
in dependency order, with automatic implicits disabled. The initial elaboration
issues in subset-map naturality, retract-property visibility and subtype coercion
were repaired. The docstring spacing warning was repaired. Final clean compile
and `deliver2.py --no-push` results are recorded below when complete.

## New nodes

`def-coef-good-cellular-tree` supplies the missing general definition of an
`L`-tree, its cardinal goodness and its canonical restricted-colimit maps.
The source is HTT Definition A.1.5.1 and Notation A.1.5.2; its source has been
opened and compared with the structures above. Mathlib already provides the
individual undercategories, colimits, pushout squares and presentability, which
are reused. It does not provide this combination with a general well-founded
partial-order index. The semantic, structural and DAG searches above distinguish
this from linear relative cell complexes and combinatorial rooted trees. The
new node cites only the existing colimit definition and inherits this item's
chapter, unit and blueprint ancestor, with the item prepended to its via path.
Its module's seven public declarations are listed in `lean.declarations` and
all carry the new node's source/blueprint docstring. All construction data are
explicit; there is no auxiliary postponed theorem in the definition module.

## Second reading by Q14

I independently opened the base node, both sandbox Lean files, the new definition
node, and the colimit dependency's node and Mathlib declarations. I also read the
recorded proof-dependency statements and the imported cellular-factorization
signature. No repair note exists for this item. There is no `statement_change`:
the original natural-language statement is preserved.

Source: [Lurie, Higher Topos Theory](https://people.math.harvard.edu/~lurie/papers/HTT.pdf),
A.1.5.1–2, A.1.5.5–6 and A.1.5.12–13, opened independently online. These are
ordinary categories; the source's ambient presentability and its uncountability
and accessibility assumptions are present here. The colimit source is Stacks
002F through the recorded Mathlib dependency. No Stacks tag is claimed for the
cellular-tree theorem itself.

My object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

1. Fixed small universe, potentially large category, small Hom sets:
   `universe v u`, `{A : Type u}`, `[Category.{v} A]`. All tree indices, the
   generating set's smallness, and transfinite-composition indices use `v`.
   Verdict: exact; no equality between `u` and `v` is imposed.
2. Uncountable regular cardinal: `(κ : Cardinal.{v}) [Fact κ.IsRegular]` and
   `hκ : Cardinal.aleph0 < κ`. Verdict: exact; the strict inequality excludes
   the countable case required to be excluded by HTT A.1.5.12(i).
3. All small colimits and a small family of κ-presentable generators under
   small κ-filtered colimits: `[IsCardinalLocallyPresentable A κ]`.
   I opened `LocallyPresentable.lean` and `CardinalFilteredPresentation.lean`:
   the class extends `HasColimitsOfSize.{v,v}` and
   `HasCardinalFilteredGenerator`; the latter supplies an essentially small
   object property whose presentations have `J : Type v`, `SmallCategory J`,
   and `IsCardinalFiltered J κ`. Choosing representatives gives precisely the
   node's small generating family. Verdict: exact, with no presentability
   assumption on the arbitrary roots or vertices.
4. Arrow class C is weakly saturated: the four parts of `hC` are
   `isomorphisms A ≤ C`, `IsStableUnderCobaseChange`,
   `IsStableUnderTransfiniteComposition.{v}`, `IsStableUnderRetracts`.
   I opened the definitions: cobase change tests every pushout square;
   transfinite composition uses a well-ordered continuous functor, its bottom
   identification and its colimit; retract closure takes `RetractArrow`.
   Verdict: exact, including all isomorphisms, arbitrary existing pushouts,
   and retracts of arrows rather than only retracts of codomains.
5. K consists of precisely the C-arrows with presentable endpoints:
   the cell predicate is `C k ∧ IsCardinalPresentable P κ ∧
   IsCardinalPresentable Q κ`. I checked `Presentable.Basic`: presentability
   is accessibility of `coyoneda.obj (op P)`, preserving small κ-filtered
   colimits. Verdict: exact; no project-specific compactness substitute.
6. C is generated by a small subset of K: `hgen` gives an `I`,
   `MorphismProperty.IsSmall.{v} I`, membership implying the predicate in
   item 5, and `C ≤ W` for every weakly saturated W containing I.
   `IsSmall.lean` says the actual subtype of `Arrow A` is small, and
   `isSmall_iff_eq_ofHoms` supplies a small indexing family. It is not merely
   essential smallness up to arrow isomorphism. Since I is contained in C
   and `hC` supplies C's closure, the least-class condition gives exactly
   equality with its weak saturation. Verdict: exact.
7. An arbitrary L-tree: `(L : MorphismProperty A)`, root X, small T,
   `[PartialOrder T] [WellFoundedLT T]`, and `CellularTree L X T`.
   Its diagram is `T ⥤ Under X`; `source`, `target`, `cell`, `cell_mem`,
   `attach`, `targetMap`, and `isPushout` are all the data enumerated by the
   node. The last leg of `isPushout` is `predecessorMap diagram t`'s right
   component. Its cocone consists of the actual arrows
   `D.map (homOfLE s.property.le)`, so the square cannot use an unrelated
   predecessor arrow. `IsPushout` includes commutativity and the universal
   property in A. Verdict: exact.
8. Restricted colimits and canonical transitions: `subsetDiagram` uses the
   subtype inclusion with inherited order, `subsetObj` is its colimit in
   `Under X`, and `subsetMap` is the descent of the larger colimit's
   coprojections. I checked the recorded colimit declaration, `IsColimit`
   (including its uniqueness clause), and the undercategory colimit instance
   in `Limits.Constructions.Over.Basic`. Verdict: exact; no extra choices of
   transition arrows enter the statement.
9. κ-goodness: `tree.IsGood κ` requires both endpoints presentable and
   `HasCardinalLT (Set.Iio t) κ` at every vertex. Verdict: exact. In particular
   this does not bound the total number of cells or make the root presentable.
10. First conclusion, every C-arrow has a good K-tree presentation:
    `∀ ... (f : X ⟶ Y), C f → ∃ T ... tree, tree.IsGood κ ∧
    Nonempty (colimit tree.diagram ≅ Under.mk f)`.
    The isomorphism is in `Under X`, so it identifies the structural map from
    X as well as the total object. Verdict: exact.
11. Second conclusion, all downward-closed transitions are in weak saturation:
    `IsLowerSet E → IsLowerSet F → ∀ hEF : E ⊆ F`, followed by membership of
    `(subsetMap tree.diagram hEF).right` in every weakly saturated W
    containing L. Verdict: exact intersection characterization, with the
    quantifiers over arbitrary L, X, T and tree retained.
12. Third conclusion, goodness of the relative presentation: under
    `tree.IsGood κ` there is a `relative : CellularTree L
    (subsetObj tree.diagram E).right ↥(F \ E)` that is good, with total
    colimit isomorphic to `Under.mk (subsetMap tree.diagram hEF).right`.
    The subtype inherits the original order and its well-foundedness;
    no replacement order or extra finiteness hypothesis is chosen.
    Verdict: exact root, index poset and represented transition.

Edge cases: empty T and empty I are permitted. There is no `Nonempty T`,
`OrderBot T` or linearity assumption. I checked Mathlib's `Under.mkIdInitial`:
the empty colimit is the identity of the root, up to its unique undercategory
isomorphism. Thus minimal cells attach to X. Empty E, empty F, E = F, and an
empty difference are all admitted; the relative tree is allowed to be empty.
Empty transfinite composites are covered by the isomorphism condition even
though Mathlib's nonempty well-order representation uses a bottom object.
Large/nonpresentable roots and branching posets are allowed. If A has a zero
object nothing excludes it; no scheme, characteristic, additive structure,
degree n, or nonzero-object hypothesis is introduced. The category itself
cannot be empty under the stated cocompleteness assumption, as in the node.

Independent duplicate searches used different queries from the worker:

- LeanFinder, `well founded partially ordered cellular diagram with small
  predecessor pushouts`: eight hits, led by `RelativeCellComplex.Cells`,
  `RelativeCellComplex` and small-object relative cell complex constructions.
- LeanSearch, `cofibrantly generated weak saturation retracts good diagram
  presentation`: eight model-category and cylinder hits, no requested theorem.
- `msearch.py grep`, `CellularTree|GoodDiagram|GoodPoset|cellularTree|goodTree`:
  no hits. Direct `rg` in upstream `WeilConjectures`, shared `lean/Sheaf`,
  Mathlib CategoryTheory and RelativeCellComplex found related cellular
  factorizations and simplicial constructions, not this general notion or
  statement. Searching DAG definition nodes and `dag/lean_names_upstream.json`
  gave no existing general cellular-tree definition.
- I opened `Mathlib.AlgebraicTopology.RelativeCellComplex.Basic`:
  its structure extends a composition indexed by a `LinearOrder` with
  `OrderBot` and `SuccOrder`. It is not the data of a general well-founded
  partial-order tree and cannot replace `CellularTree` here.

New-node review: `def-coef-good-cellular-tree` is justified by those searches.
Its statement matches HTT A.1.5.1–2 and gives explicit canonical restriction
maps. Generalizing its ambient assumptions to all small colimits introduces
no additional tree notion: those are exactly the constructions used by the
source definition. I matched every structure field and `IsGood` with that
statement. Its only statement dependency is the recorded colimit notion.
Its seven public declarations all have source/blueprint docstrings; definitions
have actual construction data and no postponed theorem. The node has the
required definition kind, split status, empty proof/proof-dependency fields,
null proof origin and Mathlib match, three kinds of searches, creation record,
ancestor/via, chapter/unit, audits and Lean record. No existing node was
privately copied and no dependency module is needed.

Mismatches and repairs: no object, hypothesis, conclusion, definition, universe,
or source mismatch was found. Four proof-plan dependency lists split node IDs
across lines (`def-` or other hyphenated fragments); I rewrapped these so each
ID is intact and searchable. No declaration signature, construction, natural
statement, proof plan step, or node metadata changed. The complete ten-step
proof remains in the theorem's docstring. There is one postponed theorem with
proof `sorry` and no proved theorem. Both node `lean.statement` strings were
checked verbatim against their file signatures; all Lean lines have at most
100 characters and `autoImplicit` is false.

Validation after the docstring repair: the prescribed `scompile.py` invocation
compiled both sibling modules separately in dependency order, including their
library-path checks. Exit status 0, no errors and no warnings; final library
checks took 1.9 seconds for `CellularTree` and 1.7 seconds for the theorem module.

Delivery dry run: `deliver2.py Q14 lem-coef-weak-saturation-tree-presentation
--no-push` reported `OK (dry run): commit d4e2f566c6 passes the preflight and
compiles; nothing pushed`. Only the two modules, their two node records and
this report were staged. Shared-fetch contention cleared without a tool repair.
