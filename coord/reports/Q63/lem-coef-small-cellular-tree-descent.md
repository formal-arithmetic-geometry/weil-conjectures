## Worker report

Item: lem-coef-small-cellular-tree-descent. The new module
`Sheaf.CategoryTheory.SmallCellularTreeDescent` states
`CategoryTheory.smallCellularTree_descent`, with its sole proof `sorry`.
The supporting definition `CategoryTheory.CellularTree.rootChangeMap` is the actual canonical
map on undercategory colimits: `colim.map α ≫ colimit.post E (Under.map f)`.
It contains no postponed data or proof. It is an owning-node helper for the comparison maps,
as authorized in the brief; no new mathematical notion or additional DAG node is needed.

The source was read online at
[HTT](https://people.math.harvard.edu/~lurie/papers/HTT.pdf), Lemma A.1.5.11
(printed pp. 806-807), including its induction, together with Definition A.1.5.1,
Remark A.1.5.3 and Lemma A.1.5.6. The source's statement has the apparent typo
“X is κ-compact” immediately after introducing X₀; the proof and the DAG correctly require
presentability of the new root. The DAG additionally assumes presentable cell targets and
concludes presentability of the descended total object, exactly as its Step 7 proves.
The current main-20261015 blueprint's prop-coef-integral-exceptional-adjoint is the
recorded ancestor, not this auxiliary lemma's own statement. No node correction is needed.

Hypotheses and conclusions, clause by clause:

- Small universe: `v`; ambient object universe: arbitrary `u`. `{A : Type u}` and
  `[Category.{v} A]` encode ordinary categories with small Hom sets. All indexing types,
  cardinal bounds, and transfinite-composition sizes use `v`, matching the dependency.
- The uncountable regular cardinal is `(κ : Cardinal.{v}) [Fact κ.IsRegular]`
  and `(hκ : Cardinal.aleph0 < κ)`.
- Local κ-presentability is `[IsCardinalLocallyPresentable A κ]`. Mathlib's class extends
  `HasCardinalFilteredGenerator A κ` and `HasColimitsOfSize.{v,v} A`: a small generating
  family of κ-presentables with small κ-filtered presentations, and all small colimits.
- The arbitrary arrow class is `(L : MorphismProperty A)`. The hypothesis `hL` says,
  for EVERY arrow `i : P ⟶ Q` in `L`, that BOTH `P` and `Q` are κ-presentable.
  It imposes neither small generation nor weak saturation on `L` itself.
- The original root is `(Z : A)` with no presentability hypothesis. The original tree is
  `(tree : CellularTree L Z T)` on `(T : Type v) [PartialOrder T] [WellFoundedLT T]`.
  Its specified cells, attaching maps, and canonical predecessor pushouts are exactly
  the dependency's existing structure. `hT : HasCardinalLT T κ` means `|T| < κ`.
- The new root and root map are the existential `(M : A) (f : M ⟶ Z)`.
  The existential `small : CellularTree L M T` keeps the SAME `T`, order, and well-founded
  structure. `IsCardinalPresentable M κ` is the asserted root presentability.
- The endpoint `N` is `(colimit small.diagram).right`; `IsCardinalPresentable ... κ`
  is its presentability. Naming this chosen colimit instead of adding an independent
  existential `N` is equivalent by uniqueness of colimits. Its structure arrow
  `(colimit small.diagram).hom` is exactly `h : M ⟶ N`.
- Objectwise pushout is the natural transformation
  `α : small.diagram ⟶ tree.diagram ⋙ Under.map f`, together with
  `∀ t, IsPushout (small.diagram.obj t).hom f (α.app t).right (tree.diagram.obj t).hom`.
  Because `Under.map f` precomposes structural arrows, naturality gives compatibility
  of the comparison with every order arrow and with the root. Pushout uniqueness gives
  the claimed natural isomorphism from objectwise pushout to the original diagram.
- The comparison also respects the specified cellular data, not only diagram vertices.
  For each `t`, an isomorphism `e : Arrow.mk (small.cell t) ≅ Arrow.mk (tree.cell t)`
  identifies its source, target, and cell arrow. The two following equalities intertwine
  the target map and attaching map. The latter uses `rootChangeMap` on the strict
  predecessor diagram (restriction is `Functor.whiskerLeft` along its subtype functor),
  so it is the canonical predecessor comparison, including for empty predecessors.
  These conditions spell out the source's “isomorphism of S-trees”. They do not require
  arbitrary maps to be in an isomorphism-stable arrow class; both trees have cells in `L`.
- The asserted total pushout is `IsPushout (colimit small.diagram).hom f
  (CellularTree.rootChangeMap f α).right (colimit tree.diagram).hom`.
  Thus the bottom map is precisely the original canonical `Z ⟶ Y_T`, and the right
  map is induced by the SAME natural comparison used at every vertex. No unrelated
  existential arrow is substituted for the canonical map.
- Weak saturation of `h` is quantified over every `W : MorphismProperty A` containing `L`,
  containing all isomorphisms, and stable under cobase change, small transfinite composition,
  and arrow retracts; its conclusion is `W (colimit small.diagram).hom`.
  This is the same least-class encoding used by the statement dependency and is exactly
  membership in the weakly saturated closure, without introducing a competing definition.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.WeakSaturationTreePresentation`,
  `CategoryTheory.weakSaturation_good_tree_presentation`: its full signature and docstring
  were read. The transition conclusion uses exactly the same weak-saturation quantifier.
  Its module is publicly imported. Its auxiliary small-generated class `C` is not made an
  extra assumption here: only its unconditional tree-transition clause is relevant.
- Its public dependency `Sheaf.CategoryTheory.CellularTree`:
  `CategoryTheory.CellularTree`, `CellularTree.subsetDiagram`, `subsetObj`,
  `predecessorMap`, and `IsGood` were read. The statement reuses the existing tree structure.
- Mathlib `CategoryTheory.Presentable.LocallyPresentable`:
  `CategoryTheory.IsCardinalLocallyPresentable`; and `Presentable.Basic`:
  `CategoryTheory.IsCardinalPresentable`, whose definition is preservation by `Hom(X,-)`
  of κ-filtered colimits.
- Mathlib `CategoryTheory.Comma.Over.Basic`: `Under.map`, `Under.forget`, and `Under.mk`;
  `CategoryTheory.Limits.HasLimits`: `colimit`, `colim.map`, and `colimit.post`.
  The helper is only a composition of those existing canonical constructions.
- The proof imports `Mathlib.CategoryTheory.Presentable.Directed` for
  `IsCardinalFiltered.exists_cardinal_directed` (the reindexing node's Mathlib match),
  `Mathlib.CategoryTheory.Presentable.Limits` for
  `isCardinalPresentable_of_isColimit` (small-colimit-presentability node), and
  `Mathlib.CategoryTheory.Limits.Types.Filtered` for the elementwise-colimit node's
  declarations, including `Limits.Types.jointly_surjective` from its public imports.
  `def-weil-pbc-category-colimit` is realized by Mathlib's `colimit` and its cocone API.
  These are all the stated proof-dependency modules; no proof-import cycle is introduced.

Edge cases checked mathematically before finalizing the statement:

- `T = ∅`: undercategory colimits have underlying object isomorphic to the root, so
  `N ≅ M`, `h` is an isomorphism, and the total pushout is `Z`. The theorem imposes
  no vertex or cell condition and DOES retain the root map and total pushout condition.
  Using ordinary colimits of the underlying empty diagram would be wrong; the file
  consistently uses colimits in `Under M` and `Under Z`.
- A single cell with no predecessors: the predecessor colimit is the root, and the
  attaching comparison equation is still meaningful through `rootChangeMap`.
- Disconnected or incomparable cells: comparisons are natural on the full poset and all
  colimits are in the undercategory; the root is included in each component's calculation.
- Non-presentable `Z` (for example, a large set) is admitted. Its presentable-stage
  factorization uses only presentability of cell sources; `Z` is never restricted.
- Empty `L` permits the empty tree and does not exclude it by any nonempty-index binder.
- Arbitrary cell arrows, including nonmonomorphisms, remain allowed. The square condition
  is the universal-property `IsPushout`, not an injection or subobject condition.
- No equality of the object and Hom universes is imposed. The index and cardinal universes
  use the same `v` as the given small-Hom-set universe, following the recorded dependency.

Searches for an exact existing statement (2026-10-17):

- `msearch.py`, leanfinder: “A small cellular tree with fewer than kappa presentable cells
  descends by pushout from a kappa presentable root”. Eight hits, including
  `SmallObject.relativeCellComplexιObj`, `SmallObject.attachCellsOfSuccStructProp`,
  and `RelativeCellComplex.Cells`. These construct individual cells or relative cell
  complexes; none descends a specified branching tree to a single presentable root.
- `msearch.py`, loogle: `CategoryTheory.IsCardinalPresentable, "pushout"`.
  Zero hits.
- `msearch.py`, grep: `presentable|compact` in `CategoryTheory/SmallObject`.
  Three hits, all explanatory comments in `IsCardinalForSmallObjectArgument` or `Basic`;
  no compact-root tree descent statement.
- `msearch.py`, leansearch: “A small cellular tree in a locally presentable category
  descends by pushout from a presentable root”. Eight hits about single cell pushouts,
  including `SmallObject.functorObj_isPushout` and `AttachCells.isPushout`; no match.
  Raw search records are in sandbox `searches.jsonl`.
- `rg` in upstream `WeilConjectures`, project `lean/Sheaf`, and Mathlib category theory
  for `smallCellularTree_descent`, small-cellular descent, and cellular-tree descent:
  the project's `AccessibleIntersectionGenerators.lean` only cites this item's blueprint
  identifier in its proof plan; no existing statement. A separate `grep -rn` for this
  exact node id in upstream `WeilConjectures` has no hit. The upstream name inventory
  similarly has no declaration. Searches for root-change comparison names found no
  existing `CellularTree.rootChangeMap`; the helper composes the existing colimit maps.

Validation: the final module compiles through the prescribed `scompile.py`, both as a
sandbox file and under its actual module name, with no errors or warnings. The first
elaboration of the cell-compatibility clause exposed the missing `Functor.` qualification
on `whiskerLeft`; that was repaired and recompiled. Every variable and universe is bound
explicitly, with `set_option autoImplicit false`. There is one theorem with `sorry`, with
the complete eight-step DAG proof plan in its docstring, and one actual helper definition.
No new nodes, dependency repairs, or statement corrections; only the item's `lean` field
changes. No statement dispute found.

## Second reading by Q63

Independent second reading, 2026-10-17. I opened the sandbox node and complete module,
the base node, the recorded statement dependency and its module, and the underlying
`def-coef-good-cellular-tree` node and `CellularTree.lean`. Only the item's `lean` field
differs from the base. There is no `statement_change`, new node, dependency-module repair,
or repair note for this item. The Lean statement says exactly what the node says;
no Lean or node changes were needed.

Source check: I independently opened [HTT](https://people.math.harvard.edu/~lurie/papers/HTT.pdf),
Definition A.1.5.1, Notation A.1.5.2, Remark A.1.5.3 and Lemma A.1.5.6
(printed pp. 799-801), and the full statement and induction of A.1.5.11
(printed pp. 806-807; PDF pages 823-824, zero based). This is an ordinary-category
result, not a Stacks theorem, so there is no applicable Stacks .tex source place.
The ambient presentability and cardinal accessibility assumed there are rendered
by local cardinal presentability here. The printed claim of compactness for the old
root is a typo: the proof chooses the new root among the compact presentation terms.
The node already uses that meaning. The source only needs presentable cell sources;
the node explicitly assumes both endpoints presentable and adds presentability of the
total object. This addition is valid by the root-augmented small-colimit argument in
its Step 7; it is faithfully retained, not silently attributed to the bare source lemma.

Here is my inventory of the node, matched against the actual signature:

| Object, hypothesis, or conclusion | Lean rendering and verdict |
| --- | --- |
| Fixed small universe; ordinary category with small Homs | `{A : Type u} [Category.{v} A]`; indices and cardinals use `v`, with unrestricted object universe `u`. Exact. |
| Uncountable regular cardinal | `(κ : Cardinal.{v}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)`. Exact. |
| All small colimits and a small cardinal-filtered generating family of presentables | `[IsCardinalLocallyPresentable A κ]`. I read this Mathlib class and `HasCardinalFilteredGenerator`/`IsCardinalFilteredGenerator`; these give precisely the node's cocompleteness and generation condition. Exact. |
| Arbitrary arrow class whose sources and targets are presentable | `(L : MorphismProperty A)` and `hL`, quantifying over every arrow in `L` and asserting `IsCardinalPresentable P κ ∧ IsCardinalPresentable Q κ`. No smallness, monicity, saturation or extra condition on `L`. Exact. |
| Arbitrary root and a small well-founded partially ordered index | `(Z : A) (T : Type v) [PartialOrder T] [WellFoundedLT T]`. No presentability hypothesis on `Z`. Exact. |
| Given cellular tree with fewer than the cardinal's number of cells | `(tree : CellularTree L Z T) (hT : HasCardinalLT T κ)`. The recorded structure has the actual cell arrows in `L`, attaching maps and pushout squares with the diagram-induced predecessor maps. Exact. |
| New presentable root and map to the old root | `∃ (M : A) (f : M ⟶ Z) ...`, followed by `IsCardinalPresentable M κ`. Exact quantifier order. |
| New tree on the same poset | `(small : CellularTree L M T)` uses precisely the original `T` and its order and well-foundedness instances. Exact. |
| Presentable total object and its root arrow | `N` is represented by the chosen `(colimit small.diagram).right`, and `h` by `(colimit small.diagram).hom`; the second presentability conjunct supplies the required property. A separate existential colimit object is equivalent by the unique undercategory colimit isomorphism. Exact. |
| Original tree is the objectwise pushout | `α : small.diagram ⟶ tree.diagram ⋙ Under.map f` and the vertexwise `IsPushout` conjunct. `Under.map f` precomposes root arrows; thus naturality includes the root and every order map. These natural pushout squares give exactly the natural isomorphism with the objectwise pushout diagram. Exact. |
| The tree isomorphism includes the specified cells | For every `t`, `e : Arrow.mk (small.cell t) ≅ Arrow.mk (tree.cell t)` identifies cell sources, targets and arrows. Its two displayed equations identify the target and attaching maps. The predecessor comparison is induced from the restriction of the very same `α`. Together with the vertexwise pushouts these are precisely isomorphism of cellular trees, not merely isomorphism of their total objects. Exact. |
| Canonical total pushout square | `IsPushout (colimit small.diagram).hom f (CellularTree.rootChangeMap f α).right (colimit tree.diagram).hom`. Both horizontal maps are the root structure maps of the chosen undercategory colimits; the vertical map is induced by `α`. Exact, including its canonical-map requirement. |
| The top arrow lies in the weakly saturated closure of `L` | The final quantifier over every `W` containing `L` and all isomorphisms and closed under cobase change, small transfinite composition and arrow retracts asserts `W (colimit small.diagram).hom`. This is the least-class condition used by the recorded dependency. Exact. |

Dependency and helper inspection: `weakSaturation_good_tree_presentation` is the recorded
statement and its second conjunct supplies the tree-transition result for arbitrary `L`.
Its outer `C`, closure and generation hypotheses do remain in its signature; the worker's
word "unconditional" means independent of `L`, not absence of those binders. They can be
satisfied with `C` the isomorphisms and the empty generating class, so using this conjunct
does not add an assumption to the present theorem. `CellularTree`, `subsetDiagram`,
`subsetObj`, `predecessorMap` and `IsGood` match their node; there is no private replacement.
I also read Mathlib's `IsCardinalPresentable` (the Hom-functor preservation condition),
`Under.map` (the contravariant restriction functor), `colimit.post`, and the undercategory
colimit existence instances. The helper `rootChangeMap` is real data:
`colim.map α ≫ colimit.post E (Under.map f)`. It is the canonical induced map even when
`Under.map f` does not preserve the colimit. Its use on strict predecessors has exactly
`subsetDiagram`'s restricted diagram as domain, and its equations have the right directions.
The helper belongs to this comparison construction and needs no independent definition node.

The proof-only imports are appropriate: I checked the actual signatures of
`IsCardinalFiltered.exists_cardinal_directed` and
`isCardinalPresentable_of_isColimit`, including its bound on `Arrow K` and small-Hom
condition. The latter are available because the root-augmented poset is small and its
arrow cardinal is less than `κ`. The Type-valued filtered-colimit import supplies the
recorded elementwise leaf; the chosen-colimit dependency is already publicly imported.
The theorem docstring follows all eight DAG proof steps, including tails, successor
factorization without presentability of the old root, limit gluing, endpoint presentability
and saturation. Both declarations have source and blueprint docstrings. There is one
named theorem with whole proof `sorry`; the helper has no postponed data or proof.

Edge cases checked independently:

- `T` empty: the two undercategory colimits are the identity root arrows up to canonical
  isomorphism. Thus `N ≅ M`, `h` is an isomorphism, and its pushout is the identity at `Z`.
  Neither a nonempty-index binder nor an underlying empty colimit discards this case.
- One vertex, and arbitrary incomparable vertices: predecessor colimits include the root.
  The same canonical predecessor comparison and attaching equation remain meaningful.
- Empty `L`: the empty tree is allowed; a nonempty tree would already require a member
  of `L`, as it should. No nonemptiness of `L` was introduced.
- A zero or initial root, arbitrary nonpresentable old root, and nonmonic cell arrows
  are all admitted. No additive, field, characteristic or scheme hypotheses occur.
  Degree-zero and empty-scheme cases therefore introduce no separate restriction here.
- The small index universe is exactly the small Hom/cardinal universe `v`, while `u`
  remains independent. No implicit universe equality or finite index restriction was added.

Independent searches, with different wording from the worker:

- `msearch.py ... leanfinder "An entire well founded cell attachment diagram is a base
  change from a small presentable object"`: eight hits, including `RelativeCellComplex`,
  `RelativeCellComplex.attachCells` and small-object attachment constructions. Their
  signatures concern well-ordered cell complexes or individual attachment operations,
  not descent of the specified branching tree and its attaching maps to one new root.
- `msearch.py ... loogle '"IsCardinalPresentable", "colimit"'`: twelve hits, chiefly
  the single-object factorization/equality lemmas and small-colimit presentability.
  None provides whole-tree root descent.
- `msearch.py ... leansearch "A diagram with fewer than kappa cell attachments can be
  obtained by pushing out a diagram based at a kappa presentable object"`: eight hits,
  including `AttachCells.isPushout`, `AttachCells.mk`, and
  `isCardinalPresentable_of_isColimit`; no exact statement.
- Independent `rg` searches for descent/root/presentable/compact in Mathlib's
  `CategoryTheory/SmallObject` and `Presentable`, and for cellular trees, root-change
  maps and tree descent in upstream `WeilConjectures`, project `lean/Sheaf`, the upstream
  name inventory and DAG nodes, found the recorded tree modules and related DAG nodes.
  None already states this theorem or defines its root-change helper. The larger
  cellular-tree-approximation DAG node has no usable matching Lean declaration.

Mismatch and change log: no mismatch in the Lean statement or definitions was found.
I retained the module and node verbatim and appended this independent audit only.
The preserved node `lean.statement` was checked byte-for-byte against the signature
before `:= by`; every variable and universe is explicitly bound. Validation and delivery
are recorded below after the prescribed wrapper checks complete.

Second-reader validation: the prescribed `scompile.py` compiled the sole delivered
module separately as `Sheaf.Stage2.Sandbox0` and as
`Sheaf.CategoryTheory.SmallCellularTreeDescent`, both clean (1.6 seconds each), with
no errors or warnings. A direct text comparison confirmed exact `lean.statement`
equality and all Lean lines at most 100 characters. No declaration was proved,
no mathematical statement changed, and no target or live source was edited.
