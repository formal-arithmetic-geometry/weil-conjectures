## Worker report

Item: `lem-coef-infinity-kan-mapping-restriction`, group Q45, stage 2.

The delivery adds `lean/Sheaf/CategoryTheory/KanMappingRestriction.lean`, module
`Sheaf.CategoryTheory.KanMappingRestriction`. Its main statement is
`SSet.Enhanced.kan_mapping_restriction`, with its sole theorem proof `sorry`.
All eleven helper definitions have real data or explicit predicates; there is no
choice from an unproved existence theorem. All twelve declarations are listed in
`lean.declarations` and carry this node's blueprint/source docstring.

The shared checkout predates this node. I read and copied the current node from
`dag/nodes/sec-six-functors/lem-coef-infinity-kan-mapping-restriction.json` on the
server, together with its statement dependency's current record. There was no
repair note for the item. The node copy changes only `lean`. No statement correction,
new node, dependency module, or other DAG statement is needed.

Sources read: [Kerodon Corollary the project server, 030M](https://kerodon.net/tag/030M) and
[Definition the project server, 02YQ](https://kerodon.net/tag/02YQ). The first gives restriction
as a trivial Kan fibration under either pointwise Kan hypothesis; this node asks
only for the equivalence consequence. The latter specifies the canonical slice
contractions used for the two pointwise hypotheses. The node's coherent
transformation/comma convention is exactly the already recorded dependency's
convention, reused here.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Quasicategories `C,E` | `{C E : SSet.{u}} [Quasicategory C] [Quasicategory E]`; the ambient universe is arbitrary and explicitly bound. |
| Full subcategory `A` of `C` | A predicate `P : C _⦋0⦌ → Prop` and the existing `fullSubcomplex C P`. Its simplices are exactly those with all vertices satisfying `P`, so this parametrizes every full simplicial subcategory without requiring a new fullness notion. |
| Functors `F,G : C → E` | `(F G : C ⟶ E)`, simplicial maps between the specified quasicategories. |
| Over-slice simplices ending at `c` | `kanSlice A c true`: a simplex `s : C[n+1]`, with `C.map (kanEndpoint true n).op s = c`; its entire opposite face belongs to `A.obj n`. |
| Fiber product `A ×_C C_/c` | The second subtype condition is exactly membership of that opposite face in `A`, degree by degree. `kanSliceProjection` is the opposite-face map to `C`. |
| Over-slice operators | `kanExtend true a = appendLast a`, using the dependency's recorded `appendLast`; the new last vertex is fixed. |
| Dual under-slice | `kanSlice A c false` fixes the first vertex, with its face opposite vertex zero in `A`. Its operators are `kanPrependFirst`, which fixes the new first vertex. |
| Canonical cocone/cone | `kanSliceTransformation A c over : kanSlice A c over ⊗ Δ[1] ⟶ C`. `kanPrism true` retains vertices labelled zero and sends vertices labelled one to the last vertex; its dual sends zero-labelled vertices to the first vertex and retains the one-labelled vertices. Thus this is the canonical join contraction converted to the dependency's coherent-transformation convention, with all higher simplices retained. |
| Apply `F`/`G` to that specific cocone/cone | In `IsPointwiseKanDiagram A F over`, the underlying comma vertex is fixed by the equality `t.1 = (F.app _ c, diagramVertex (MonoidalClosed.curry (kanSliceTransformation A c over ≫ F)))`. Both the apex and the entire coherent transformation are fixed, rather than only its individual edges. |
| Every canonical `F` cocone is colimiting | `IsPointwiseKanDiagram A F true`: for every vertex `c`, the uniquely specified comma vertex is initial. With `!true = false`, this comma object is definitionally the dependency's `coconeCategory (kanSliceProjection A c true ≫ F)`; `IsInitial` is precisely its recorded `IsColimiting` condition. |
| Or every canonical `G` cone is limiting | `IsPointwiseKanDiagram A G false`: `!false = true` gives `coneCategory`, and `IsTerminal` is its recorded `IsLimiting` condition. The main hypothesis is an `Or` between the two complete universal hypotheses; it is not a per-object mixture. |
| Map of the two right-pinched mapping spaces | `diagramMappingRestriction A F G = mappingSpaceMap (diagramRestriction A E) (diagramVertex F) (diagramVertex G)`. Both `mappingSpace` and `mappingSpaceMap` are reused from the dependency. |
| The restricted diagrams in the codomain | `(diagramRestriction A E).app _ (diagramVertex F)` is definitionally `diagramVertex (A.ι ≫ F)`, and likewise for `G`; checked in a scratch example. |
| The comparison is restriction itself | `diagramRestriction A E = (MonoidalClosed.pre A.ι).app E`, the existing canonical internal-hom precomposition. There is no arbitrary comparison map hypothesis. |
| Equivalence of spaces | `IsWeakHomotopyEquivalence (diagramMappingRestriction A F G)`, reusing the dependency's geometric-realization definition, including components and all positive based homotopy groups. |
| Coherent naturality under pre/postcomposition | The second conjunct quantifies over every simplicial set `K` and coherent family `H : K ⟶ (ihom C).obj E`. It states `uncurry (H ≫ diagramRestriction A E) = A.ι ▷ K ≫ uncurry H`. Thus restriction acts on the entire parameterized coherent diagram. It includes every standard-simplex parameter, higher compatibility, and family representing pre/postcomposition, rather than asserting only equality on homotopy-category arrows. |

`IsPointwiseKanDiagram` uses an existential only to express that the explicitly
fixed pair is a vertex of the recorded comma subcomplex and satisfies its universal
property. The equality fixes all its data; different witnesses differ only in a
subtype proof. No definition chooses such a witness, and no arbitrary cone or
noncanonical map is substituted. The slice constructions are the notions introduced
inline by this item's own statement, so their helpers belong to this module rather
than to a new independent DAG node.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.fullSubcomplex`,
  `appendLast`, `diagramVertex`, `constantDiagrams`, `comma`, `coneCategory`,
  `coconeCategory`, `IsInitial`, `IsTerminal`, `IsColimiting`, `IsLimiting`,
  `mappingSpace`, `mappingSpaceMap`, and `IsWeakHomotopyEquivalence`. I read the
  complete current source through `scompile.py --source`, including the signatures,
  docstrings, and concrete endpoint/subtype conventions.
- Mathlib primitives: `SSet.Subcomplex`, `Subcomplex.ι`, `stdSimplex.objEquiv`,
  `SimplexCategory.δ`, `SimplexCategory.const`, internal hom `ihom`,
  `MonoidalClosed.pre`, `MonoidalClosed.curry`, `MonoidalClosed.uncurry`, and
  `MonoidalClosed.uncurry_pre_app` (the latter checked in the scratch test).
- Already stated proof dependencies are imported without `public`:
  `Sheaf.Paper.TrivialKanHomotopyEquivalence`, declaration
  `SSet.exists_section_homotopy_equivalence`;
  `Sheaf.CategoryTheory.RightPinchComparison`, declaration
  `SSet.Enhanced.right_pinch_comparison` (current source and its full signature read).
  The Mathlib leaf `def-weil-pbc-trivial-kan-fibration` is imported via
  `Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations`; read
  `SSet.modelCategoryQuillen.I` at line 38, `SSet.boundary` and `boundary_zero`,
  and `CategoryTheory.MorphismProperty.rlp` at line 40.
- The remaining proof dependencies `lem-coef-infinity-parameter-cone-extension`,
  `def-coef-infinity-relative-cone`, and `lem-coef-infinity-relative-kan-existence`
  had no Lean records when read. Their modules cannot yet be imported. They are
  proof dependencies only; this delivery does not state them. All seven proof
  steps, including those future inputs, are retained in the main docstring.

Edge cases checked before writing and against the resulting definitions:

- Empty `C`: both pointwise hypotheses quantify over the empty vertex type; there
  is no nonemptiness assumption on `C`, `E`, or the mapping spaces.
- Empty `A` and empty over/under slices: the subtype slice remains empty in every
  degree, its contraction is the unique map out of the empty product, and the
  universal property still requires the specified apex to be initial/terminal.
  Empty slices are not silently discarded or given an extra inhabitedness condition.
- `A = C`: `P` can be the always-true predicate. Full restriction and identity
  diagrams are included, with no proper-subcategory condition.
- Degree zero: `kanSlice` uses edges with one fixed endpoint; its projection is
  the other endpoint. Both possible parameter vertices in `kanPrism` give the
  specified diagram/apex in the correct order. No dimension-zero horn filling is
  imposed; the proof plan explicitly includes mapping-space degree zero.
- Both alternatives use the same right-pinched model, including the entire
  constant initial face, with no change to homotopy-category Hom sets.
- Universe `u` is arbitrary, as in the recorded enhanced-diagram dependency. All
  variables and universes are explicitly bound; `autoImplicit` is disabled.

Searches actually run (2026-10-16 UTC):

1. `msearch.py ... leanfinder` query: "Restriction of mapping spaces between
   quasicategory diagrams is an equivalence for pointwise left or right Kan
   extensions". Eight hits, including ordinary
   `CategoryTheory.Functor.LeftExtension.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv`,
   `...isPointwiseLeftKanExtensionEquivOfGuitartExact`, and
   `SSet.StrictSegal.isPointwiseRightKanExtension`; no exact result for arbitrary
   quasicategories. Read Mathlib `Functor/KanExtension/Basic.lean:199-207` and
   `Pointwise.lean:35-65`: their ordinary-category Hom sets and ordinary
   pointwise (co)limits do not state this coherent mapping-space assertion.
2. `msearch.py ... loogle` query `"Quasicategory", "KanExtension"`: zero hits.
3. `msearch.py ... grep` query `slice|Slice|KanExtension|mappingSpace`, subdirectory
   `AlgebraicTopology/Quasicategory`: zero hits. An earlier direct variant
   `slice|Slice|over|Under` likewise supplied no relevant slice API.
4. `msearch.py ... leansearch` query: "Mapping spaces of natural transformations
   restrict equivalently when a diagram is pointwise Kan extended in a
   quasicategory". Eight ordinary-category results, including
   `Functor.homEquivOfIsLeftKanExtension`; its signature read at the lines above
   gives only an ordinary Hom-set bijection.
5. Direct `rg` of Mathlib `AlgebraicTopology/SimplicialSet` and `Quasicategory`
   for slice/over/under constructions found no such construction. Direct `rg`
   of the upstream `WeilConjectures` tree for `mapping.*restriction|restriction.*mapping`
   found only an unrelated torsor-gluing comment; `grep -rn` of the exact item ID
   found nothing. Searches in `lean/Sheaf/CategoryTheory` found ordinary site
   slices and the already used `EnhancedDiagramsCones` primitives, not this lemma.
6. Direct name searches in `dag/lean_names_upstream.json`, all Mathlib, upstream
   `WeilConjectures`, and `lean/Sheaf` found none of the twelve new declaration
   names. A separate read-only server search of current `lean/Sheaf` and the
   upstream-name map likewise found no collision or existing statement.

Validation: the delivered module compiled cleanly with `scompile.py` in its
sandbox and final module path (about 3 seconds each in the final check), without
warnings. An additional scratch file, outside the delivered `lean/` tree, compiled
cleanly and checked the restricted endpoint vertices by `rfl` and the complete
arbitrary-parameter restriction formula with Mathlib's `uncurry_pre_app`.
No scratch declaration is included in the delivery. The required `deliver2.py
Q45 lem-coef-infinity-kan-mapping-restriction --no-push` dry run is the final gate.

No `STATEMENT-DISPUTED` or source/node fault was found. The module contains one
postponed theorem, the item itself, and no other postponed declaration.

## Second reading by Q45

I reread the node statement, its source place, the recorded dependency
`def-cbc-enhanced-diagrams-cones`, and the complete delivered module. The
item-by-item match is:

| Node object, hypothesis, or conclusion | Lean rendering and verdict |
| --- | --- |
| Quasicategories `C` and `E` | `{C E : SSet.{u}} [Quasicategory C] [Quasicategory E]`; the universe is explicit and unrestricted. Matches. |
| Full subcategory `A ⊆ C` | `P : C _⦋0⦌ → Prop` and `fullSubcomplex C P`; the subcomplex condition requires every vertex of every simplex to satisfy `P`. Matches the full-subcategory convention. |
| Functors `F,G : C → E` | `(F G : C ⟶ E)`. Matches. |
| Over-slice `A_{/c}` | `kanSlice A c true`; its `(n+1)`-simplex has fixed last vertex `c` and its opposite `n`-face in `A`. `kanSliceProjection` is that face map. Matches. |
| Canonical over cocone | `kanExtend true = appendLast` and `kanSliceTransformation A c true`; the complete coherent prism appends the fixed final vertex. Matches. |
| Under-slice `A_{c/}` | `kanSlice A c false`; its first vertex is fixed to `c` and the opposite face is in `A`. Matches. |
| Canonical under cone | `kanExtend false = kanPrependFirst` and `kanSliceTransformation A c false`; the dual complete coherent prism fixes the initial vertex. Matches. |
| Pointwise left Kan hypothesis | `IsPointwiseKanDiagram A F true`: the comma vertex is fixed to `(F.app _ c, diagramVertex (cocone transformation))`, and `IsInitial` is the dependency's colimiting-cocone condition. The `∃` only packages the fixed subtype proof. Matches. |
| Pointwise right Kan hypothesis | `IsPointwiseKanDiagram A G false`: `!false` selects the dependency's cone category and `IsTerminal` is its limiting condition. Matches. |
| Alternative is global | The theorem assumes one `Or` between the two complete `∀ c` predicates, with no per-object mixture. Matches. |
| Mapping-space restriction | `diagramMappingRestriction` is `mappingSpaceMap (diagramRestriction A E) ...`; `diagramRestriction` is the canonical `(MonoidalClosed.pre A.ι).app E`. It is restriction itself. Matches. |
| Equivalence conclusion | `IsWeakHomotopyEquivalence` on that map, using the dependency's realization/components/homotopy-group convention. Matches the stated equivalence of spaces. |
| Coherent naturality | The second conjunct quantifies every `K : SSet.{u}` and `H : K ⟶ (ihom C).obj E` and gives `uncurry (H ≫ restriction) = ι ▷ K ≫ uncurry H`. This is the degreewise coherent restriction identity. Matches. |

Source verification: Kerodon 030M states the restriction map is a trivial Kan
fibration when either diagram is Kan extended from the full subcategory;
02YQ defines the over-slice colimit and under-slice limit contractions used
here. No source hypothesis is omitted and no additional finiteness,
nonemptiness, or universe equality is introduced.

Edge cases checked: empty `C`, empty `A` and empty slices remain allowed;
`A = C` is represented by the always-true predicate; zero-dimensional
simplices use the fixed endpoint edge with no horn assumption; both alternatives
retain the same right-pinched mapping model; and arbitrary `u` is allowed.
The zero object and characteristic impose no extra conditions because the
statement is purely simplicial.

Searches were repeated with `msearch.py` (LeanSearch, LeanFinder and Loogle),
`rg` over Mathlib, the upstream `WeilConjectures` tree and this project's
`lean/Sheaf`, and exact-name searches in `dag/lean_names_upstream.json`.
Only ordinary-category Kan-extension/Hom-set results were found; no existing
coherent quasicategory mapping-space statement or any of the twelve helper
names exists. The dependency declarations were opened and used directly.

No mismatch was found, so no Lean or node repair was necessary. The module was
recompiled with `scompile.py` (sandbox and final module, clean with no warnings).
