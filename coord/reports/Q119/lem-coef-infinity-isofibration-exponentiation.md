## Worker report

The item is stated in `lean/Sheaf/CategoryTheory/IsofibrationExponentiation.lean`,
main declaration `SSet.Enhanced.isofibration_exponentiation`. It has one postponed
proof, the theorem of this DAG node. Three supporting definitions belong to the
notions and canonical maps explicitly introduced by the item's statement:
`IsIsofibration`, `exponentialCorner`, and `arrowMappingSpaceMap`. Their data are
fully constructed. No other DAG node is stated; no new node is needed. Only the
item's `lean` field changes.

The retained sandbox contained only dispatcher markers. The current shared node
has no `lean` record: Q37's synchronized delivery supplied a reviewed stage-1
split, not a stage-2 statement. This delivery adds the actual stage-2 attachment
and module; it does not attempt to redeliver that split.

Clause-by-clause correspondence:

* Small simplicial sets: every binder uses `SSet.{u}`, for an explicitly bound
  arbitrary universe `u`. Shapes A and B are arbitrary simplicial sets; neither
  is assumed to be a quasicategory.
* Degreewise injectivity: the first two conjuncts quantify over every
  `n : SimplexCategoryᵒᵖ` and assume `Function.Injective (i.app n)`. This includes
  every degree and allows any injective simplicial map, not just a chosen subset
  inclusion.
* Inner fibration: Mathlib's `SSet.InnerFibration`, defined using the right lifting
  property against precisely inner horn inclusions. No private replacement.
* Isofibration between quasicategories: `IsIsofibration p` includes
  `Quasicategory C ∧ Quasicategory D ∧ InnerFibration p`. Its remaining clause
  takes a vertex c and equivalence edge e with source `D.δ 1 e = p.app _ c`,
  and supplies an equivalence edge e' with `C.δ 1 e' = c` and `p.app _ e' = e`.
  The terminal vertex d is the target `D.δ 0 e`; the terminal vertex of e' is
  unrestricted, and naturality gives its required image d. Thus using edges
  instead of separately naming their target vertices loses no data or clause.
* The first conclusion is `IsIsofibration (exponentialCorner i p)`. Its source is
  `(ihom B).obj C`. Its target is exactly
  `pullback ((ihom A).map p) ((MonoidalClosed.pre i).app D)`, namely
  Fun(A,C) times Fun(B,D) over Fun(A,D). The map is Mathlib's canonical
  `(Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i p).π`,
  whose projections are restriction and postcomposition. Both quasicategory
  conclusions are included in `IsIsofibration`, rather than silently assumed.
* The second conjunct states the independent special case: for any
  `[Quasicategory C]` and any degreewise injection i, the actual restriction
  `(MonoidalClosed.pre i).app C` is an isofibration, again including its two
  quasicategory conclusions. It requires no p or isofibration hypothesis.
* U_C(x,y) is the strict pullback of the simultaneous evaluations at 0 and 1
  along the point with values x,y. This equals the iterated fixed-endpoint
  pullback in the node, with conditions in every simplicial degree. It is
  written directly using Mathlib `pullback`, cartesian `lift`, the dependency's
  `evaluation`, and `SSet.const`; there is no second arrow-space definition.
  Unfolding `SSet.Enhanced.arrowMappingSpace` and `arrowEndpoints` in the published
  `RightPinchComparison` module gives literally the same expression.
* The induced U map is `arrowMappingSpaceMap p x y`. It is constructed by
  `pullback.map` from `(ihom Δ[1]).map p`, the identity of Δ[0], and `p ⊗ₘ p`.
  The commutativities are proved from the actual endpoint constructions inside
  this definition; no arbitrary morphism or unproved choice is supplied.
* The third conjunct requires only `[Quasicategory C]`, `[Quasicategory D]`,
  and `[InnerFibration p]`, with arbitrary vertices x,y. It asserts that both
  endpoint-fixed arrow spaces are `KanComplex` and that their actual induced map
  belongs to `modelCategoryQuillen.J.rlp`. The definition of J includes every
  horn in dimension n+1 for n a natural number: dimensions at least one, all
  indices, both outer horns included, and no dimension-zero nonemptiness axiom.
  This is exactly a Kan fibration; the original p need not lift equivalences.

Dependency declarations read and used:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsEquivalenceEdge`
  (inverse edge and two inverse triangles), `SSet.Enhanced.evaluation` (restriction
  at a vertex), and the existing Mathlib internal-hom/quasicategory primitives
  used throughout that module. The recorded main declaration `coneCategory` and
  its comma-pullback docstring were also read; no cone construction is needed
  for this particular theorem.
* `Mathlib.AlgebraicTopology.Quasicategory.InnerFibration`:
  `SSet.InnerFibration`, `SSet.innerFibrations`, `SSet.innerHornInclusions`.
* `Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations`:
  `SSet.modelCategoryQuillen.J`, its positive-dimensional horn family, and its
  right lifting property. It is available through the public dependency imports.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj`:
  `CategoryTheory.Functor.PullbackObjObj.ofHasPullback` and its canonical `π`.
  The ordinary `pullback.map`, `pullback`, and cartesian `lift` construct U maps.
* Proof-only imports: `Mathlib.CategoryTheory.Limits.HasLimits` for the recorded
  colimit dependency; `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct`
  for `SSet.innerAnodyneExtensions_pushoutObjObjι'`; and
  `Sheaf.CategoryTheory.InvertiblePrismExtension` for
  `SSet.Enhanced.invertible_prism_extension`. Their recorded signatures/docstrings
  and the full node proof were read. The three other proof nodes (relative
  equivalence-prism extension, pointwise equivalences, core Kan fibration) do not
  yet have published records and are referenced in the docstring without an
  import; no statement dependency is missing.

Import/dependency hygiene: the existing U definition lives in the downstream
pinch-comparison module. Its DAG proof path is pinch comparison -> right-fibration
fibers -> this item. Importing it, or adding that node to stmt_deps, would reverse
this order and obstruct future proof imports. The delivered file instead writes
its defining Mathlib pullback expression directly, introduces no duplicate U
alias, and uses no pinch theorem. A separate scratch consumer imports both
modules and typechecks `arrowMappingSpaceMap p x y` with the existing named
`arrowMappingSpace` source and target; this verifies definitional compatibility
while preserving the bottom-up library imports.

Edge cases checked before and after writing:

* A empty is allowed; no binder requires vertices or simplices of A.
* B empty (hence A empty under an injection) is allowed; restriction is the
  terminal-to-terminal special case. A=B and identity i are also included.
* Empty C or D is not excluded. Isofibration lifting quantifies only over actual
  source vertices, and requires no surjectivity onto components.
* The arrow spaces may be empty when x,y have no arrow. Empty Kan complexes and
  maps from them satisfy the positive-horn lifting convention; no nonemptiness
  of a mapping space is imposed.
* Positive horns start at dimension one and include i=0 and i=n. Dimension-one
  horn filling in the proof plan uses degenerate edges, not a missing n>=2 case.
* The mapping-space clause uses only inner lifting of p; equivalence lifting is
  not added accidentally by sharing the first conjunct's hypothesis.
* All universes and variables are explicit; `set_option autoImplicit false` is
  present. No equality between independent site universes is involved.

Searches for an existing statement or construction:

* `msearch.py ... leanfinder "Exponentiation of an isofibration of quasicategories
  by a monomorphism and Kan fibration on fixed endpoint arrow mapping spaces"`:
  eight hits, all about the Quillen-model generating families, cofibrations,
  fibrations, and horn lifting. None states quasicategorical equivalence lifting
  or the combined theorem. The relevant pinned source was read.
* `msearch.py ... loogle '"InnerFibration", "ihom"'`: one hit,
  `SSet.instInnerFibrationMapIhom`. It gives inner lifting after postcomposition
  in an internal hom, without equivalence lifting or the U-space conclusion.
* `msearch.py ... grep 'Isofibration|isofibration|KanFibration|exponentialCorner'
  AlgebraicTopology`: no hits. The generic Mathlib `PullbackObjObj.π` supplies the
  canonical corner construction and is reused.
* `rg` over `WeilConjectures/` for this item's id and for isofibration, mapping-space,
  and corner names: no implementing statement. `rg` over `lean/Sheaf/` found
  downstream proof-plan mentions of this item, not a statement or existing
  isofibration predicate. Broader arrow-space searches found the existing
  `arrowMappingSpace` in `RightPinchComparison`, whose definition was read in
  full and whose pullback expression is used without redefinition.
* Pinned Mathlib files read include Quasicategory/Basic, InnerFibration,
  SimplicialSet/CategoryWithFibrations, Monoidal, the inner PushoutProduct file,
  Monoidal/Closed/Basic and FunctorToTypes, and Pullback/PullbackObjObj.

Source validation: opened [Kerodon 01F1](https://kerodon.net/tag/01F1),
[01F3](https://kerodon.net/tag/01F3), and [01P8](https://kerodon.net/tag/01P8).
They give respectively the corner, restriction, and unpinched morphism-space
fibration results used by the node. The outgoing convention is the node's
explicit convention, with the relative-prism proof already recorded there.
No statement correction or STATEMENT-DISPUTED finding is needed.

Validation: `scompile.py` compiled the final module cleanly as sandbox and library
modules under the prescribed limit. The scratch consumer checks compatibility
with the published named arrow spaces and the exact corner target. The delivery
dry run result is recorded below after running the prescribed wrapper.

`deliver2.py Q119 lem-coef-infinity-isofibration-exponentiation --no-push`
printed: `OK (dry run): commit 9a60dc3f8b compiles and passes the preflight except
for the second reading, which the second reader writes; nothing pushed.`
The required independent second reading is left to the next worker.

## Second reading by Q119

I independently read the shared node, the sandbox node and full Lean module, the
recorded `def-cbc-enhanced-diagrams-cones` statement and declarations, and the
three online source places [01F1](https://kerodon.net/tag/01F1),
[01F3](https://kerodon.net/tag/01F3), and [01P8](https://kerodon.net/tag/01P8).
These are Kerodon sources, not Stacks tags. The hypotheses throughout are
quasicategories and simplicial subsets; there is no finiteness assumption on the
shape. The node explicitly uses the equivalent degreewise-injective formulation
and outgoing equivalence-lifting convention. No statement correction is present
or needed, and no target or unit statement changes.

Object, hypothesis, and conclusion checklist (H3):

1. Small simplicial sets A, B, C, D: the first clause binds
   `{A B C D : SSet.{u}}` at arbitrary explicit universe `u`. The other clauses
   bind their own shapes and categories independently. Verdict: exact; A and B
   need not be quasicategories.
2. Simplicial maps i and p: `(i : A ⟶ B) (p : C ⟶ D)` are actual natural
   transformations. Degreewise injectivity is
   `∀ n : SimplexCategoryᵒᵖ, Function.Injective (i.app n)`, in both clauses
   that require i. Verdict: exact, with no chosen subcomplex or extra instance.
3. Inner fibration: `SSet.InnerFibration` is the recorded Mathlib lifting
   predicate. I read `innerHornInclusions` and `innerFibrations`: only the horns
   with `0 < i < n` occur. Verdict: exact.
4. Isofibration of quasicategories: `IsIsofibration p` contains
   `Quasicategory C ∧ Quasicategory D ∧ InnerFibration p` followed by outgoing
   equivalence lifting. `D.δ 1 e = p.app _ c` fixes the source, and the witness
   has `C.δ 1 e' = c`, `IsEquivalenceEdge C e'`, and `p.app _ e' = e`.
   The unnamed endpoint is `C.δ 0 e'`; naturality forces its image to be the
   endpoint of e. `IsEquivalenceEdge` is the dependency's actual two-triangle
   predicate, whose signature and definition I opened. Verdict: no endpoint
   clause or equivalence witness is lost and no surjectivity is added.
5. Functor objects and corner target: `(ihom B).obj C` is the dependency's
   internal functor simplicial set. `exponentialCorner i p` uses the existing
   `Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i p` and
   its canonical projection. Its target is precisely
   `pullback ((ihom A).map p) ((MonoidalClosed.pre i).app D)`, so the factors
   and maps have the order in the displayed node statement. Verdict: canonical
   restriction/postcomposition corner, not an arbitrary map.
6. First conclusion: `IsIsofibration (exponentialCorner i p)` includes both
   its source and target quasicategory assertions as well as inner and
   equivalence lifting. Verdict: every conclusion clause is present.
7. Independent restriction conclusion: the second conjunct quantifies over
   `[Quasicategory C]`, i and its degreewise injectivity alone, and concludes
   `IsIsofibration ((MonoidalClosed.pre i).app C)`. It does not inherit p or
   an isofibration assumption from the first conjunct. Verdict: exact.
8. Vertices and unpinched U: `(x y : C _⦋0⦌)` are arbitrary vertices. The
   two `KanComplex` expressions are the strict pullback of the paired endpoint
   evaluations along the point with constant values x,y, and p(x),p(y),
   respectively. These fix the entire endpoint simplices. I read `evaluation`
   in EnhancedDiagramsCones and `arrowEndpoints`/`arrowMappingSpace` in
   RightPinchComparison: unfolding the latter gives these exact expressions.
   Verdict: the node's U, not its right-pinched mapping-space model.
9. Induced U map: `arrowMappingSpaceMap p x y` is `pullback.map` with arrow
   component `(ihom Δ[1]).map p`, point component `𝟙 _`, and base component
   `p ⊗ₘ p`. Its two naturality equations are proved directly. Verdict: actual
   postcomposition map with both endpoint conditions, no choice or placeholder.
10. Final hypotheses and conclusions: only `[Quasicategory C]`,
    `[Quasicategory D]`, `(p : C ⟶ D)`, and `[InnerFibration p]` precede x,y.
    Both U objects are asserted `KanComplex`; the actual map is asserted
    `modelCategoryQuillen.J.rlp`. I opened J: its family is all horns
    `Λ[n + 1, i].ι`, with every index `i : Fin (n + 2)`. Verdict: precisely
    all positive-dimensional horns, including both outer horns; no extra
    equivalence-lifting hypothesis on p and no zero-dimensional condition.

Edge cases: empty A and B are permitted, as are identity i and infinite shapes.
Empty C or D is not excluded; equivalence lifting only quantifies over actual
source vertices. U may be empty when no arrow x to y exists: neither KanComplex
nor J imposes dimension-zero nonemptiness. Dimension-one outer horns are in J;
inner horns begin in dimension two. A common arbitrary small-simplicial-set
universe is the dependency's convention, and no new equality of universes or
size bound is imposed. Zero objects, characteristic and scheme hypotheses do
not occur in this statement. Verdict: no excluded edge case found.

Independent H4 searches, using different wording from the worker:

* LeanFinder: "Categorical fibration of quasi categories stable under exponential
  pullback along simplicial monomorphisms", and "Inner fibration between
  infinity categories induces a Kan fibration on spaces of arrows with both
  endpoints fixed". Results give Quillen all-horn fibrations and generic model
  category infrastructure, not this statement.
* Loogle: `"InnerFibration", "ihom"` returns
  `SSet.instInnerFibrationMapIhom`, only the inner-lifting assertion for
  postcomposition. I read the pinned PushoutProduct file, including its stronger
  inner-corner lemma; neither supplies equivalence lifting or the U conclusion.
* LeanSearch: "Isofibrations of quasicategories are stable under pullback
  exponentiation by monomorphisms of simplicial sets" returns generic base-change
  results and Quillen horn lifting, not the required quasicategorical statement.
* Wrapper grep for `CategoricalFibration|Isofibration|exponentialCorner` in
  AlgebraicTopology returns no hits. Direct case-insensitive rg for categorical
  fibration, isofibration, exponential corner, fixed endpoint and unpinched in
  pinned Mathlib, upstream WeilConjectures and shared lean/Sheaf found no existing
  equivalent statement or isofibration definition. Project hits are downstream
  proof-plan references and the named arrow-space definition discussed above.

No H4 duplicate is introduced: the item defines only its explicitly introduced
isofibration notion and canonical maps. Writing the existing U's unfolded
pullback expression avoids importing its downstream comparison theorem and
introduces no competing U definition. There are no new nodes or dependency
modules to audit. I also opened the proof dependency records and the published
InvertiblePrismExtension module; the three available proof modules are imported,
while the relative-prism, pointwise-equivalence and core-map nodes have no Lean
record yet. No statement prerequisite is missing.

H5/H6/H8/H9 checks: all three definitions have real data; the map's local proofs
are the naturality equations of that construction. The only postponed theorem
is this node, with `by sorry`. Every declaration has its source/blueprint
docstring, and the theorem docstring follows all five node proof steps, including
the acyclic direct Kan argument and the final relative lifting argument. No
private definitions, local notation or local instances occur. All lines fit
100 columns; variables and universes are explicitly bound.

Mismatches and repairs: none found. I preserved the Lean and node rather than
rewriting correct work, and appended this independent audit. The sandbox node
differs from the current shared node only in `lean`; `lean.statement` was checked
verbatim equal to the full theorem signature. There is no item repair note.

Validation: the prescribed `scompile.py Q119
lem-coef-infinity-isofibration-exponentiation
lean/Sheaf/CategoryTheory/IsofibrationExponentiation.lean` compiled both sandbox
and library forms cleanly (1.3 s and 1.4 s), with no warnings or errors. The
required dry run and delivery are performed after this section is written.
