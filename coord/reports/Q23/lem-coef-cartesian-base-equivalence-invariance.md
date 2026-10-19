## Worker report

The module `Sheaf.AlgebraicTopology.CartesianBaseEquivalenceInvariance` states
`SSet.Marked.Over.cartesian_base_equivalence_invariance`, with one postponed
proof. Its two auxiliary declarations belong to this node:
`CartesianBaseModelHypotheses` packages exactly its explicitly assumed model
structures, and `extensionBaseChangeMap` constructs its canonical comparison
by the pullback universal property. Neither auxiliary has postponed data or
postponed proofs. The theorem docstring carries all 17 DAG proof steps and
their cited inputs.

### Source and hypothesis-by-hypothesis correspondence

I fetched the source's HTT PDF into the sandbox scratchpad and read printed
pp. 204–207, in particular Proposition the project server, Corollary the project server,
Proposition the project server and its comparison diagram, and Proposition the project server.
Corollary the project server supplies the extension; the sharp marked inverse in the
node's hypotheses makes its comparison universally categorical. Proposition
the project server states the projection assertion over arbitrary simplicial sets.

| Node hypothesis or convention | Lean rendering |
| --- | --- |
| Small simplicial sets and maps, with no base quasicategory hypothesis | `SSet.{u}` and its category morphisms; no `Quasicategory S`, `Quasicategory T` or total-space instance |
| Arbitrary-base cartesian fibration with prescribed-target lifts | Existing `relativeFibration false q`, which uses `InnerFibration` and `Enhanced.IsCartesianEdge` with final horns |
| Natural marking is exactly the cartesian edges | Existing `IsNaturallyFibrant false X`, and `cartesianNatural` / `cartesianNaturalOver` from the relative calculus |
| Marked objects and marked maps over the sharp base | Existing `SSet.Marked.Over B = CategoryTheory.Over (sharp B)` |
| The class W_B detected by Map-sharp into every natural cartesian object | Existing `weak false`; its definition quantifies over all `Over B` objects satisfying `IsNaturallyFibrant false` and tests `Enhanced.IsWeakHomotopyEquivalence (mapSharpPre f Z)` |
| Given structures in each universe | `_models : ∀ B : SSet.{u}, CartesianBaseModelHypotheses B` and `_largerModels : ∀ B : SSet.{max u v}, CartesianBaseModelHypotheses B`; `u v` are explicit, arbitrary universes |
| Complete and cocomplete model categories | `complete`, `cocomplete`, `model` fields of the hypothesis record |
| Left proper | `left_proper`, stability of `weak false` under cobase change against `cof` |
| Combinatorial | `locally_presentable` and the small generating sets in `generating_cofibrations`, `generating_trivial_cofibrations` |
| Cofibrations are underlying simplicial monomorphisms | `cofibrations` identifies them with the existing `cof`, defined by degreewise injectivity of the underlying map |
| Weak equivalences are W_B | `weak_equivalences` identifies the model's weak-equivalence field with `weak false` |
| Fibrant objects are exactly naturally marked cartesian fibrations | `fibrant_objects`, testing the canonical terminal arrow `toBase X` against `IsNaturallyFibrant false X` |
| Fibrations and factorizations in the input universe | `fibrations`, `cof_triv_fib_factorization`, `triv_cof_fib_factorization`; each uses the original `Over B` and its morphism universe, without enlarging factorization objects |
| Simplicial enrichment is Map-sharp | `enrichment`, `mapping_iso`, `ordinary_enrichment`, `enrichment_composition`; the latter formulas fix the usual underlying maps and composition, so no arbitrary enrichment can stand in for it |
| Tensor U × K-sharp and cotensor | Existing `tensor`; `tensor_adjunction`, `tensor_formula`, `cotensor`, `tensor_cotensor` fix the ordinary simplicial adjunctions with that tensor |
| Simplicial model axiom over Kan simplicial sets | `simplicial_pushout_product` uses the existing canonical `IsPushoutProduct`, `Mono j`, and realization-based `Enhanced.IsWeakHomotopyEquivalence j` |
| Fibrant weak equivalence iff all vertex fibers are equivalent | `fiberwise_criterion`, with the existing `fiberMap` and `Enhanced.IsFunctorEquivalence` on the quasicategory fibers |
| Equivalently, a marked inverse up to sharp paths | `marked_inverse_criterion`, with an actual over-base inverse and `HasSharpPath` for both composites |
| Composition and pullback form a Quillen adjunction for every c | `base_change_adjunction : push a ⊣ pull a`, `base_change_cof`, `base_change_triv_cof`; these use the existing canonical functors for every base map, with exactly the left Quillen preservation conditions |
| Categorical equivalence, tested by hFun against all quasicategories | Verbatim Joyal expression `∀ C : SSet.{max u v}, Quasicategory C → ((hoFunctor.map ((MonoidalClosed.pre (uliftFunctor.{v, u}.map f)).app C)).toFunctor).IsEquivalence` |

The hypothesis record deliberately does not use the entire
`RelativeCartesianModelStatement`: that record also contains the downstream
`pullback_homotopy_pullback` conclusion. It only reuses its already recorded
underlying constructions and packages the hypotheses actually written in
this node. In particular no base-equivalence theorem or arbitrary chosen
comparison is smuggled into the hypotheses. The record is not another
model-structure construction or another definition of cartesian fibrations.

### Conclusion clause-by-clause correspondence

1. The first conjunct universally quantifies `S T Z q a`, assumes
   `relativeFibration false q` and exactly the Joyal categorical-equivalence
   tests on `a`, then gives the same tests for `pullback.snd a q`.
   The pullback is ordered `T ×_S Z`, so its second projection is exactly the
   node's map to `Z`.
2. The second conjunct quantifies `S S' Z i q`, assumes exactly the tests on
   `i` and cartesianness of `q`, then gives an actual small `Z'` and map
   `q' : Z' ⟶ S'` satisfying `relativeFibration false q'`.
3. Its witnesses `e : Z ⟶ pullback i q'` and
   `he : e ≫ pullback.fst i q' = q` are precisely the comparison over `S`.
   `Enhanced.preservesCartesianEdges q (pullback.fst i q') e he` states its
   preservation of cartesian edges, using the recorded predicate directly.
4. The same witnesses precede every quantifier over `T` and `b : T ⟶ S`.
   Thus one fixed extension works after every base change. The exact map
   `extensionBaseChangeMap q i q' e he b` has source `pullback b q`, target
   `pullback (b ≫ i) q'`, first coordinate the projection to `T`, and second
   coordinate the projection to `Z` followed by `e` and the projection to
   `Z'`. The proof of its well-definedness uses only pullback commutation,
   associativity, and `he`. This is the canonical universal comparison,
   with exactly the specified composite base map on the right.
5. The conclusion applies the same Joyal tests to this actual comparison.
   There is no fibrancy, injectivity, nonemptiness or finiteness hypothesis
   on any `T`, `b`, `a`, or `i`.

### Dependency declarations used

- `Sheaf.CategoryTheory.InfinityFibrations`:
  `SSet.Enhanced.IsCartesianEdge`, `SSet.Enhanced.preservesCartesianEdges`.
  The recorded `cartesianFibration` requires quasicategories, so the item
  correctly uses its already-landed arbitrary-base extension below.
- `Sheaf.AlgebraicTopology.RelativeMarkedAnodyneCalculus`:
  `SSet.Marked.cartesianNatural`, `cartesianNaturalOver`,
  `SSet.Marked.Over.relative_marked_anodyne_calculus`.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`:
  `SSet.Marked`, `sharp`, marked maps, products and sharp simplices;
  `SSet.Marked.marked_point_cartesian_model` is the point-model proof input.
- `Sheaf.AlgebraicTopology.JoyalModelStructure`:
  `SSet.exists_joyal_model_structure`, whose exact categorical-equivalence
  testing expression is retained rather than using the different
  core-testing spelling `CoherentNerve.IsCategoricalEquivalence`.
- The relative calculus publicly exports
  `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`. Its definitions
  `SSet.Marked.Over`, `relativeFibration`, `IsNaturallyFibrant`, `cof`,
  `weak`, `mapSharp`, `tensor`, `IsPushoutProduct`, `fiberMap`,
  `HasSharpPath`, `push`, `pull`, `toBase` are all reused directly.
  Its downstream theorem `marked_relative_cartesian_model` is not an
  assumption or a proof input.
- Mathlib supplies the actual simplicial sets, `hoFunctor`, `ihom` and
  precomposition, `uliftFunctor`, ordinary/model-category structures,
  `HasFunctorialFactorization`, and `Limits.pullback` with its canonical
  projections and lift.

All recorded proof-dependency modules available at writing are imported
without `public` unless already public statement dependencies. They include
CoherentNerveComparison, MarkedAnodyneLiftingCalculus,
ModelLocalizationDetectsWeakEquivalences, ModelInfinityDerivedAdjunction,
SimplexSpineInnerAnodyne, ModelCofibrantColimitComparison,
SimplicialModelNerveLocalization, RigidificationEquivalenceDetection,
EnhancedFunctorConeCalculus, KanQuillenRightProper,
InfinityCocartesianMappingCriterion, JoyalQuasicategoryCharacterizations,
and IsofibrationPullbackLimit. The Mathlib matched inner-anodyne pushout
product module is imported too. Six proof-only nodes have no binding yet
and require no new statement to type this item: marked-cone-generator-
calculations, simplicial-projective-model-calculus,
small-object-cell-factorization, marked-cone-external-product,
cartesian-cone-fiber-comparison, mapping-simplex-final-edge (each with
prefix `lem-coef-`). Their full roles remain in the proof docstring.
No statement dependency was repaired, copied, or replaced.

### Edge cases checked before writing

- Empty `S` or total space: no nonempty instance is imposed; lifts are
  vacuous when appropriate and empty pullbacks remain included. A
  categorical equivalence from a nonempty simplicial set to the empty one
  cannot occur, as the empty quasicategory test detects it.
- Identity `a` or `i`: the projection is the canonical isomorphism up to
  the strict pullback choice. In the extension case one may take `Z'=Z`
  and the canonical diagonal into the identity pullback. The formula for
  the comparison uses the actual pullback projections, not a chosen weak
  equivalence, so these cases are retained.
- Noninjective categorical equivalences: neither `a` nor `i` is assumed
  monic; no cofibration restriction was introduced.
- Nonquasicategorical bases and test sources: only the testing targets
  `C` carry `Quasicategory`. The arbitrary-base horn predicate has no
  hidden instances, unlike the older quasicategory-only spelling.
- Point bases: prescribed-target cartesian lifts reduce to the existing
  naturally marked quasicategory situation, consistently with the point
  model and the fiber criterion.
- Arbitrarily large test quasicategories: `max u v` retains every
  enlargement; all actual extension and base-change objects stay in `u`.

### Searches for an existing declaration

- `msearch.py ... leansearch "Pullback along a Cartesian fibration
  preserves categorical equivalences of simplicial sets"`: eight hits
  about ordinary fibered categories, base-change stability of fibrations,
  and isomorphisms of pullback squares; none states this simplicial result.

- `msearch.py ... leanfinder "Pullback of a cartesian fibration along a
  categorical equivalence of simplicial sets is a categorical equivalence"`:
  eight hits, concerning ordinary fibered categories, finite pullbacks,
  trivial fibrations and nerves; none states this simplicial result.
- `msearch.py ... loogle "SSet, CategoryTheory.Limits.pullback"`:
  one hit, `SSet.instFinitePullback`; no match.
- `msearch.py ... grep
  "cartesian.*equivalence|Cartesian.*Equivalence|base.*equivalence"
  AlgebraicTopology`: one unrelated fundamental-groupoid prose hit.
- Direct `rg` in Mathlib, upstream `WeilConjectures`, the side project's
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision for
  `CartesianBaseModelHypotheses`, `extensionBaseChangeMap`, or
  `cartesian_base_equivalence_invariance`.
- Direct conceptual `rg` in upstream `WeilConjectures` and side
  `lean/Sheaf`: only downstream references and unrelated geometry,
  and `cocartesian_categorical_base_change`, which is the cocartesian
  quasicategory-base corollary and supplies neither conclusion here.
- `grep -rn` of the item id in upstream `WeilConjectures`: no hits.

No new independent notion or new DAG node was required. No statement
correction and no STATEMENT-DISPUTED flag is needed.

### Validation

The initial compile diagnosed an explicit-versus-implicit argument error in
`pullback.condition`; this was corrected to its actual named implicit
parameters. A subsequent compile passed elaboration and found one newly
long line; the line was wrapped. Final `scompile.py` completed both its sandbox and library-module checks
with exit 0 and no warnings (1.7 s and 2.1 s). `deliver2.py Q23 lem-coef-cartesian-base-equivalence-invariance --no-push`
printed `OK (dry run)` for commit `a9584e3b8a`: compilation and preflight
passed except for the intentionally pending independent second-reading
section. Nothing was pushed, and no second-reading section was fabricated.


## Second reading by Q23

I independently read the sandbox node and module, the four statement-dependency
nodes and their recorded declarations, and HTT printed pp. 204–207 in
`scratchpad/HTT.txt` (Corollary the project server, Proposition the project server and its complete
proof, with Proposition the project server and Proposition the project server). This source is HTT,
not a Stacks tag. Section 3.3.1 explicitly distinguishes arbitrary simplicial
bases from the special case of infinity-category bases. Neither displayed
source result assumes that its bases or total space are quasicategories.
Corollary the project server gives an equivalence of cartesian fibrations; retaining an
actual marked inverse and its sharp homotopies supplies the universal
base-change assertion in the node. The node explicitly makes the previously
constructed model structures and Quillen adjunctions hypotheses. I found no
source-based correction needed; the sandbox changes only the `lean` field.
There is no repair note, statement_change, new node or dependency module.

The following is my object/hypothesis/conclusion checklist. Every row passes.
Unqualified names below are in `SSet.Marked.Over` unless indicated.

| Node object or clause | Actual Lean and verdict |
| --- | --- |
| Arbitrary small simplicial bases and total spaces | `SSet.{u}` for `S T Z S' Z' B`; the only `Quasicategory` premises in the delivered theorem concern testing targets `C`. Pass: no hidden base or total-space fibrancy instance. |
| Cartesian fibrations over arbitrary bases | `relativeFibration false q` and `relativeFibration false q'`. I opened its definition: `InnerFibration q` and a lift of each base edge with prescribed target `δ 0`, distinguished by final outer horns. Pass. |
| Natural marking consists of cartesian edges | `IsNaturallyFibrant false X` asserts `relativeFibration false X.hom.val` and exact equivalence of the marking with `IsDistinguishedEdge false`. The latter uses `Enhanced.IsCartesianEdge`, whose definition fills the final horns with specified last edge. Pass. |
| Category M_B of marked objects and marked maps over B | Existing `Marked.Over B` is `CategoryTheory.Over (sharp B)`; `Marked.Hom` preserves markings and `sharp` marks all edges. Pass: this is exactly the slice in the node. |
| Sharp mapping simplices over B | Existing `mapSharp X Y` is the simplicial Yoneda object of `sharpSimplex ⋙ productLeft X`; its n-simplices are marked maps `X × (Δ[n])^sharp → Y` over B. Pass. |
| W_B tested against all natural cartesian objects | `weak false f` quantifies `Z : Over B`, assumes `IsNaturallyFibrant false Z`, and tests `Enhanced.IsWeakHomotopyEquivalence (mapSharpPre f Z)`. I opened the latter predicate: it checks components and positive based homotopy groups after realization. Pass. |
| Given model family in each input and enlarged universe | `_models : ∀ B : SSet.{u}, CartesianBaseModelHypotheses B` and `_largerModels : ∀ B : SSet.{max u v}, CartesianBaseModelHypotheses B`, with arbitrary declared `u v`. Pass: the enlargement is not an equality constraint. |
| Complete, cocomplete model category | `complete`, `cocomplete : Has(Limits/Colimits)OfSize.{u,u} (Over S)` and `model : ModelCategory (Over S)`. Pass: these are the structures in the input universe. |
| Left proper | `left_proper` is stability of `weak false` under cobase change against `cof`. Pass. |
| Combinatorial | `locally_presentable` and small generating properties `I`, `J` with right lifting classes equal to trivial fibrations and fibrations in `generating_cofibrations` and `generating_trivial_cofibrations`. Pass. |
| Cofibrations exactly underlying monomorphisms | `cofibrations` identifies the model class with existing `cof`, which uses `Marked.cof f.left`, i.e. degreewise injectivity of the underlying simplicial map. Pass. |
| Weak equivalences exactly W_B | `weak_equivalences` identifies the actual model's class with `weak false`. Pass. |
| Fibrations and factorizations | `fibrations` is the model lifting characterization; both `HasFunctorialFactorization` fields are on the same `Over S`. Pass: factorization objects are not enlarged and no extra mathematical hypothesis is imposed. |
| Fibrant objects exactly naturally marked cartesian fibrations | `fibrant_objects` tests the terminal arrow `toBase X` and concludes exactly `IsNaturallyFibrant false X`. I opened `toBase`: its target is the identity object over `sharp S`. Pass. |
| Simplicial enrichment is the specified sharp enrichment | `enrichment`, `mapping_iso`, `ordinary_enrichment`, `enrichment_composition`. I checked the formulas: constant simplices of ordinary maps and parameterwise composition are fixed, not just arbitrary isomorphic hom objects. Pass. |
| Tensor X × K^sharp and cotensor | Existing `tensor K` is `productLeft X` evaluated on `sharp K`. `tensor_adjunction` and `tensor_formula` specify the usual adjunction with `mapSharp`; `cotensor` and `tensor_cotensor` provide its right adjoint. Pass. |
| Simplicial model compatibility with Kan model structure | `simplicial_pushout_product` uses `cof i`, `Mono j`, the actual universal pushout-product square `IsPushoutProduct i j p`, and triviality if `weak false i` or `Enhanced.IsWeakHomotopyEquivalence j`. Pass. |
| Fibrant weak equivalences iff equivalences on all vertex fibers | `fiberwise_criterion` quantifies every `s : S _⦋0⦌` and uses the actual pulled-back `fiberMap f s`. `Enhanced.IsFunctorEquivalence` is the coherent quasi-inverse predicate; I opened it and its natural-equivalence definition. Pass. |
| Equivalently, marked inverse up to sharp paths | `marked_inverse_criterion` requires `r : Y ⟶ X` over the same base and `HasSharpPath (f ≫ r) (𝟙 X)` and `HasSharpPath (r ≫ f) (𝟙 Y)`. I checked that `HasSharpPath` is an actual edge in the relative sharp mapping object with these endpoints. Pass. |
| Composition/pullback are Quillen for every base map | `base_change_adjunction` uses existing `push a ⊣ pull a`; `base_change_cof` and `base_change_triv_cof` express preservation by its left adjoint. The canonical functors' definitions are composition to the sharp base and degreewise marked pullback. Pass: all base maps are included. |
| Categorical equivalence convention | Every occurrence is the same `hoFunctor.map ((MonoidalClosed.pre (uliftFunctor.{v,u}.map f)).app C)` ordinary categorical-equivalence test, universally quantified over `C : SSet.{max u v}` with `Quasicategory C`. I opened `exists_joyal_model_structure` and compared its weak-equivalence clause. Pass: no substitution of the distinct core-testing spelling. |
| Conclusion (1): pullback projection | First conjunct quantifies `S T Z q a`, assumes exactly cartesianness of `q` and categorical equivalence of `a`, and concludes categorical equivalence of `pullback.snd a q`. Its domain is `T ×_S Z` and codomain is `Z`. Pass. |
| Conclusion (2): extension exists | Second conjunct quantifies `S S' Z i q`, assumes exactly categorical equivalence of `i` and cartesianness of `q`, then produces `Z'`, `q'` and `relativeFibration false q'`. Pass: an actual small extension, not merely an equivalence class. |
| Fixed comparison over S preserving cartesian edges | Witnesses `e : Z ⟶ pullback i q'` and `he : e ≫ pullback.fst i q' = q` precede `Enhanced.preservesCartesianEdges q (pullback.fst i q') e he`. I opened the preservation predicate: every cartesian edge is carried to one for the displayed projection. Pass. |
| Same comparison works after every base change | The witnesses precede `∀ (T : SSet.{u}) (b : T ⟶ S) (C : SSet.{max u v})`. Pass: neither the extension nor its comparison depends on T, b or C. |
| Induced map uses composite b followed by i | `extensionBaseChangeMap q i q' e he b` has domain `pullback b q` and target `pullback (b ≫ i) q'`. Its `pullback.lift` coordinates are `pullback.fst b q` and `pullback.snd b q ≫ e ≫ pullback.snd i q'`. The condition follows from `he` and the two pullback conditions. Pass: this is the canonical map, not an arbitrary categorical equivalence between these objects. |
| Universal categorical-equivalence conclusion, with no fibrancy on T | The final Joyal test applies to that exact constructed comparison for every T and b. Pass: no extra `Quasicategory T`, `Mono b`, finiteness or nonemptiness assumption. |

Dependency inspection and reuse: I read the recorded signatures in
`InfinityFibrations`, `JoyalModelStructure`, `MarkedPointCartesianModel`,
and `RelativeMarkedAnodyneCalculus`, and opened the relative constructions
exported from `MarkedRelativeCartesianModel`. The older
`Enhanced.cartesianFibration` requires quasicategories; the delivered theorem
correctly uses the already-recorded arbitrary-base `relativeFibration false`
through the relative-calculus dependency instead. No second horn, natural
marking, mapping-space, weak-equivalence or model construction is introduced.
`CartesianBaseModelHypotheses` only packages this node's explicitly given
structures; unlike the existing full `RelativeCartesianModelStatement`, it
does not assume the downstream homotopy-pullback theorem. The helper
`extensionBaseChangeMap` specializes the ordinary pullback universal property
to the fixed extension data; its data and well-definedness are explicit.
There are no dependency repairs or new independent definition nodes to audit.

Edge cases: empty bases and empty total spaces are allowed without a vertex
choice; the empty-base fiber criterion quantifies over no vertices, as it
should. Identity and nonmonic categorical equivalences are included. The
identity extension and its base changes are covered by the same coordinate
formula. Zero simplices and degenerate edges are covered by the existing
markings and all-degree mapping formulas; horn tests begin at dimension two
as the definition requires. No index set, ring, characteristic, scheme or
integer n occurs in this statement, so those proposed edge cases add no
restriction. Both universes are explicitly bound; all construction objects
remain in u, while the Joyal targets range in arbitrary `max u v`. There is
no additional universe equality or smallness assumption on a base.

Independent searches used different wording from the first worker:

- `msearch.py ... leanfinder "Categorical equivalences stable under base
  change along cartesian fibrations and extension of cartesian fibrations
  along equivalences"`: eight hits about ordinary fibered categories and
  Grothendieck constructions, none about this simplicial statement.
- An initial Loogle query containing unqualified `pullback.snd` was rejected
  as an unknown identifier; I reran with
  `CategoryTheory.Limits.pullback.snd`. The corrected query returned twelve
  ordinary pullback-construction/projection lemmas, with no cartesian
  categorical-equivalence or extension assertion.
- `msearch.py ... grep "cartesian.*categorical|categorical.*cartesian|Cartesian.*equivalence"
  AlgebraicTopology`: zero hits.
- Direct conceptual `rg` in upstream `WeilConjectures`, Mathlib
  `AlgebraicTopology` and `CategoryTheory`, and this project's `lean/Sheaf`
  found `cocartesian_categorical_base_change` and
  `CartesianSimplexInverseExtension`. I opened both. The former assumes a
  quasicategory base and a cocartesian fibration and gives no extension;
  the latter extends a prescribed inverse/homotopy across a simplex, not a
  cartesian fibration across a categorical equivalence. Neither replaces
  this item. Other hits concern ordinary scheme base change.
- Exact-name `rg` for all three delivered declarations in Mathlib, upstream,
  `lean/Sheaf` and `dag/lean_names_upstream.json` found no collisions.

H5–H9 checks: there is one postponed theorem, whose entire proof is `sorry`;
there is no postponed definition data. The hypothesis structure is data,
not a new existence assertion. The comparison definition proves only its
structural pullback compatibility. All three declaration docstrings and the
module docstring name HTT and this blueprint id. The theorem docstring has
all seventeen numbered proof steps and their dependencies. All lines are at
most 100 characters, all variables and universes are bound, and the node's
`lean.statement` is byte-for-byte the theorem signature before `:=`.
Statement dependencies are public imports and available proof dependencies
are imported. No theorem has been proved and no extra conclusion is assumed.

Mismatches found and changes: none in the Lean, node or source correspondence.
I left the correct statement, constructions and node record untouched and
appended this independent reading to the report. No statement correction or
citer audit is required.

Validation: I ran `scompile.py Q23 lem-coef-cartesian-base-equivalence-invariance`
on the delivered module. The sandbox check (1.7 s) and library-module check
(2.3 s) both passed with exit 0 and no errors or warnings. There are no sibling
modules. The delivery dry run and push are recorded below after execution.

Delivery dry run: `deliver2.py Q23 lem-coef-cartesian-base-equivalence-invariance --no-push` printed `OK (dry run)` for commit `0f49f8c30e`: server preflight and both compilation checks passed. The wrapper refreshed its own temporary delivery worktree; no direct Git operation was used.
