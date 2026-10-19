## Worker report

Item: `lem-coef-bisimplicial-reedy-division-calculus`, group Q130, stage 2.
Module: `Sheaf.AlgebraicTopology.BisimplicialReedyDivisionCalculus`.
Main declaration: `SSet.BisimplicialDivision.bisimplicial_reedy_division_calculus`.
The theorem has exactly one postponed proof, `by sorry`; every construction has real data.
The earlier attempt supplied a module but neither its node copy nor its report. I repaired
its functor laws and row/column restriction code, completed its enrichment assertion,
and supplied the missing delivery metadata. No natural-language node field was changed.

Source read: Joyal--Tierney, *Quasi-categories vs Segal spaces*,
https://arxiv.org/html/math/0607820, Section 2, definitions preceding Proposition 2.1,
Propositions 2.1, 2.4 and 2.5, Theorem 2.6 and Proposition 2.10. The tensor and cotensor
formulas are Proposition 2.4; the fibration tests are Proposition 2.5. Functoriality is
supplied by the recorded Reedy dependency (Hovey Theorem 5.2.5).
Archive WANTED: the paper is not present in literature/LIST.md; its online Section 2 was
read directly. The source has additional properness and Cartesian-closed assertions;
the item does not request those and the Lean does not add them.

Hypothesis and clause correspondence (names below are in `SSet.BisimplicialDivision`):

| Node text | Lean rendering |
| --- | --- |
| Simplicial sets in fixed universes | `SSet.{u}` is Mathlib's functor category; `BSet.{u}` is an abbreviation for `(SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) ⥤ Type u`. Universes `u v` are explicitly declared; `autoImplicit` is false. |
| Standard simplices and boundary inclusions, including degree zero | Mathlib `SSet.stdSimplex`, `(SSet.boundary p).ι`, with `p : ℕ` including zero. |
| `(U ⊠ V)_(p,q) = U_p × V_q` | `box`, with componentwise functor maps; `boxMap` is the componentwise map on products. `boxLeft` and `boxRight` fix one variable. |
| `(U \\ X)_q = Hom(U ⊠ Δ[q],X)` | `leftDivision` has exactly this object assignment and precomposition operators; `leftDivisionFunctor` supplies covariance in `X`. |
| `(X / V)_p = Hom(Δ[p] ⊠ V,X)` | `rightDivision`, with precomposition operators; `rightDivisionFunctor` supplies covariance in `X`. |
| Relative left division of `a : U → U'`, `f : X → Y` | `relativeLeft a f` is `pullback.lift` of the postcomposition and restriction maps into precisely the displayed pullback. `leftMap` acts by precomposition in `U` and postcomposition in `X`. |
| Relative right division of `f`, `b : V → V'` | `relativeRight f b`, analogously, uses the specified pullback and `rightMap`. |
| Abbreviations for `f : X → *` | `leftObject a X` and `rightObject X b` use `terminal.from X`. |
| External pushout product | `boxPushout a b` is the actual `pushout.desc` from `(U' ⊠ V) ⨿_(U ⊠ V) (U ⊠ V')` to `U' ⊠ V'`. Its two legs are the indicated product maps. |
| Natural division correspondences | Existential adjunctions `l U : boxLeft U ⊣ leftDivisionFunctor U`, `r V : boxRight V ⊣ rightDivisionFunctor V`, with evaluation on identity simplices fixing their hom equivalences. These evaluation equations determine the usual transpose on every simplex by naturality, rather than allowing arbitrary bijections. |
| Natural bijections of lifting problems | `el` and `er` are equivalences of `Arrow.mk` hom types (commutative squares). The six equations specify both transpose maps and both projections into each pullback. Since the division adjunctions and pushout/pullback maps are canonical, these formulas determine the square bijections and imply naturality in the three arrows. |
| Correspondence of fillers | For each square `s`, equivalences `fl` and `fr` between the `Arrow.LiftStruct` types. Equations on their diagonal `.l` identify them with the same division adjunctions. |
| All three lifting conditions equivalent | The two consecutive `HasLiftingProperty` iff clauses, in exactly the order in the node. This Mathlib predicate means every square has a filler. |
| Kan ground model | The scoped Mathlib Kan fibration structure, as fixed by `SSet.KanQuillen.right_proper_kan_quillen`; weak homotopy equivalences use the dependency's realization-based `SSet.Enhanced.IsWeakHomotopyEquivalence`. |
| Joyal ground model | Witness `J : ModelCategory SSet.{u}` with monomorphism cofibrations, the recorded enlarged-universe quasicategory/homotopy-category test for weak equivalences, and fibrations equal to the right lifting class of trivial cofibrations. This uses precisely the convention of `SSet.exists_joyal_model_structure`, with tests in `max u v`. |
| Vertical Reedy structure exists | Witness `V : ModelCategory BSet.{u}`. Its three classes are fixed by the three corresponding equalities. |
| Vertical cofibrations are monomorphisms | `V.categoryWithCofibrations.cofibrations = monomorphisms BSet.{u}`. |
| Vertical weak equivalences are columnwise weak homotopy equivalences | `verticalWeakEquivalences` tests `(column p).map f` for every first degree `p`. `column p` restricts along `Prod.sectR p SimplexCategoryᵒᵖ`, fixing the FIRST coordinate. |
| Vertical fibrations are tested against every first boundary | `verticalFibrations` is `∀ p : ℕ, Fibration (relativeLeft (boundary p).ι f)`. |
| Vertical simplicial mapping object | `mapping X Y` has q-simplices `tensor X (stdSimplex.obj q.unop) ⟶ Y`; `tensor X L = X ⊗ box (𝟙_ SSet) L`, where the Cartesian tensor is the degreewise product. Operators precompose in the parameter simplex. |
| It is a simplicial model category for this mapping object | Witness `E : SimplicialCategory BSet` with `E.Hom = mapping`, so the enrichment is compatible with the existing ordinary category. `parameterTensor X ⊣ mappingFunctor X` and `tensorFunctor L ⊣ cotensorFunctor L` give ordinary adjunctions; the two simplicial hom isomorphism clauses give their enriched tensor/cotensor forms. The unit isomorphism identifies tensor by `Δ[0]` with the identity. The final clause imposes the Kan fibration SM7 condition for `relativeMapping a f`, and its triviality when either `a` or `f` is weak. |
| Tensor and cotensor are actual constructions | `tensor`, `tensorMap`, `tensorFunctor`, `parameterTensor`; `cotensorFunctor L = ihom (box (𝟙_ SSet) L)`, using Mathlib's presheaf exponential. No object is selected from an existence-only sorry. |
| Vertical fibration iff all monomorphism left divisions are Kan fibrations | First iff in the `∀ X Y f` clause: every `U U' a`, with `Mono a`, tests `Fibration (relativeLeft a f)`. |
| Equivalently, right division by every Kan trivial cofibration lifts all monomorphisms | Second iff: every `L M b` with `Mono b` and `Enhanced.IsWeakHomotopyEquivalence b` tests `(monomorphisms SSet).rlp (relativeRight f b)`. These are exactly Kan trivial cofibrations by the Kan dependency, without fibrancy hypotheses. |
| Horizontal Reedy model structure | Witness `H : ModelCategory BSet`; its classes are fixed by equalities. |
| Horizontal cofibrations are monomorphisms | `H.categoryWithCofibrations.cofibrations = monomorphisms BSet`. |
| Horizontal weak equivalences are rowwise Joyal equivalences | `horizontalWeakEquivalences J` tests every `(row q).map f` in the specified Joyal weak-equivalence class. `row q` restricts along `Prod.sectL SimplexCategoryᵒᵖ q`, fixing the SECOND coordinate. |
| Horizontal fibration boundary test | `horizontalFibrations J` tests `J.categoryWithFibrations.fibrations (relativeRight f (boundary q).ι)` for every `q : ℕ`. |
| All objects cofibrant in both models | `∀ X, V...cofibrations (initial.to X) ∧ H...cofibrations (initial.to X)`. |
| Both factorizations functorial in both structures | `Functorial V ∧ Functorial H`; this predicate is the conjunction of `HasFunctorialFactorization` for `(cofibrations, fibrations ∩ weak equivalences)` and `(cofibrations ∩ weak equivalences, fibrations)`. |

Dependency declarations inspected and used:

- `def-weil-pbc-simplicial-set` is a Mathlib leaf. Read `SSet` in
  `Mathlib.AlgebraicTopology.SimplicialSet.Basic`; `SSet.degenerate` and
  `SSet.nonDegenerate` in `.Degenerate`; `SSet.Subcomplex` in `.Subcomplex`, and
  `SSet.Finite` in `.Finite`. The item needs the functor-category part, not a fresh
  definition of simplicial sets.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`,
  `SSet.KanQuillen.right_proper_kan_quillen`: inspected its full signature and docstring;
  in particular the model witness fixes the scoped Kan fibrations, monomorphism
  cofibrations, and realization-based weak equivalences. No alternate weak-equivalence
  definition or ground model is introduced here.
- `Sheaf.AlgebraicTopology.JoyalModelStructure`, `SSet.exists_joyal_model_structure`:
  inspected its full signature and docstring. The existential Joyal class specification
  in this item uses its actual `hoFunctor`, `MonoidalClosed.pre`, and `uliftFunctor`
  test; it does not replace categorical equivalence by an arbitrary predicate.
- `Sheaf.CategoryTheory.ReedyModelStructure`,
  `HomotopicalAlgebra.Reedy.model_structure`: read its signature, including ground
  completeness/cocompleteness and both functorial-factorization instances, and its
  docstring. Its module is imported for the proof's Reedy construction. The matching
  classes here are the source's explicit boundary-division specialization.
- Proof-only import `Mathlib.AlgebraicTopology.SimplicialSet.Degenerate`: inspected
  `SSet.exists_nonDegenerate`, `SSet.unique_nonDegenerate_dim`,
  `SSet.unique_nonDegenerate_simplex`, and `SSet.unique_nonDegenerate_map`, the recorded
  declarations of `lem-weil-pbc-simplicial-set-nondegenerate-decomposition`.
- Proof-only import `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct`:
  inspected `SSet.anodyneExtensions_pushoutObjObjι`, the exact Mathlib leaf for
  `lem-coef-sset-anodyne-pushout-product`.
- Mathlib's `Monoidal.Closed.FunctorToTypes`, `SimplicialCategory.Basic`, and
  `CategoryTheory.Whiskering` supply the presheaf exponential, ordinary-compatible
  enrichment structure, and the restriction functors, respectively.

Edge cases checked before finalizing:

- `u = 0` is allowed: simplicial index categories are small and divisions have hom
  sets in `Type u`, since the countable indexing universe is zero. No universe equality
  is imposed, and `v` permits all enlarged Joyal test universes as in the dependency.
- `p = 0` and `q = 0` are included. Mathlib's zero boundary is empty; division by it
  is terminal. Thus the relative tests give the ordinary zero-column or zero-row map.
- Empty simplicial sets and the empty bisimplicial set are allowed throughout. Initial
  maps are monomorphisms, so the all-cofibrant clauses include the empty object.
- Arbitrary `X` and `Y` occur in all fibration tests; no Kan, quasicategory, or Reedy
  fibrancy assumption was accidentally imposed on their source or target.
- Identity arrows, terminal-target maps, and empty-domain external products use the
  actual functor-category pushouts and pullbacks, without ad hoc inhabitedness choices.
- Checked both coordinate orders: columns fix first degree; rows fix second degree.
- The final trivial-mapping clause uses a disjunction: either the cofibration or the
  fibration being weak suffices, exactly the two simplicial-model triviality cases.

Searches for existing notions/statements:

- `msearch.py ... leanfinder "Bisimplicial sets external product division adjunction Reedy model structure"`:
  eight hits, including `SSet.instMonoidalClosed`, `SSet.instCartesianMonoidalCategory`,
  `CategoryTheory.SimplicialObject.instSimplicialCategorySSet`, and product-standard-simplex
  lemmas; none is the external division or the two bisimplicial Reedy structures.
- `msearch.py ... loogle "CategoryTheory.HasLiftingProperty"`: twelve hits; the existing
  predicate and `CategoryTheory.Arrow.hasLiftingProperty_iff` provide the square/filler
  interpretation. Used these Mathlib notions instead of defining lifting again.
- `msearch.py ... grep "Bisimplicial|bisimplicial|boxtimes" AlgebraicTopology`: zero hits.
- `rg` on the upstream `WeilConjectures` tree for `Bisimplicial|bisimplicial|leftDivision|relativeLeft|boxtimes`
  and for this node id: no matching implementation of this calculus or annotation.
- `rg` on `lean/Sheaf` finds diagonal-equivalence and bar-comparison modules, and
  `CategoryTheory.SegalSpace.Space`, the same product functor category. `BSet` is only
  a reducible shorthand for that existing category, not a competing structured notion.
  No external-product division construction or the requested theorem was found.
- Full-name checks of `SSet.BisimplicialDivision` and
  `bisimplicial_reedy_division_calculus` in Mathlib, upstream, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no existing declaration.
- The earlier attempt's `searches.jsonl` also records its LeanFinder, Loogle and grep
  searches. I repeated them, correcting the unqualified Loogle identifier to the
  namespace-qualified existing Mathlib name.

The module's seven-step theorem docstring carries the entire DAG proof plan, including
its nondegenerate-latching calculation, matching-object identification, lifting tests,
and tensor pushout-product proof. All helper declarations belong to the notion that the
item itself introduces and are listed in `lean.declarations`; no independent missing
notion or unusable dependency required a new node or dependency module. No statement
correction or STATEMENT-DISPUTED flag was needed.

Validation: the prescribed `scompile.py` compiled the sandbox module and its library-path
form cleanly, with no errors or warnings (3.2 s and 3.4 s reported compiler times).
The delivery dry run is the final validation; no branch is pushed by this worker.

## Second reading by Q130

I independently read the base node, sandbox node and complete Lean module, then the
source itself: Joyal--Tierney, *Quasi-categories vs Segal spaces*,
https://arxiv.org/html/math/0607820, Section 2, definitions before Proposition 2.1,
Propositions 2.1, 2.4, 2.5, Theorem 2.6 and Proposition 2.10. This node has no Stacks
source place. The source's ambient category is arbitrary small simplicial sets, not
only Kan complexes or quasicategories. Its vertical direction fixes the first index;
its horizontal direction fixes the second. There is no characteristic, ring, scheme,
Noetherian, finite-dimensionality or nonemptiness hypothesis. I found no repair note
for this item, no statement_change, and no new or repaired dependency node in this delivery.

My object/hypothesis/conclusion inventory and its Lean match follows. All names in the
right column are in `SSet.BisimplicialDivision` unless qualified otherwise.

| Object, hypothesis or conclusion in the node | Lean rendering and verdict |
| --- | --- |
| Simplicial sets in fixed universes; arbitrary bisimplicial sets | Mathlib `SSet.{u}` and reducible `BSet.{u} := (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) ⥤ Type u`. Same categories, no additional instances in the theorem. Pass. |
| External product with bidegree `U_p × V_q`, with its two functorial variables | `box` now aliases Mathlib `externalProduct`; `boxMap` aliases `externalProductBifunctor.map`. `boxLeft` and `boxRight` specialize its variables. Pass after H4 repair below. |
| Left division in degree q, Hom from U box Delta[q] | `leftDivision U X`, with maps by precomposition in the standard second simplex. `leftDivisionFunctor` gives covariance in X. Pass. |
| Right division in degree p, Hom from Delta[p] box V | `rightDivision X V`, with maps by precomposition in the first simplex; `rightDivisionFunctor` gives covariance in X. Pass. |
| Arbitrary arrows a:U→U', b:V→V', f:X→Y | Explicit binders in the first quantified block; no monomorphism or fibrancy hypothesis there. Pass. |
| Relative left map to `(U' backslash Y) ×_(U backslash Y) (U backslash X)` | `relativeLeft a f` uses `pullback.lift` with postcomposition first and restriction second. I checked both pullback legs and their common target. Pass. |
| Relative right map to `(Y/V') ×_(Y/V) (X/V)` | `relativeRight f b` uses the corresponding actual pullback and its two prescribed maps. Pass. |
| Abbreviations when f has terminal target | `leftObject a X` and `rightObject X b` use the unique `terminal.from X`. No arbitrary terminal-target map. Pass. |
| External pushout-product source and target | `boxPushout a b` is `pushout.desc` from precisely the displayed two external-product maps to `box U' V'`. The order of summands is the node's order. Pass. |
| Division adjunctions, naturally in the input objects | Witnesses `l U` and `r V` are actual `Adjunction`s. The two identity-simplex evaluation equations fix their hom equivalences to the source's currying formulas; naturality in the variable external-product factor follows by evaluating arbitrary simplices via standard-simplex maps. Pass. |
| Natural bijections of squares | `el` and `er` are equivalences of `Arrow.mk` hom types, hence of commutative squares. Their six projection equations fix the transposed upper map and both pullback components of the lower map. The two adjunction evaluation equations determine the transposes, so these square equivalences cannot be arbitrary permutations; naturality in a,b,f follows from the same formulas. Pass. |
| Bijections of fillers belonging to each square | For each square s, `fl` and `fr` identify its `Arrow.LiftStruct` types. The diagonal equations identify the bijections with the same transposes as the square maps. Pass. |
| Three equivalent lifting conditions in the written order | The two final `HasLiftingProperty` iff clauses of the first block give pushout-product vs right division, then right vs left division. Mathlib's predicate means every square admits a diagonal filler. Pass. |
| Kan ground structure, without fibrancy restrictions on its objects | `open scoped SSet.modelCategoryQuillen` fixes the dependency's horn-defined `Fibration`. `Enhanced.IsWeakHomotopyEquivalence` is the recorded realization-based class, not an arbitrary model class. Pass. |
| Joyal ground model | Existential J has monomorphism cofibrations, exactly the dependency's `hoFunctor`/internal-hom testing class after `uliftFunctor.{v,u}`, and the RLP characterization of fibrations. The test objects live in `max u v` as in the recorded Joyal theorem. Pass. |
| Vertical model structure exists | Existential `V : ModelCategory BSet` with its three class equalities. Pass. |
| Vertical cofibrations are all monomorphisms | `V.categoryWithCofibrations.cofibrations = monomorphisms BSet`. Pass. |
| Vertical weak equivalences are columnwise weak homotopy equivalences | `verticalWeakEquivalences` tests every `(column p).map f`; `column p` restricts along `Prod.sectR p`, fixing the FIRST coordinate. Pass. |
| Vertical fibrations are tested against every first boundary | `verticalFibrations` is `∀ p : ℕ, Fibration (relativeLeft (boundary p).ι f)`. No degree is excluded. Pass. |
| The specified vertical simplicial mapping object | `mapping X Y` has q-simplices `tensor X (stdSimplex.obj q.unop) ⟶ Y`, and `tensor X L = X ⊗ box (𝟙_ SSet) L`; Cartesian tensor is degreewise product. Operators precompose on Delta[q]. Pass. |
| Simplicial structure, tensors, cotensors and simplicial-model axiom | `∃ E : SimplicialCategory BSet, E.Hom = mapping` gives ordinary-compatible enrichment. `parameterTensor X ⊣ mappingFunctor X` and `tensorFunctor L ⊣ cotensorFunctor L` are adjunctions, with both enriched-hom isomorphism clauses and the Delta[0] tensor-unit isomorphism. Cotensors use the existing presheaf `ihom`. `relativeMapping` is the canonical map to the corresponding pullback; the last clause is SM7: Kan fibration for cofibration a/fibration f, trivial whenever a OR f is weak. Pass. |
| Vertical fibration iff all mono left-division tests | First iff quantified over every `U U' a`, with precisely `Mono a`, and over every X,Y,f without fibrancy assumptions. Pass. |
| Equivalent right-division test for every Kan trivial cofibration | Second iff tests each `b` with `Mono b` and `Enhanced.IsWeakHomotopyEquivalence b`; its conclusion is `(monomorphisms SSet).rlp (relativeRight f b)`. The Kan dependency identifies these b with exactly its trivial cofibrations. Pass. |
| Horizontal model structure with monomorphism cofibrations | Existential H and its cofibration-class equality. Pass. |
| Horizontal weak equivalences are rowwise Joyal equivalences | `horizontalWeakEquivalences J` tests every `(row q).map f` using the Joyal weak class. `row q` restricts along `Prod.sectL`, fixing the SECOND coordinate. Pass. |
| Horizontal boundary-division fibration criterion | `horizontalFibrations J` tests `relativeRight f (boundary q).ι` in J's fibration class for all natural q. Pass. |
| Both models have every object cofibrant | The `∀ X` clause asserts the initial map is in each class. It is not an assumption on X. Pass. |
| Both model factorizations are functorial | `Functorial V ∧ Functorial H`, where `Functorial` uses Mathlib `HasFunctorialFactorization` for each of the two exact weak factorization systems. Pass. |

Dependency audit: I opened the node records and actual source signatures of
`SSet.KanQuillen.right_proper_kan_quillen`, `SSet.exists_joyal_model_structure` and
`HomotopicalAlgebra.Reedy.model_structure`. The first fixes the scoped Kan fibration
and monomorphism structures and realization-based weak equivalences explicitly. The
second supplies precisely the enlarged-universe test used here, plus functorial
factorizations. The Reedy theorem takes a small indexing category, complete and
cocomplete ground category, and both ground functorial factorization instances; with
Delta-op and simplicial sets those are available from the two ground results and
existing set-valued functor-category limits. Thus there is no hidden ground hypothesis
in this theorem. I also opened Mathlib `SSet`, `boundary`/`boundary_zero`, the four
nondegenerate-decomposition statements, and `anodyneExtensions_pushoutObjObjι` together
with the definition `anodyneExtensions := (fibrations _).llp`. The two proof-only
imports match the two remaining proof dependencies. No private replacement of a
recorded dependency is used, and no new definition node/dependency module is needed.

Edge cases: p=q=0 are included in the natural-number boundary quantifiers; Mathlib
`boundary_zero` is empty, so the matching target there is terminal and these tests
recover the zero-degree component. Empty U or V and empty X or Y are allowed; maps
out of an empty external product give the appropriate terminal division. Identity
a,b,f and terminal-target f use their actual universal maps. All objects includes
the initial bisimplicial set. No nonempty index set, chosen basepoint or fibrancy is
assumed. At u=0 the simplex indexing category is small, so its natural-transformation
types still lie in `Type u`; there is no upward restriction on u. The independent v
only enlarges the Joyal test universe through `max u v`, exactly as in the dependency.
Schemes, zero objects and characteristic impose no cases here because these categories
are unpointed set-valued presheaf categories.

Independent searches, using different wording from the worker:

- `msearch.py ... leanfinder "External products of two simplicial presheaves and their right adjoints with relative lifting squares"`: eight hits. This located the existing external-product API and general `ParametrizedAdjunction.hasLiftingProperty_iff`; neither states this two-model theorem. I opened `Monoidal/ExternalProduct/Basic.lean` and repaired the duplication it exposed.
- `msearch.py ... loogle "CategoryTheory.SimplicialCategory"`: nine hits. Opened `SimplicialCategory.Basic` and `SimplicialCategory.SimplicialObject`; the latter enriches a nested simplicial-object category generically, not this product-index category with its specified vertical Hom and Reedy model classes. No exact existing theorem.
- `msearch.py ... grep "externalProduct|leftDivision|rightDivision" CategoryTheory/Monoidal`: 23 hits, including `externalProductBifunctor`, `externalProduct`, their swap and diagonal isomorphisms. Used the actual Mathlib external-product notion.
- Direct `rg` of Mathlib, upstream `WeilConjectures`, and the project's `lean/Sheaf` for `externalProduct`, `division`, `bisimplicial`, and full declaration names: the source has external products of derived sheaves, unrelated algebraic division, and no bisimplicial division/model result. Project hits include diagonal equivalence and bar-comparison statements; those do not state this node. Exact namespace/main-name searches, including `dag/lean_names_upstream.json`, found no collision.

Mismatch repaired (H4): the worker had manually reconstructed the already existing
external-product functor and its map. I replaced `box` by a reducible abbreviation
for Mathlib `externalProduct`, and `boxMap` by a reducible abbreviation for
`externalProductBifunctor.map (a,b)`, with its direct public import. I removed one
now-redundant trailing `rfl` in `mapping.map_comp`, since simplification now closes
that goal. No natural-language node field or theorem signature changed. The helpers
`boxLeft` and `boxRight` merely specialize this API; the remaining helpers construct
exactly the division, mapping and model-class notions introduced by this node.

H5/H6/H8/H9 checks: all object data are explicit constructions or existing Mathlib
constructions. There is exactly one postponed theorem, with `by sorry`; no theorem
was proved. Structural functor/universal-map compatibility proofs have real terms.
Every helper has source and blueprint docstrings, and the theorem docstring follows
all seven DAG proof steps, naming the nondegenerate, Reedy, Kan, Joyal and anodyne
inputs. No file-local notation, private definition, local instance, unbound variable
or universe, extra axiom, or line over 100 characters remains. The node's
`lean.statement` was mechanically checked verbatim against the theorem signature.

Validation: `scompile.py Q130 lem-coef-bisimplicial-reedy-division-calculus
lean/Sheaf/AlgebraicTopology/BisimplicialReedyDivisionCalculus.lean` passed both sandbox
and library-path compilation cleanly (2.6 s and 2.8 s), with no errors or warnings.

Delivery dry run: `deliver2.py Q130 lem-coef-bisimplicial-reedy-division-calculus
--no-push` returned `OK`: preflight and compilation passed at dry-run commit
`9073360df6`; nothing was pushed by that check.
