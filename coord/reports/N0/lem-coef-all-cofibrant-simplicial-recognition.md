## Worker report

The item module `Sheaf.AlgebraicTopology.AllCofibrantSimplicialRecognition` states
`CategoryTheory.all_cofibrant_simplicial_recognition`. The only theorem proof is
`sorry`. The node statement is unchanged. Its full six-step natural-language
proof is in the theorem's docstring. No new DAG nodes are needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The model category is `{M : Type u} [Category.{v} M] [ModelCategory M]`.
  Mathlib's `ModelCategory` gives the three classes, retract stability,
  two-out-of-three, and both weak factorization systems. Following the explicitly
  cited boundary-collapse node's conventions, full completeness/cocompleteness
  and functoriality are also explicit:
  `[HasLimitsOfSize.{max v w, max v w} M]`, the corresponding colimits instance,
  and the two `HasFunctorialFactorization` instances for cofibrations/trivial
  fibrations and trivial cofibrations/fibrations. These are inherited model
  conventions, not additional mathematical assumptions.
- The enrichment is `[SimplicialCategory M]`, which identifies ordinary arrows
  with vertices and supplies enriched associative composition and units. The
  recorded dependency `T : SimplicialTensorCotensor M` supplies the same chosen
  tensor/cotensor objects and their enriched universal-element isomorphisms.
  No substitute tensor or enrichment is introduced.
- Every object is cofibrant is `hall : ∀ X : M, IsCofibrant X`.
- Stability under small filtered colimits in the arrow category is the existing
  Mathlib class `[(weakEquivalences M).IsStableUnderFilteredColimits.{w, w}]`.
  Its field quantifies every `J : Type w`, `[Category.{w} J]`, `[IsFiltered J]`;
  stability under colimits is stated for objectwise weak natural transformations
  and arbitrary colimiting cocones. These are exactly colimits of arrows, since
  arrow-category colimits are computed on domain and codomain. `IsFiltered`
  includes nonemptiness and the finite-cocone criterion, so no redundant
  nonempty hypothesis is necessary.
- `hpushout` quantifies all maps `i : A ⟶ B` and `j : K ⟶ L`, with precisely
  `Cofibration i` and `Mono j`. The pushout has legs `T.parameterMap j A` and
  `T.tensorMap K i`, hence objects `(A tensor L)` and `(B tensor K)` over
  `(A tensor K)`. Its codomain is `T.tensor L B`. The two equations with
  `pushout.inl` and `pushout.inr` fix its restrictions to `T.tensorMap L i` and
  `T.parameterMap j B`. Their conjunction with `Cofibration q` is the claimed
  cofibration condition on the canonical pushout-product map. Existence of this
  uniquely characterized map is used instead of an arbitrary unnormalized map:
  the pushout universal property makes any two such `q` equal, and tensor
  naturality guarantees their compatibility. It is therefore equivalent to
  asserting that the displayed canonical map is a cofibration.
- `hcollapse` quantifies every `X : M` and `m : ℕ`, using the map induced by
  `SSet.stdSimplex.map (SimplexCategory.const ⦋m⦌ ⦋0⦌ 0)`. Its target is the
  chosen tensor with `Δ⁰`. That object is canonically isomorphic to `X` by the
  enriched representing property; composing with the isomorphism does not
  change the weak-equivalence assertion.
- The conclusion quantifies every cofibration `i : A ⟶ B` and fibration
  `p : Y ⟶ Z`. The explicit `pullback.lift` maps `sHom B Y` to
  `sHom A Y ×[sHom A Z] sHom B Z`, with projections exactly precomposition
  by `i` and postcomposition by `p`. Mathlib's `eHom_whisker_exchange` supplies
  the compatibility proof. `SSet.modelCategoryQuillen.J.rlp` says this canonical
  map is a Kan fibration. The second conjunct asserts its realization-based weak
  homotopy equivalence whenever `WeakEquivalence i ∨ WeakEquivalence p`.
  Together these are exactly the two triviality cases for a trivial Kan
  fibration, using the Kan-model definitions already recorded by the dependency.
- The universes `u`, `v`, `w` are explicit and independent. Simplicial sets and
  mapping objects have universe `v`, as in the recorded tensor dependency;
  filtered diagrams have object and morphism universe `w`. Completeness and
  cocompleteness cover their maximum. No equality of category-object and
  category-morphism universes is imposed, and no auto-bound variable is used.

Statement dependency declarations read and used:

- `Sheaf.CategoryTheory.SimplicialTensorCotensor`:
  `CategoryTheory.SimplicialTensorCotensor`,
  `CategoryTheory.SimplicialTensorCotensor.tensorMap`, and the interface extension
  `CategoryTheory.SimplicialTensorCotensor.parameterMap` described below.
- `Sheaf.AlgebraicTopology.SimplicialBoundaryCollapseTest`:
  `CategoryTheory.simplicial_boundary_collapse_test`; its full source signature
  and docstring were read, including size and functorial-factorization conventions.

Proof imports are `Mathlib.CategoryTheory.Limits.HasLimits` (the recorded
`CategoryTheory.Limits.colimit`),
`Mathlib.AlgebraicTopology.SimplicialSet.Skeleton`
(`SSet.relativeCellComplexOfMono`),
`Sheaf.AlgebraicTopology.KanQuillenRightProper`
(`SSet.KanQuillen.right_proper_kan_quillen`), and
`Sheaf.CategoryTheory.ReedyModelStructure`
(`HomotopicalAlgebra.Reedy.model_structure`). The last proof dependency,
`lem-coef-reedy-colimit-comparison`, has no published Lean record and so has no
module to import; its use remains explicit in the complete proof docstring.
It is not a notion needed to type the item's statement.

Edge cases checked mathematically before finalizing the statement: `m = 0`
is the identity collapse, the empty simplicial set is allowed in both tensor
parameters, empty coproducts and the dimension-zero empty boundary are retained,
and the `J.rlp` conclusion includes all positive-dimensional horns. The
triviality conclusion includes boundary lifting in dimension zero, hence does
not drop surjectivity on vertices. `IsFiltered` excludes an empty indexing
category and covers the singleton and sequential cases. Identity `i` or `p`
is permitted; both alternatives of the weak-equivalence disjunction remain.
The fixed universes accommodate the skeletal filtration without restricting
objects of `M` to the hom universe.

Searches actually run for this item (2026-10-17):

- `msearch.py leanfinder`, query: "An all cofibrant model category with filtered
  colimit stable weak equivalences is simplicial if tensor pushout products are
  cofibrations and simplex collapses are weak equivalences". Eight hits were
  generic model-category/cofibrancy and simplicial-set model declarations; none
  states this recognition result.
- `msearch.py loogle`, query: `"SimplicialCategory", "ModelCategory"`.
  Zero hits.
- `msearch.py grep`, query: `simplicial.*model|SimplicialModel|pushoutProduct`,
  restricted to `AlgebraicTopology`. Five import/path hits for simplicial-set
  pushout products, no general simplicial-model recognition theorem.
- `msearch.py leansearch`, query: "Recognition of a simplicial model category
  when all objects are cofibrant weak equivalences are stable under filtered
  colimits and simplex tensor maps contract". Eight hits; one supplies the
  exact existing `MorphismProperty.IsStableUnderFilteredColimits` class, reused
  here, and the others are generic model/cofibration infrastructure.
- `rg` in Mathlib's `AlgebraicTopology`, the upstream `WeilConjectures/`, the
  project's `lean/Sheaf/`, and `dag/lean_names_upstream.json` checked the item id,
  recognition names, `SimplicialCategory`, tensor representations, and corner
  maps. No existing recognition theorem was found. Shared helper definitions
  were found in the downstream modules below; their signatures/docstrings and
  DAG dependency paths were read rather than duplicated in the item module.

The primary source HTT Proposition A.3.1.7 and Remark A.3.1.6 were opened online
at https://people.math.harvard.edu/~lurie/papers/HTT.pdf. The criterion agrees
with the node; no `STATEMENT-DISPUTED` issue or statement correction remains.

## Dependency modules

`def-coef-simplicial-tensor-cotensor` receives a lean-only interface repair under
brief-stage2 §1(B). Its existing module, structure, and `tensorMap` are preserved
verbatim. The new `CategoryTheory.SimplicialTensorCotensor.parameterMap` exposes
the canonical induced map for `j : K ⟶ L`, obtained by applying the inverse
representing isomorphism to `j ≫ T.tensorUnit L X`. Its data are entirely the
existing universal elements, curry, and inverse of the specified isomorphism;
it uses no postponed theorem and chooses no unspecified map. The node's
`lean.declarations` lists it and `lean.note` explains the repair. All non-lean
fields of this dependency are unchanged. The source/blueprint docstring is
attached to the helper.

Equivalent helpers exist downstream:
`HomotopicalAlgebra.barTensorParameterMap` in
`Sheaf.CategoryTheory.SimplicialBarProjectiveResolution` and
`CategoryTheory.SimplicialUndercategory.tensorTranspose` in
`Sheaf.CategoryTheory.SimplicialUndercategoryModel`. Neither can be imported
as a statement dependency: the bar node reaches this item through
model-colimit-localization-comparison → small-diagram-model-rectification →
coherent-diagram-coyoneda → right-fibration-section-limit →
simplicial-right-fibration-presentation; the undercategory node reaches it
through simplicial-model-nerve-localization → coherent-nerve-comparison →
pinched-rigidification-resolution → right-straightening-fiber-comparison →
unmarked-straightening-quillen → simplicial-right-fibration-presentation.
The already recorded tensor dependency lacked this parameter-map interface,
so the canonical construction is exposed at its owning dependency, without
waiting on a downstream theorem. The corner map and SM7 predicate also exist
in the downstream nerve-localization module; the item introduces no duplicate
corner-map or SM7 definition, and writes its conclusion with the existing
enriched pre/postcomposition maps and Mathlib's actual pullback lift.

Both delivered modules compiled cleanly through `scompile.py` together in
dependency order. Final delivery validation uses `deliver2.py --no-push`.

## Second reading by N0

I independently opened the node, its HTT source place (Proposition A.3.1.7 and
Remark A.3.1.6), both dependency records, and the two delivered modules.
The item-by-item correspondence is:

- The category is `M : Type u` with `Category.{v} M` and `ModelCategory M`; the
  explicit size-completeness, cocompleteness, and two functorial-factorization
  instances are exactly the conventions inherited from
  `lem-coef-simplicial-boundary-collapse-test`.
- `SimplicialCategory M` and `T : SimplicialTensorCotensor M` provide the
  simplicial enrichment, chosen tensor and cotensor, and enriched representing
  isomorphisms. No second tensor or cotensor notion is introduced.
- `hall : ∀ X : M, IsCofibrant X` renders the all-objects-cofibrant hypothesis.
- `[(weakEquivalences M).IsStableUnderFilteredColimits.{w,w}]` renders the
  filtered-colimit hypothesis. Mathlib's `IsFiltered` supplies nonemptiness
  and finite-cocone conditions for every small `J : Type w`.
- `hpushout` quantifies `i : A ⟶ B`, `j : K ⟶ L`, `Cofibration i`, and
  `Mono j`, and gives the canonical pushout-product map with its two pushout
  equations and `Cofibration q`. The parameter map and tensor map are the
  canonical maps from the dependency module, so this is the node's displayed
  map rather than an arbitrary map.
- `hcollapse` quantifies every `X` and `m : ℕ` and asserts weak equivalence of
  the canonical map induced by `[m] → [0]`; its codomain is the chosen
  `T.tensor Δ⁰ X`, the node's `X ⊗ Δ⁰ ≅ X` presentation.
- The conclusion quantifies a cofibration `i` and fibration `p`. The displayed
  `pullback.lift` has the precomposition and postcomposition projections fixed
  by `eHomWhiskerRight`, `eHomWhiskerLeft`, and
  `eHom_whisker_exchange`; `J.rlp` is the Kan-fibration clause and the
  disjunction implication is the asserted triviality when either input is a
  weak equivalence.
- Universes `u`, `v`, and `w` remain explicit and independent; simplicial sets
  use `v` and filtered indexing categories use `w`.

Edge cases checked: `m = 0` gives the identity collapse; empty simplicial sets,
empty coproducts, and the empty zero-dimensional boundary remain allowed;
`IsFiltered` rules out an empty indexing category while allowing singleton and
sequential diagrams; identity cofibrations and fibrations are allowed; the
dimension-zero boundary case is retained in the triviality assertion.

Searches were repeated with `msearch.py` (LeanFinder, Loogle, grep, and
LeanSearch), plus `rg` over Mathlib, `WeilConjectures/`, `lean/Sheaf/`, and
`dag/lean_names_upstream.json`, using recognition, simplicial-model,
pushout-product, tensor/cotensor, and parameter-map queries. They found no
existing recognition declaration. The recorded tensor dependency was read
against its source; its structure and `tensorMap` are usable, while the newly
recorded `parameterMap` is the required canonical parameter transport.

No mismatch was found, so no statement, hypothesis, universe, or dependency
was changed in this second reading. The only delivery repair is the authorized
§1(B) interface extension adding `SimplicialTensorCotensor.parameterMap`, with
real data from the inverse representing isomorphism and no postponed proof.
Both modules compile cleanly with `scompile.py` in dependency order.
