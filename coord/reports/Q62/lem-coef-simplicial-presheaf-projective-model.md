## Worker report

The module `Sheaf.AlgebraicTopology.SimplicialPresheafProjectiveModel` states
`SSet.ProjectivePresheaf.simplicial_presheaf_projective_model`. Its only postponed theorem
is this theorem, with proof `sorry`. The docstring gives the node's seven proof steps.
All helper definitions have real data; the structural proofs within `mapping` verify
functor or natural-transformation laws and do not postpone any mathematical theorem.
There is no statement correction, disputed statement, new node, or dependency-module repair.

The node's mathematical statement is unchanged. The module imports the existing project
source declarations `HomotopicalAlgebra.CombinatorialModelCategory`,
`CategoryTheory.SimplicialModelLocalization.SatisfiesSM7`, and `cornerMap` for the
proof plan. Their theorem declarations are not hypotheses of this theorem. The item
retains exactly its base `stmt_deps`; recording the imported localization node would
create the cycle reported by the maintainer, so it is not recorded as a statement
dependency.

Clause-by-clause reading:

- Small simplicial sets are Mathlib `SSet.{u}`; a small ordinary category is
  `(D : Type u) [SmallCategory D]`. Their presheaf category is literally
  `Dᵒᵖ ⥤ SSet.{u}`, whose object universe is `u+1` and Hom universe is `u`.
  Thus the ambient larger universe is available without restricting D or the simplex sets.
- The first existential model `m` is on `SSet.{u}`. Its three structure fields are
  identified with the recorded Kan fibrations, monomorphism cofibrations and
  `SSet.KanQuillen.weakEquivalenceStructure`. The latter uses the realization-based
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, not an unspecified weak-equivalence class.
- Left properness of the Kan model is the quantified implication with `Mono i`,
  a weak-equivalence `w`, and weak-equivalence `pushout.inl i w`. This is the arrow
  from B to the pushout of B ← A → A'. There is no cofibrancy assumption on A.
- `CombinatorialModelCategory.{u+1,u,u}` is the existing structure with
  `IsLocallyPresentable.{u}`, small generating families for the two left lifting
  classes, and functorial factorizations for both weak factorization systems.
  Its underlying Mathlib local-presentability definition is the existence of a
  regular cardinal and a small cardinal-filtered generator of presentable objects,
  with the required small colimits. This renders all terminology in paragraph one.
- The simplicial enrichment on simplicial sets is Mathlib's canonical
  `SimplicialObject.instSimplicialCategorySSet`. The existential
  `SimplicialTensorCotensor SSet` has tensor `X ⊗ K` and cotensor `(ihom K).obj Y`.
  `SatisfiesSM7` uses the actual pre/postcomposition corner map, requires its horn
  right lifting property, and requires weak equivalence when either input is one.
  These are Kan fibration and trivial Kan fibration, by the recorded Kan theorem.
- For each D the second existential `m` is a full `ModelCategory` on the literal
  presheaf category. `HasLimitsOfSize.{u,u}` and `HasColimitsOfSize.{u,u}` make the
  complete/cocomplete convention explicit, beyond the finite limits built into Mathlib's
  model-category class. Combinatoriality supplies functorial factorizations.
- The field equality for weak equivalences is
  `weakEquivalenceStructure.weakEquivalences.functorCategory Dᵒᵖ`; the field equality
  for fibrations is `(modelCategoryQuillen.J.rlp).functorCategory Dᵒᵖ`.
  These say exactly objectwise realization weak equivalence and objectwise Kan fibration.
- The cofibration class equals
  `((modelCategoryQuillen.I.rlp).functorCategory Dᵒᵖ).llp`, so it is precisely
  left lifting against objectwise trivial fibrations. The following inequality to
  `(monomorphisms SSet).functorCategory Dᵒᵖ` says all these maps are objectwise monic.
  It does not claim that every objectwise mono is projectively cofibrant.
- `representable d` is `yoneda.obj d` followed by the constant simplicial-set functor.
  Consequently its value at e is the discrete simplicial set on Hom(e,d), with
  precomposition as restriction. `generatingCofibrations D` is indexed by `D × ℕ`
  and consists of the representable whiskered constant boundary inclusions.
  `generatingTrivialCofibrations D` is indexed by
  `D × (Σ n : ℕ, Fin (n+2))` and uses the horns of dimension n+1. Thus boundaries
  include n=0, and horns cover exactly the positive dimensions and every vertex.
  Their `.rlp` equalities specify exactly the right classes of the two model weak
  factorization systems, so these really are the asserted generating families.
- Projective left properness is the implication involving the model cofibration
  predicate, model weak-equivalence predicate, and `pushout.inl i w`.
- Fibrant objects are expressed using the actual terminal map:
  `m.categoryWithFibrations.fibrations (terminal.from F) ↔ ∀ d, KanComplex (F.obj d)`.
- `tensor K F` is pointwise `F ⊗ const K`; `cotensor K G` is `G ⋙ ihom K`, including
  restriction maps. The tensor/cotensor witness uses these actual object assignments.
  `mapping F G` has n-simplices `tensor Δ[n] F ⟶ G` and precomposition by the
  simplex map as operator. It is a natural-transformation end, not an objectwise
  collection without naturality. `IsUsualEnrichment E` supplies simplicial-set
  isomorphisms to these mapping objects, and requires both the underlying arrow
  formula and the pointwise composition formula with the same simplex parameter.
  Therefore the subsequent `SatisfiesSM7` refers to the specified enrichment.
- There are no finiteness, inhabitedness, nonemptiness, or chosen-object hypotheses on D.

Dependency declarations used:

- Mathlib `AlgebraicTopology.SimplicialSet.Basic`: `SSet`; the recorded degenerate,
  nondegenerate, subcomplex and finite definitions were also read and are not needed
  in this signature. Standard simplices, boundaries and horns are Mathlib's existing ones.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.weakEquivalenceStructure`, `right_proper_kan_quillen` (proof input).
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsWeakHomotopyEquivalence` (realization and all basepoints).
- `Sheaf.AlgebraicTopology.SimplicialBoundaryCollapseTest`:
  `CategoryTheory.simplicial_boundary_collapse_test`; this imports the independent
  model-category convention from Mathlib. It is not invoked as a theorem hypothesis.
- `Sheaf.CategoryTheory.SimplicialTensorCotensor`:
  `CategoryTheory.SimplicialTensorCotensor`, whose enriched representing maps are
  required to be isomorphisms; this retains genuine enriched tensor/cotensor adjunctions.
- `Sheaf.CategoryTheory.ModelColimitLocalizationComparison`:
  `HomotopicalAlgebra.CombinatorialModelCategory` (definition only).
- `Sheaf.CategoryTheory.SimplicialModelNerveLocalization`:
  `CategoryTheory.SimplicialModelLocalization.cornerMap`, `SatisfiesSM7` (definitions only).
- Proof dependencies are imported without `public`: presentability of types/presheaves,
  `SSet.gluing_filtered_weak_equivalences`,
  `SSet.anodyneExtensions_pushoutObjObjι`, presentability ranks from
  `Presentable.LocallyPresentable` (already exposed by the combinatorial definition),
  `HasCardinalLT.exists_regular_cardinal`, and
  `CategoryTheory.SmallObject.functorialFactorizationData` and its retract theorem.
  Each recorded Mathlib match's source and signature was inspected.

Edge cases checked mathematically before writing:

- D empty: one diagram and one arrow, empty generating families, all assertions reduce
  to the terminal model category. The theorem has no binder excluding this case.
- D terminal: reduces to the ordinary Kan model structure.
- D a discrete pair: objectwise independent products; the enriched map is the product
  of the two mapping spaces, as the natural-transformation formula requires.
- D the arrow category, or a one-object group category: naturality restricts the
  enriched maps, and projective cofibrations need not be all objectwise monomorphisms.
  Only the correct one-way implication is stated.
- The zero-dimensional boundary has empty domain. Horn indexing starts in dimension one,
  includes its two outer horns and imposes no dimension-zero nonemptiness test.
- Empty simplicial sets and empty component values are allowed. The fibrant predicate is
  Kan lifting without an inhabitedness assumption.
- Left properness quantifies over arbitrary cofibration sources, not just cofibrant ones.
- No extra equality of unrelated universes is imposed: all indexing data are small in u
  and the presheaf category lives in u+1.

Searches (2026-10-17):

- `msearch.py ... leanfinder "Projective simplicial presheaf model structure with
  objectwise weak equivalences and Kan fibrations"`: eight hits, principally
  `SSet.modelCategoryQuillen` class instances, cofibration/fibration lemmas, `SSet.QCat`,
  coskeleta and the simplicial enrichment of simplicial objects. None states this theorem.
- `msearch.py ... loogle "ModelCategory, SimplicialObject"`: zero hits; the service
  reported unknown identifier `ModelCategory`. Previous-worker search
  `SimplicialCategory, Functor, ModelCategory` likewise returned zero hits.
- `msearch.py ... grep "projective.*model|presheaf.*model|SimplicialCategory.*Functor"
  AlgebraicTopology`: zero hits. The existing project `CombinatorialModelCategory`,
  `cornerMap` and `SatisfiesSM7` were found by direct `rg` and reused.
- Direct `rg` in Mathlib AlgebraicTopology/CategoryTheory, upstream WeilConjectures
  and side `lean/Sheaf` for `SimplicialModel`, `Combinatorial`, `IsLeftProper`,
  `LeftProper`, `projectiveModel`, `projective_model`, `simplicial_presheaf` and
  `simplicialPresheaf`: no exact theorem. Hits about projective complexes are unrelated.
- Required `grep -rn` of this node id in upstream WeilConjectures: no matches.
- The existing definitions above avoid introducing a second model convention.

The source was read online at
https://people.math.harvard.edu/~lurie/papers/HTT.pdf:
Proposition A.2.8.2 and the free-diagram generator proof (printed p. 830 onward),
Example A.3.2.18 (p. 863), and Remarks A.3.3.4--A.3.3.5 (pp. 870--871).
The IAS mirror timed out; the Harvard PDF opened successfully.

Validation: `scompile.py Q62 lem-coef-simplicial-presheaf-projective-model <module>`
compiled both the sandbox probe and module path cleanly, without errors or warnings.
The module's explicit `autoImplicit false` binds every universe and variable.

## Earlier second reading (a previous round; superseded)

I independently read the item's node and complete Lean module, the statement-dependency
nodes and their recorded declarations, and the cited HTT source. The source is HTT,
not a Stacks tag: I opened the Harvard PDF and read A.2.7.3--A.2.7.4,
A.2.8.1--A.2.8.2 with the free-diagram proof, A.3.2.16--A.3.2.18, and
A.3.3.1--A.3.3.5. The general source assumptions are a small indexing category and a
combinatorial coefficient model category; in the enriched version the base is excellent.
The Kan Cartesian model supplies that base, and an ordinary small category is regarded
as discretely enriched. No extra finiteness, inhabitedness, or fibrancy assumption on
the indexing category is needed. The source's homotopy-equivalence convention for
realizations agrees with the recorded weak-homotopy convention since realizations of
simplicial sets are CW complexes. The node has no `statement_change`; no mathematical
statement correction is needed.

Here is my inventory of objects, hypotheses, and conclusions, matched to the Lean.
Each verdict is against the node's actual statement, not just the first report.

| Node item | Lean rendering and verdict |
| --- | --- |
| Small simplicial sets and a larger ambient category universe | `SSet.{u}` is Mathlib's `SimplexCategoryᵒᵖ ⥤ Type u`; its category lives in `Type (u+1)`. Both it and the presheaf category are locally `u`-small. Correct. |
| Kan model, with its specified three classes | The first `∃ m : ModelCategory SSet.{u}` fixes both structure projections to the scoped Mathlib Kan classes and the third to `KanQuillen.weakEquivalenceStructure`. I read that definition: it is precisely `Enhanced.IsWeakHomotopyEquivalence`. Correct. |
| Model-category conventions, including functorial weak factorization systems | Mathlib `ModelCategory` provides the retract, two-out-of-three, lifting, and factorization axioms; `CombinatorialModelCategory` additionally supplies both functorial factorizations. Completeness/cocompleteness hold for simplicial sets; the presheaf clause also asserts `HasLimitsOfSize.{u,u}` and `HasColimitsOfSize.{u,u}`. Correct, with no such properties assumed as extra hypotheses. |
| Kan left properness | For every `i : A ⟶ B` and `w : A ⟶ A'`, the implication assumes exactly `Mono i` and realization weak equivalence of `w`, and concludes this for `pushout.inl i w : B ⟶ pushout i w`. The direction of this map is correct. No cofibrancy premise on `A` is added. |
| Combinatoriality and local presentability | `@CombinatorialModelCategory.{u+1,u,u} _ _ m` uses the existing small generating families and functorial factorization fields. I opened `IsLocallyPresentable` and `IsCardinalLocallyPresentable`: the cardinal is regular, the generator is small, its objects are cardinal-presentable, and the category is cocomplete. Correct. |
| Kan simplicial structure with its usual Cartesian enrichment | `@SatisfiesSM7 _ _ m inferInstance` uses Mathlib's canonical simplicial enrichment of simplicial sets. `SimplicialTensorCotensor SSet` gives genuine enriched representing isomorphisms, and the two equalities fix Cartesian tensor and internal-hom cotensor objects. Correct. |
| Every small ordinary category, with no further hypotheses | `∀ (D : Type u) [SmallCategory D]`; this occurs before the presheaf model witness. There is no chosen object or nonempty/finite instance. Correct quantifier order. |
| The actual presheaf category | The second model witness is on the literal category `Dᵒᵖ ⥤ SSet.{u}`, not a subcategory of fibrant or cofibrant diagrams. Correct. |
| Objectwise weak homotopy equivalences | Equality of `m.categoryWithWeakEquivalences.weakEquivalences` with `(KanQuillen.weakEquivalenceStructure.weakEquivalences).functorCategory Dᵒᵖ`. Correct in both directions. |
| Objectwise Kan fibrations | Equality of `m.categoryWithFibrations.fibrations` with `(modelCategoryQuillen.J.rlp).functorCategory Dᵒᵖ`. Mathlib's `J` consists of all positive-dimensional horns. Correct. |
| Projective cofibrations and their monomorphism property | The cofibration class equals `((modelCategoryQuillen.I.rlp).functorCategory Dᵒᵖ).llp`. The Kan dependency identifies `I.rlp` with trivial fibrations. The subsequent inequality asserts only that projective cofibrations are objectwise monomorphisms. It does not incorrectly identify the two classes. Correct. |
| Discrete representable and boundary generators | `representable d = yoneda.obj d ⋙ Functor.const SimplexCategoryᵒᵖ` has values the discrete `Hom(e,d)` with precomposition restrictions. `generatingCofibrations` uses `D × ℕ` and `representable d ◁ (Functor.const Dᵒᵖ).map (boundary n).ι`, precisely the required product map. Its `.rlp` equality specifies generation of the first model weak factorization system. Correct. |
| Horn generators | `generatingTrivialCofibrations` uses `D × (Σ n : ℕ, Fin (n+2))` and `horn (n+1) i`. This gives exactly every dimension at least one and every vertex in that dimension. Its `.rlp` equality specifies generation of the second model weak factorization system. Correct. |
| Projective left properness | The second pushout implication uses the very same model witness's cofibration and weak-equivalence fields, concluding weak equivalence of `pushout.inl i w`. It has no extra fibrancy or cofibrancy restrictions. Correct. |
| Fibrant objects | The biconditional on `m.categoryWithFibrations.fibrations (terminal.from F)` is exactly `∀ d : Dᵒᵖ, KanComplex (F.obj d)`. Correct. |
| Objectwise tensors and cotensors | `tensor K F` is `F ⊗ const K`; `cotensor K G` is `G ⋙ ihom K`. Equalities for the witness `T` are equalities of entire presheaves, including restriction maps, and `T` is for the same enrichment `E` as SM7. Correct. |
| Enriched maps and their simplicial operators | `mapping F G` has degree `n` equal to natural transformations `tensor Δ[n] F ⟶ G`. Its operator is precomposition by `𝟙 F ⊗ₘ const(Δ[a])`. Thus it retains naturality in `D` and the simplex parameter. Correct. |
| Usual enrichment and the simplicial model axiom | `IsUsualEnrichment E` supplies simplicial isomorphisms to `mapping`, preserves ordinary arrows, and identifies composition with the formula retaining the same simplex parameter. Hence identities and pre/postcomposition agree too. `SatisfiesSM7` uses the dependency's actual `cornerMap`; I opened it and checked both legs of the pullback. It requires a horn-lifting map, and a realization weak equivalence whenever either input is weak. By the Kan dependency this is exactly the trivial-fibration clause. Correct. |

Edge checks: empty `D` is admitted, the generator index sets are empty, and mapping
spaces are terminal because there is exactly one natural transformation between empty
diagrams. A terminal category recovers the Kan model. A discrete pair gives independent
component data, whereas an arrow category or a one-object group category imposes the
required naturality on mapping simplices; this also checks the distinction between
projective cofibrations and all objectwise monomorphisms. Empty component simplicial
sets are allowed. The `n=0` boundary is included, while no zero-dimensional horn is
imposed; the two dimension-one horns are both included. No ring, characteristic,
scheme, or additive zero object occurs. All index and simplex data are small in the
single arbitrary universe `u`; no equality between independent site universes is
introduced. `autoImplicit false` plus the clean compile confirms all variables and
universes are bound.

I repeated the searches with different wording:

- `msearch.py Q62 ... leanfinder "Model category structure on functors to simplicial
  sets via evaluation at objects"`: eight hits, including the Kan class instances and
  the existing simplicial-set enrichment, but no theorem with this node's conclusion.
- `msearch.py Q62 ... leanfinder "Simplicial enrichment of the functor category of
  simplicial sets: mapping simplices are natural transformations from a pointwise
  tensor"`: eight hits. I opened `SimplicialCategory/SimplicialObject.lean` and
  `Functor/FunctorHom.lean`. They provide the existing canonical enrichment of
  simplicial objects (used here for simplicial sets), not this theorem on the literal
  presheaf category. The new mapping construction has the right two diagram directions.
- `msearch.py Q62 ... loogle "SimplicialCategory"`: zero hits, with the service reporting
  an unknown identifier. This unsuccessful query is not evidence of absence by itself.
- `msearch.py Q62 ... grep "model structure|projective_model|projectiveModel"
  AlgebraicTopology`: eight hits in descriptions of the Kan construction; none gives
  this presheaf theorem.
- Direct `rg` across Mathlib AlgebraicTopology and CategoryTheory, upstream
  `WeilConjectures`, and the side `lean/Sheaf` used `projective.*model`,
  `model.*presheaf`, `presheaf.*simplicial`, `SimplicialCategory.*Functor`, and
  `discrete.*representable`. The general diagram-model theorem lacks the additional
  generators and simplicial conclusions; the Reedy simplicial-space theorem concerns
  a different model structure and only the simplex indexing category. Neither is an
  exact existing match. Searching the node id and `ProjectivePresheaf` in upstream
  declarations and `dag/lean_names_upstream.json` gave no collision.

One H4 mismatch found and repaired: the helper `constMap` rebuilt the map of Mathlib's
existing constant functor. I opened `CategoryTheory/Functor/Const.lean` and replaced
both its use and its definition by `(Functor.const Dᵒᵖ).map`. I adjusted the structural
functor-law proofs and removed `SSet.ProjectivePresheaf.constMap` from
`lean.declarations`. The theorem signature and mathematical node statement are unchanged.
No other mismatch was found, and I left the other constructions intact.

There are no new nodes or dependency modules to review. The imported source modules own precisely `CombinatorialModelCategory` and
`SatisfiesSM7`/`cornerMap`, whose source and signatures I read. Their localization
theorems are not assumptions of this theorem. I restored the item's base `stmt_deps`
after the return: the attempted dependency edge to
`lem-coef-simplicial-model-nerve-localization` closes the reported path
`lem-coef-simplicial-model-nerve-localization -> lem-coef-coherent-nerve-comparison ->
lem-coef-pinched-rigidification-resolution -> lem-coef-right-straightening-fiber-comparison
-> lem-coef-unmarked-straightening-quillen -> lem-coef-simplicial-presheaf-projective-model`.
The module still imports the source declaration for the proof plan, while the DAG no
longer contains the cycle.
I also checked the recorded Kan theorem, realization predicate, tensor/cotensor universal
elements, boundary-collapse convention, and the proof-input declarations for local
presentability, anodyne pushout products, cardinal bounds, and small-object factorization.
There is no unusable dependency hidden behind a private notion.

H5/H6/H8/H9: every definition contains real data, the only postponed theorem is
`simplicial_presheaf_projective_model`, and its proof remains `sorry`. The structural
functor-law proofs establish the data's laws only. The module and every declaration
have source and blueprint docstrings. The theorem's docstring follows the node's seven
steps, including the cotensor lifting argument rather than an unsupported cell argument
for SM7. No file-local notation or instance is introduced. The node's `lean.statement`
is verbatim the signature in the file; no declaration or universe is implicit.

Validation after repair: `scompile.py Q62 lem-coef-simplicial-presheaf-projective-model
lean/Sheaf/AlgebraicTopology/SimplicialPresheafProjectiveModel.lean`, run from the sandbox,
compiled both probe and library module cleanly (1.6 s and 1.7 s), without warnings.


## Repair after return

The maintainer's immutable-head diagnostic reported a cycle introduced by the prior
packet's extra `stmt_deps` entries. I removed both unauthorized additions, restoring
the item's original five statement dependencies, and updated the owned `lean.note` to
state that the imported source declarations are proof-plan interfaces rather than
statement hypotheses. No statement, declaration, or mathematical clause changed.
The cycle path was checked against the full DAG; the remaining five dependencies do
not reach the item.

## Second reading by Q62

I reread the current node copy, its HTT source place (Example A.3.2.18,
Remark A.3.2.17, Proposition A.2.8.2, Remarks A.2.8.4--A.2.8.5 and
A.3.3.4--A.3.3.5), all five statement dependencies, and the complete module.
The node has no `statement_change`; its `lean` record names
`Sheaf.AlgebraicTopology.SimplicialPresheafProjectiveModel` and the declaration
`SSet.ProjectivePresheaf.simplicial_presheaf_projective_model`.

The statement inventory and verdicts are:

- The ambient universes and small simplicial sets are rendered by `SSet.{u}`;
  the presheaf category is literally `Dᵒᵖ ⥤ SSet.{u}` and therefore has the
  intended larger object universe. Correct.
- The first existential model has exactly the Kan fibrations, monomorphism
  cofibrations, and `KanQuillen.weakEquivalenceStructure`; its left-properness
  implication has precisely `Mono i` and a weak-equivalence `w`. Correct.
- `CombinatorialModelCategory`, `SatisfiesSM7`, and the existential
  `SimplicialTensorCotensor` express local presentability, generating/functorial
  factorizations, Cartesian tensor/cotensor, and both SM7 triviality cases.
  Correct; no extra hypotheses occur.
- The quantifier `∀ (D : Type u) [SmallCategory D]` imposes no finiteness,
  inhabitedness, or chosen-object assumption. Correct.
- The second model witness is on the full functor category. Its weak-equivalence
  and fibration equalities are respectively objectwise realization weak
  equivalences and objectwise Kan fibrations. Correct.
- Cofibrations are exactly the left lifting class against objectwise trivial
  fibrations, with only the asserted one-way inclusion into objectwise
  monomorphisms. Correct.
- `representable` is the discrete Yoneda presheaf; the boundary family is
  indexed by `D × ℕ`, and the horn family by `D × (Σ n, Fin (n+2))`. Thus
  boundaries include dimension zero and horns include every positive dimension
  and vertex. Their `.rlp` equalities state the two generating families. Correct.
- The projective left-properness implication, terminal-map fibrant-object
  biconditional, and objectwise tensor/cotensor equalities are all present in
  the same order as the node. Correct.
- `mapping F G` has simplices the natural transformations
  `tensor (stdSimplex.obj n.unop) F ⟶ G`, with operators by simplex-parameter
  precomposition. `IsUsualEnrichment` additionally fixes underlying arrows and
  composition, so the following `SatisfiesSM7` refers to this mapping object.
  Correct.

Edge cases checked again: empty `D` gives the unique diagram and empty generator
families; terminal and discrete categories reduce as expected; arrow and group
categories retain naturality; `n = 0` occurs only for boundaries; empty simplicial
sets and empty component values are allowed; no ring, characteristic, scheme, or
zero-object hypothesis is introduced; all universes and variables are bound by
`set_option autoImplicit false`.

I repeated searches with LeanFinder/Loogle and direct `rg` over Mathlib,
`WeilConjectures`, and `lean/Sheaf` for projective simplicial-presheaf model
structures, representable boundary/horn generators, and simplicial functor
enrichments. The hits are Kan-model or unrelated projective-complex/Reedy
results; no exact declaration exists. The recorded dependency declarations were
opened and match their uses. No missing definition node or unusable dependency
module was found, and no new cycle was introduced.

The only earlier H4 repair remains valid: the helper `constMap` was removed in
favor of Mathlib's `(Functor.const Dᵒᵖ).map`; no private duplicate remains. No
other mismatch was found, so the module and node statement were left unchanged.
H5/H6/H8/H9 checks pass: definitions have real data, only the named theorem has
`sorry`, all declarations carry source and blueprint docstrings, and the theorem
docstring contains the seven proof steps. `scompile.py` compiled the module and
probe cleanly in 1.7 seconds.
