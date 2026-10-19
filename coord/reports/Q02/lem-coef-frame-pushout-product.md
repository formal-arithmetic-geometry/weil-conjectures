## Worker report

Module: `Sheaf.CategoryTheory.FramePushoutProduct`.
Main declaration: `CategoryTheory.frame_pushout_product`.
The two theorem proofs are `sorry`; all three new definitions contain real data.
No statement correction, disputed statement, new node, or dependency repair is needed.
The only node changes are `lean` and adding the already landed
`lem-cbc-framed-horn-criterion` to `stmt_deps`, to reuse its tensor construction.

Source read: Hovey, *Model Categories*, Proposition 3.1.5, printed p. 76,
Remark 5.2.9, and Proposition 5.4.3, printed pp. 130--131, first clause.
The source is the PDF URL recorded in the node. Proposition 5.4.1 supplies the
relative-latching calculation used in proof steps 1--3. The source's first clause
has the same orientation of the pushout, frame hypotheses, and simplicial
trivial-cofibration hypothesis as this module. Its dual clause is not this node.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A complete and cocomplete model category is `(C : Type u) [Category.{v} C]`
  with `[HasLimits C] [HasColimits C] [ModelCategory C]`. The two
  `MorphismProperty.HasFunctorialFactorization` instances give the specified
  functorial weak factorizations, for trivial-cofibration/fibration and
  cofibration/trivial-fibration, respectively.
- Cofibrant base objects are `{A B : C} [IsCofibrant A] [IsCofibrant B]`.
  `(FA : CosimplicialFrame C A)` and `(FB : CosimplicialFrame C B)` use the
  recorded frame definition: full cosimplicial object, degree-zero identification,
  normalized weak-equivalence augmentation, genuine latching colimits and their
  cofibration maps. These are not merely arbitrary cosimplicial objects.
- The frame map is `(f : FA.obj ⟶ FB.obj)`. Its hypothesis `hReedy` is exactly
  `Reedy.leftClass (monomorphisms SimplexCategory) (cofibrations C) f`, namely
  cofibration of every canonical relative latching arrow. No augmentation
  compatibility of f, localization, enrichment, properness, or combinatoriality
  hypothesis is imposed.
- The tensor is the existing `framedHornCoend T K`, literally
  `colimit (framedHornCoendDiagram T K)` over `K.Elementsᵒᵖ`.
  Its diagram sends a simplex of degree n to `T.obj n` and a triangle to the
  corresponding `T.map`. The opposite is required because Mathlib defines
  elements for covariant type-valued functors. This is precisely the category of
  simplices in Hovey. `framedHornCoendMap` and `framedHornCoendMapObj` are its
  canonical maps in the two inputs; they are reused without a private copy.
- `frameTensorSimplexEvaluation T n` is the actual map induced by applying T to
  each simplex's representing arrow. The first conjunct of `frame_tensor_universal`
  asserts `IsIso` of this map, giving `T ⊗ Δ[n] ≅ T.obj n` for every n.
- `frameTensorTranspose T K Y` sends g to the simplicial map whose component on
  a simplex x is `colimit.ι ... (op ⟨n, x⟩) ≫ g`. Thus its target is the recorded
  `frameHom T Y`, with degree n equal to `Hom(T.obj n, Y)`. The second conjunct
  of `frame_tensor_universal` asserts bijectivity of this canonical map, rather
  than an arbitrary equivalence of sets. Its remaining three conjuncts explicitly
  give naturality under target postcomposition, simplicial-set precomposition,
  and cosimplicial-object precomposition. They express exactly the node's
  natural tensor--Hom identification. The helper theorem requires only colimits,
  as does Hovey's Proposition 3.1.5.
- Arbitrary simplicial sets are `{K L : SSet.{v}}`, in the hom universe of C,
  the universe used by the recorded function complex and tensor. The category
  object universe `u` remains independent. This is the usual small-set convention
  for a locally v-small cocomplete category; v is arbitrary, so no fixed finite
  size or countability restriction is imposed.
- `(i : K ⟶ L) (hi : Mono i)` gives the Kan--Quillen cofibration condition.
  `hiw : SSet.Enhanced.IsWeakHomotopyEquivalence i` gives the recorded
  realization-based weak equivalence. Together they mean precisely a trivial
  cofibration, with no choice of an unrelated simplicial model structure.
- `framePushoutProduct f i` is `pushout.desc` with legs
  `framedHornCoendMapObj f L : A ⊗ L ⟶ B ⊗ L` and
  `framedHornCoendMap B i : B ⊗ K ⟶ B ⊗ L` over the span with center
  `A ⊗ K`. Its commutativity proof follows directly from the colimit injections.
  Consequently the main conclusion
  `Cofibration (framePushoutProduct f i) ∧ WeakEquivalence (framePushoutProduct f i)`
  is exactly the stated trivial-cofibration conclusion on the canonical map.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CosimplicialFrameMapping`:
  `CategoryTheory.CosimplicialFrame`, `frameHom`, `frameHomPre`, `frameHomPost`;
  read their full definitions, including the augmentation-zero and latching fields.
- `Sheaf.CategoryTheory.ReedyModelStructure`:
  `HomotopicalAlgebra.Reedy.leftClass`, `relativeLatching`, `LatchingIndex`,
  `latchingTo`, and `simplex_reedy_structure`; these make the positive maps
  precisely the simplex monomorphisms. Read the model-structure signature too.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.weakEquivalenceStructure`, `right_proper_kan_quillen`, and
  its fixed cofibration/weak-equivalence fields; use `Mono` and the recorded
  `SSet.Enhanced.IsWeakHomotopyEquivalence` in the statement.
- `Sheaf.CategoryTheory.FramedHornCriterion`:
  `framedHornCoendDiagram`, `framedHornCoend`, `framedHornCoendMap`,
  `framedHornCoendMapObj`. Only these constructions are needed; its unrelated
  framed-horn-criterion theorem is not an assumption or a proof shortcut.
- Proof-only imports:
  `Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction`, declaration
  `CategoryTheory.ParametrizedAdjunction.hasLiftingProperty_iff`;
  `Sheaf.AlgebraicTopology.SimplicialBoundaryCollapseTest`, declaration
  `CategoryTheory.simplicial_boundary_collapse_test`;
  `Mathlib.CategoryTheory.MorphismProperty.LiftingProperty`, declarations
  `CategoryTheory.MorphismProperty.llp_isStableUnderRetracts`,
  `rlp_isStableUnderRetracts`, `llp_isStableUnderCobaseChange`, `llp_isMultiplicative`.
  These are all the item's proof dependencies; signatures/docstrings were read.

The main theorem's docstring carries all five DAG proof steps. The tensor helper's
proof docstring explains the colimit universal property, terminal simplex, and all
naturality identities. Each postponed theorem corresponds to explicit clauses of
this same node; no auxiliary mathematical assertion is smuggled in as an assumption.

Edge cases checked: degree zero (the boundary latching diagram is empty), empty
simplicial sets (the tensor is the colimit of the empty diagram), identity i,
identity f, the initial zero frame, and positive-dimensional horn inclusions.
Neither nonemptiness nor positive dimension is required in the Lean statement.
For identity i or identity f the canonical corner is an isomorphism, as expected.
The theorem imposes no fibrancy condition on the ground trivial fibrations used
in proof steps 2--3 and no fibrancy condition on A or B.

Searches actually run:

- `msearch.py ... leanfinder "Reedy cofibration of cosimplicial frames pushout product
  simplicial trivial cofibration"`: eight hits, including path-object and cylinder
  cofibration facts, generic model-category coproduct/cofibration instances and
  `Arrow.cechConerve`; no frame pushout-product theorem.
- `msearch.py ... loogle '"pushout", "Cofibration"'`: zero hits.
- `msearch.py ... leansearch "cosimplicial frame pushout product trivial cofibration"`:
  eight generic trivial-cofibration definitions/closure results; no exact match.
- `msearch.py ... grep 'cosimplicial.*[Ff]rame|frame.*[Pp]ushout|[Tt]ensor.*[Cc]osimplicial'
  AlgebraicTopology`: zero hits.
- `rg` of the upstream WeilConjectures tree for the item id, frame pushout-product
  names and cosimplicial tensors/frames: no theorem or construction matching this item.
- `rg` of `lean/Sheaf` for tensor/coend/frame names found the usable
  `FramedHornCriterion` definitions above; `FrameSourceKanFibration` only mentions
  this item in its proof plan and states the downstream mapping theorem instead.
- `rg` for all five new full declaration stems through pinned Mathlib, upstream
  WeilConjectures, `lean/Sheaf` and `dag/lean_names_upstream.json`: no collisions.

Validation: the required `scompile.py Q02 lem-coef-frame-pushout-product` compiled
both the sandbox and its library-path copy successfully, with no warnings or errors
(2.7 s and 3.0 s reported). An initial compile found a representable-map proof
simplification issue, a missing namespace opening and a letI style warning; all
three were repaired before the clean compile. No direct Lean invocation or global
build was run. The required delivery dry run returned OK at commit `1123e115e5`: preflight and
per-file compilation passed, with exactly the item node, its module and report staged.
The required push follows this successful dry run.

## Second reading by Q02

Author's second pass, with the node statement and final module open; the
maintainer supplies the independent review under this dispatcher's protocol.
Checked the model category and both functorial factorization binders; both
cofibrant bases and the exact recorded frame type; the positive-map relative
latching condition; and the two hypotheses on i. Checked the span orientation
and the two canonical legs of `pushout.desc` against the displayed node formula.
No change in statement was needed. Compared the tensor diagram with Hovey's
category of simplices and verified that the opposite elements category has the
correct direction. The helper theorem retains the representable comparison,
canonical transpose and all three naturality clauses; the main theorem retains
both cofibration and weak equivalence, without a fibrant-target hypothesis.
The initial syntax/type errors described above were repaired, and the finished
file compiles cleanly. Checked every new name for collisions and every delivered
Lean line for the 100-column limit. No independent reader was impersonated and
no other agent was started.
