## Worker report

The module `Sheaf.CategoryTheory.RightResolutionMappingCriterion` states
`CategoryTheory.right_resolution_mapping_criterion`, with its entire proof `sorry`.
The four supporting definitions construct the actual simplicial object,
coaugmentation, matching limit with universal property, and matching map. None
chooses an object from an unproved existence theorem. There is exactly one
postponed theorem, matching the assigned DAG node, with all six proof steps in
its docstring. The node copy changes only `lean`.

The right resolution is the existing `CategoryTheory.CosimplicialFrame` in the
opposite model category, rather than a second definition of a frame. Taking
opposites gives precisely all the right resolutions in the node, including all
choices of matching limits. The four helpers only expose these canonical parts
of that same notion, as authorized by the brief's helper rule. No new DAG notion
or dependency repair is needed.

Hypothesis and clause correspondence:

- The arbitrary model category is `(C : Type u) [Category.{v} C] [ModelCategory C]`.
  Completeness and cocompleteness are `[HasLimits C] [HasColimits C]`. Both
  `MorphismProperty.HasFunctorialFactorization` instances express the two
  functorial factorization systems assumed in the dependency's conventions.
  Mathlib's model structure supplies two-out-of-three, retract closure and the
  mutually characterized lifting classes. There is no properness,
  combinatoriality, or enrichment hypothesis.
- `universe u v t`, `K : SSet.{max u v t}`, and
  `q : FiniteReedy.largeNerve.{u, v, t} C ⟶ K` implement the size convention
  without identifying object and morphism universes. The hypothesis
  `FiniteReedy.IsLocalization (weakEquivalences C) q` specifies the node's
  homotopy coherent localization; it is not a substitute for any mapping
  comparison in the conclusion. The extra universe `t` permits enlargement.
- `(Z : C) (hZ : IsFibrant Z)` is exactly the fibrant target hypothesis.
- `Nonempty (CosimplicialFrame Cᵒᵖ (op Z))` states existence. For each witness
  `A`, `rightResolutionObject A = A.obj.leftOp` has type `SimplicialObject C`.
  `rightResolutionCoaugmentation A = A.augmentation.leftOp` is literally the
  coaugmentation from `const Z`, with all its naturality. The existing
  `augmentation_weak` field says objectwise weak equivalence; `degree_zero`
  and `augmentation_zero` say the degree-zero object is `Z` and the
  coaugmentation component is the identity after equality transport.
  The `latching_cofibration` field in the opposite category is precisely
  Reedy fibrancy of this simplicial object. Thus these requirements are
  supplied by the reused structure, not dropped from the statement.
- The following `∀ A : CosimplicialFrame Cᵒᵖ (op Z)` quantifies over every such
  resolution, independently of the existence witness.
- `rightResolutionMatchingLimit A n` has type
  `LimitCone ((frameLatchingDiagram A.obj n).leftOp)`. Its cone and universal
  property are the concrete Mathlib duals of `A.latching n`. The indexing
  category is `(FrameLatchingIndex n)ᵒᵖ`: objects are proper injective faces
  `[k] → [n]`, with `k < n`, and all compatible triangles. Taking opposites
  turns them into exactly the proper face restrictions out of `[n]` in
  `Δᵒᵖ`. This is the simplicial specialization of the recorded Reedy matching
  convention. `rightResolutionMatchingMap A n` is the opposite of the
  canonical colimit descent to the latching cocone, so it is the canonical
  map to that matching limit, not an arbitrary arrow. The assertion
  `∀ n : ℕ, Fibration (rightResolutionMatchingMap A n)` covers all original
  fibrations, including zero.
- `Nonempty (IsTerminal (rightResolutionMatchingLimit A 0).cone.pt)` states
  `M₀ = 1` in the categorical sense of a terminal object. No equality of
  independently chosen terminal objects is imposed.
- `frameHom A.obj (op T)` has n-simplices
  `Hom_{Cᵒᵖ}(A.obj.obj ⦋n⦌, op T)`, definitionally
  `Hom_C(T, (rightResolutionObject A).obj (op ⦋n⦌))`. Its simplex operators
  come from the whole functor, including degeneracies. The clause with
  `∀ T, IsCofibrant T → ...KanComplex` is exactly the Kan assertion.
- The existential `comparison` supplies, simultaneously for every cofibrant
  `T`, an isomorphism between the right function complex and
  `SSet.Enhanced.mappingSpace K (FiniteReedy.object q T)
  (FiniteReedy.object q Z)` in `FrameSpaceHo`, the recorded localization of
  spaces at realization weak equivalences. `frameHomLarge` is the dependency's
  canonical universe lift, not a new mapping complex. This is representation
  of the full mapping-space homotopy type, not merely a comparison of π₀.
- The `FrameMappingRelation` clause renders naturality for every actual map
  `u : U ⟶ V` between cofibrant sources. It uses the actual edge `frameQEdge q u`
  and the degenerate edge at `qZ`, and hence the canonical endpoint-evaluation
  span for contravariant precomposition. Its second comparison leg is
  `(comparison V hV).inv ≫ frameSpaceQ.map (frameHomLargePost A.obj u.op)`;
  this is the actual restriction map, with no free action map supplied as data.
- The final quantifiers have exactly `IsCofibrant U → Cofibration u →`.
  Cofibrancy of `V` is a consequence of these hypotheses, not an additional
  assumption in the fibration or equivalence criterion.
  `SSet.modelCategoryQuillen.J.rlp (frameHomPost A.obj u.op)` says restriction
  is a Kan fibration, by the recorded horn test.
- Condition (i) is
  `IsIso (frameSpaceQ.map (frameHomLargePost A.obj u.op))`: equivalence of the
  canonical right homotopy function complex map in the homotopy theory of
  spaces. Through `comparison` and its specified naturality this is exactly
  equivalence of `Map^h(V,Z) → Map^h(U,Z)`. Using this actual representative
  avoids introducing an arbitrary map between derived mapping spaces.
- Condition (ii) is
  `SSet.modelCategoryQuillen.I.rlp (frameHomPost A.obj u.op)`, precisely the
  dependency's trivial Kan fibration/boundary test. The first displayed iff
  is (i) iff (ii).
- Condition (iii) is
  `∀ n : ℕ, HasLiftingProperty u (rightResolutionMatchingMap A n)`.
  Mathlib's `HasLiftingProperty` means a diagonal in every commuting square,
  not a chosen splitting. The second iff is (ii) iff (iii). Together the
  two iff clauses express equivalence of all three conditions.

Dependency declarations read and used:

- `def-weil-size-convention` is explicitly a metatheoretic convention with no
  Lean declaration or module; the explicit universes above implement it.
- `Sheaf.CategoryTheory.CosimplicialFrameMapping`:
  `CategoryTheory.CosimplicialFrame`, `FrameLatchingIndex`,
  `frameLatchingDiagram`, `frameLatchingCocone`, `frameHom`, `frameHomPost`,
  `frameHomLarge`, `frameHomLargePost`, `frameSpaceQ`, `frameQEdge`, and
  `FrameMappingRelation`. The full signatures and docstrings of the structure,
  comparison interface and `cosimplicial_frame_mapping` were read. This module
  also supplies the recorded `FiniteReedy` coherent-localization interfaces.
- `Sheaf.CategoryTheory.ReedyModelStructure`:
  `HomotopicalAlgebra.Reedy.MatchingIndex`, `matchingProjection`,
  `matchingCone`, `matchingFrom`, `model_structure`, and the prescribed-zero
  factorization interface. This import supplies the Reedy proof plan and the
  opposite model structure; the actual matching limit is obtained by canonical
  opposite-category duality of the already recorded proper-face colimit.
- `Mathlib.CategoryTheory.MorphismProperty.LiftingProperty`:
  `CategoryTheory.MorphismProperty.llp`, `rlp`,
  `llp_isStableUnderRetracts`, `rlp_isStableUnderRetracts`,
  `llp_isStableUnderCobaseChange`, and `llp_isMultiplicative`, as recorded
  in the dependency's `mathlib_match`. The diagonal meaning is Mathlib's
  `CategoryTheory.HasLiftingProperty`.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.right_proper_kan_quillen`, whose signature and proof docstring
  identify horn lifting `modelCategoryQuillen.J.rlp` with Kan fibrations and
  boundary lifting `modelCategoryQuillen.I.rlp` with trivial Kan fibrations.
  In particular the boundary family includes dimension zero.
- `Mathlib.CategoryTheory.Limits.Opposites`:
  `CategoryTheory.Limits.coneLeftOpOfCocone` and
  `isLimitConeLeftOpOfCocone` construct the matching limit with real data.

Edge cases checked mathematically before writing: at `n = 0` there is no proper
face and the empty-diagram limit is terminal; the boundary test still includes
this dimension and tests vertex lifting. For `u = 𝟙 U`, restriction is the
identity, all three conditions hold, and all matching lifting problems have
the evident diagonal. For initial/cofibrant `U`, the function complex from `U`
is terminal and the test becomes contractibility of the complex from `V`, as
expected. A terminal target permits the constant terminal resolution and
terminal right function complexes. Empty mapping complexes remain allowed:
no nonemptiness hypothesis on a Kan complex is imposed; dimension-zero
boundary lifting detects failures of surjectivity. Different object, morphism
and comparison universes are retained. The theorem quantifies over arbitrary
right resolutions, not a specially chosen relative trivial-cofibration one.

Searches on 2026-10-17 (the wrapper also recorded exact results in searches.jsonl):

- LeanFinder via `msearch.py`: “Simplicial resolution of a fibrant object computes
  derived mapping spaces and cofibrations lift against its matching maps exactly
  when the induced map is a trivial Kan fibration.” Eight hits on ordinary
  cofibrant/fibrant replacements and homotopy categories; no matching theorem.
- LeanSearch via `msearch.py`: “Right simplicial frames of fibrant objects
  characterize equivalences of homotopy function complexes by lifting against
  matching maps.” Eight hits, including `ModelCategory.cm4a`, ordinary homotopy
  relations and the horn definition of Kan fibrations; no resolution criterion.
- Loogle via `msearch.py`: `"HomotopicalAlgebra", "IsFibrant"`. Twelve hits
  defining fibrancy or its elementary consequences; no matching theorem.
- Mathlib grep via `msearch.py`:
  `matchingObject|matchingMap|SimplicialFrame|homotopyFunctionComplex` in
  `AlgebraicTopology`, and
  `simplicial.*resol|matching.*fibration|homotopy.*function.*complex` in
  `AlgebraicTopology/ModelCategory`: both returned zero hits.
- Direct `rg` of the source `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for right resolutions, simplicial frames,
  matching criteria, the item id and proposed declaration names: no existing
  theorem. The reusable `CosimplicialFrame` and mapping interface above were
  found and used; unrelated derived-category right resolutions were rejected.

Source checked: [Hirschhorn's book](
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/pshmain.pdf),
§§16.1, 16.6, 17.2 and 17.8, following the node's source places. The source's
right homotopy function complex convention agrees with the opposite-frame
encoding. No source-based correction is needed, and there is no
STATEMENT-DISPUTED issue.

Validation: the prescribed `scompile.py Q99 lem-cbc-right-resolution-mapping-criterion`
checks this module individually, including its public-library import check.
The final delivery dry run is run with `deliver2.py ... --no-push`; the independent
second reader is responsible for the second-reading section and actual delivery.

## Second reading by Q99

I read the item node, its source place, the dependency node records and the full
Lean declarations before checking the module. The node's objects, hypotheses and
conclusion match the following Lean components:

- The model category `C`, category universe `v`, object universe `u`, limits and
  colimits, model structure, and the two functorial factorization hypotheses are
  the binders at lines 120--124. These are exactly the model-category conventions;
  no properness, combinatoriality, enrichment, or finiteness assumption is added.
- The size data `K`, `q`, and `hq` at lines 125--126 render the node's coherent
  localization and universe convention. The independent `t` universe is retained.
- `Z` and `hZ` at lines 126--127 are the fibrant target. The existential at line
  128 is `CosimplicialFrame Cᵒᵖ (op Z)`, whose `leftOp` is the required simplicial
  object. Its `augmentation`, `augmentation_weak`, `degree_zero`, and
  `augmentation_zero` fields give the coaugmentation, objectwise weak equivalence,
  degree-zero object, and identity component. Its latching cofibrations become
  Reedy matching fibrations in the opposite category.
- For every frame `A` (line 129), `rightResolutionMatchingLimit A n` (lines 66--70)
  is the actual limit dual to the proper-face latching colimit, and
  `rightResolutionMatchingMap A n` (lines 77--80) is its canonical map. Thus line
  130 states the original fibration property for every `n`, while line 131 states
  that the degree-zero empty matching limit is terminal.
- The Kan clause at line 132 uses `frameHom A.obj (op T)`, whose simplices are
  exactly `Hom_C(T, Z_n)`, for every cofibrant `T`. The existential comparison at
  lines 133--143 gives the natural localized mapping-space representation; its
  `FrameMappingRelation` clause records the canonical restriction action for every
  map between cofibrant sources.
- The final quantifiers at lines 144--149 are exactly a map `u : U ⟶ V` with
  cofibrant source and a cofibration. They state first the Kan fibration, then
  (i) invertibility of the canonical localized restriction iff (ii) the boundary
  lifting condition, and finally (ii) iff (iii) left lifting against every
  matching map. `HasLiftingProperty` is the square-and-diagonal meaning required
  by the node. No quantifier is reordered or strengthened.

I checked the source at Hirschhorn Definition 16.1.2(2), Theorem 16.6.9,
Definition 17.2.1, Theorem 17.8.4, Proposition 17.8.5, and Proposition 17.8.8.
The dual simplicial-frame construction, matching-map boundary test, and
homotopy-function-complex criterion agree with the node. I also checked the
dependency declarations `CosimplicialFrame`, `frameHom`, `FrameMappingRelation`,
the Reedy matching/extension interfaces, the Kan--Quillen boundary characteriza-
tion, Mathlib's lifting-property definitions, and opposite-cone limit duality.

Edge cases are covered: `n = 0` has the empty matching category and terminal
matching object; the boundary family still includes dimension zero; identity
maps satisfy all three conditions; initial/cofibrant sources and terminal targets
are allowed; empty mapping complexes are not excluded; and all object, morphism,
and localization universes remain independent. The zero object and empty index
cases therefore remain within the stated quantifiers.

Independent searches used LeanSearch, LeanFinder, Loogle, and `rg` over Mathlib,
`WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`, with
queries for right resolutions, simplicial frames, matching maps, and homotopy
function complexes. They found no existing declaration or theorem; the recorded
`CosimplicialFrame` is the one reusable notion and is not duplicated here.
The second-reader LeanFinder query was “A homotopically constant fibrant
simplicial object gives mapping spaces and the right lifting property of
restriction against simplex boundaries equals left lifting against matching
projections” (eight hits on horn fibrations, Joyal lifting, and path objects).
LeanSearch used “Simplicial fibrant resolutions and boundary matching projections
detect weak equivalences of derived Hom spaces” (eight replacement/horn hits).
Loogle used `"HasLiftingProperty", "SimplexCategory"` (zero hits). The broad
wrapper grep returned unrelated right-function matches; a focused independent
`rg` for `simplicial.{0,60}(resolution|frame)`,
`right.{0,20}function.{0,20}complex`, and
`matching.{0,20}(projection|fibration)` found the reusable dependency modules
and unrelated bar/hypercover constructions, with no duplicate criterion.

No Lean or node-statement mismatch was found, so no statement or definition was
changed. The only delivery content added by this second reading is this report
section; the module compiled cleanly with the prescribed `scompile.py` command.
