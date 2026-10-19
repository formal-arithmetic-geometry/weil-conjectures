

## Worker report


### Maintenance recovery: latest validation (2026-10-18)

Attempt `1792280798` passed the complete prescribed seven-module compile and
server preflight at dry-run commit `956b127b7b`. The successful command took
542.216 seconds; its exact output is saved in `recovery-validation.log`.
The following delivery command was interrupted by the worker's 45-minute
deadline. There is no recorded successful push of this repair. The five
`NOANSWER` results are deadline terminations (`Stopped: 15`), not empty
provider responses.

Maintenance compared the retained packet with that Git commit: all seven Lean
modules, all seven JSON node files and this report matched byte for byte at
2026-10-18 00:33 UTC, before this paragraph was added. Subsequently the active
attempt `1792283520` started editing `SemilinearGeometryDerived.lean`; the old
successful dry run does not validate those further edits. Preserve the worker's
new work and validate the current packet before delivery. Maintenance changed
no Lean file or node record. The original H3 objection still needs independent
review; mechanical validation does not certify mathematical correctness.

Resume from the current packet with the prescribed `deliver2.py NF
lem-coef-semilinear-derived-sections --no-push`, retain a passing packet,
finish only the required self-check, then run `deliver2.py NF
lem-coef-semilinear-derived-sections` promptly and answer with its actual
printed result. Reserve time for both commands: each repeats the complete
compile, and the last successful dry run took nine minutes. Use a new command's
concrete diagnostic for any further repair.

The older `dry-run.log`, `split-compile.log`, `split-dry-run.log`, `scratch/`
and `repair*.py` describe earlier revisions; their monolithic-file timeouts do
not describe the validated seven-module packet. Re-running those transformation
scripts would overwrite retained work. `Geometry` is now in
`SemilinearGeometryDerived.lean`, imported through `SemilinearGeometryOps.lean`.
For a direct `scompile.py` check, supply all seven mutually dependent packet
modules together (as the delivery command does); passing only the new derived
geometry file gives a missing `SemilinearGeometryCore.olean` diagnostic because
its sibling is not published yet.


This repairs the immutable returned delivery `2909a6ee908e`. The prescribed
initial dry run accepted the saved packet (`7a42c568c9`), but that mechanical
pass did not address the returned H3 normalization objection. The retained
ordinary-derived construction is preserved; the changes below fix its canonical
geometric maps. The theorem remains
`WeilConjectures.SemilinearSections.semilinearDerivedSections` in
`Sheaf.Paper.SemilinearDerivedSections`, over actual ringed sequence sites.
Generic system definitions and their representative tensor normalization are now
in `Sheaf.Paper.SemilinearSystemModels`, owned by the new definition node
`def-coef-semilinear-system-models`; their declaration names are retained.
The theorem module publicly imports that module. This avoids one enlarged file
exceeding the per-file compile limit, without changing its mathematical content.
The shared current node was compared with the packet: its mathematical statement
is unchanged; only the item's existing dependency additions and Lean records
are delivered. No target or blueprint unit is changed.

All mathematical theorem proofs remain `sorry`, as required for stage 2. Every
such proof has a named declaration, source and blueprint attribution, and a
natural-language proof in its docstring. Definitions have real data. Choices
of maps are from unique sectionwise characterizations. The open extension is
specified by its universal adjunction against constructed restriction, its
actual direct-sum/sheafification models, and normalized unit/counit equations;
this universal property determines it up to unique adjunction-compatible iso.

Hypotheses and clauses, in node order:

| Hypothesis or clause | Lean rendering |
| --- | --- |
| Small site | `C : Type c`, `[Category.{v} C]`, `J : GrothendieckTopology C`; coefficient universe `max c v r`. The displayed essential-smallness instance follows from `essentiallySmallSelf`; site object and morphism universes stay independent. |
| Strict inverse sequence of commutative ring sheaves | `B : ℕ → Sheaf J CommRingCat.{max c v r}`, `τ : ∀ n, B (n+1) ⟶ B n`. Index zero represents the paper's first level. `rings` is `Functor.ofOpSequence τ`. |
| Strict semilinear systems with compatible componentwise maps | `ringPresheaf` uncurries the actual ring tower on `ℕ × C`; `systemRing` adds its vertical sheaf condition. `Systems` is the recorded `ringedSiteModules` of this ring. Horizontal restrictions are exactly the semilinear transition maps; module morphisms already commute with every restriction. |
| Equivalent ring-object realization | `coefficientSequenceTopology J` is the existing vertical topology; `ringPresheaf_isSheaf` supplies only the proof for the constructed ring presheaf. No ring data is postponed. |
| Grothendieck abelian and componentwise exactness | The actual Mathlib abelian instance is used. `Data.grothendieck` is `IsGrothendieckAbelian (Systems ...)`; `Data.componentwise` is an iff for `ShortComplex.Exact` and its images under every actual evaluation. |
| Ordinary unbounded cochain and derived categories | `CochainComplex (Mod ...) ℤ`, `DerivedCategory`, `HasDerivedCategory.standard`; `D` and `DS` abbreviate those localizations. There is no category of diagrams in derived categories. |
| Exact termwise evaluation | `evaluation` is actual continuous module restriction along `Prod.sectR n C`, using the named ring-identification theorem. `evaluation_exact` states additivity and both finite preservation clauses. `e` is its `mapDerivedCategory`; `Data.evaluation_triangulated` asserts triangulated exactness. |
| Joint detection of isomorphisms | `Data.detects` quantifies actual `f : M ⟶ N` in `DS` and concludes `IsIso f` from `∀ n, IsIso ((e n).map f)`. |
| All reduction maps from tau | `coefficientMap h` composes the supplied ring transitions. `transition_exists` uniquely specifies the ordinary map on every section by the actual horizontal restriction of the module presheaf. `derivedTransition` is its localization. `reduction h A M` is its transpose under the recorded derived change-of-rings adjunction. |
| Canonical composition and cocycle | `restrictionComposition_existsUnique` specifies the identity on section groups; `restrictionComposition` localizes it. `Data.scalarComposition_transpose` fixes scalar reassociation by adjunction against that comparison. `Data.reduction_cocycle` is the explicit composed-reduction equation. |
| Normalized/cartesian iff all reductions invertible | `Normalized` is definitionally `∀ {m n} (h : n ≤ m), IsIso (reduction ... h ... M)`. This is one simultaneous condition over all maps, including equal indices. |
| No coefficient flatness assumption | There is no such binder or field. `ScalarData.model` is the recorded everywhere-defined K-flat `DerivedChangeOfRingsCochainModel`; `transpose_model` uses `IsKFlatIndependentCoefficients`. |
| Morphism of topoi, exact inverse image | `SemilinearDerivedSectionsData.geometric` quantifies the given `uInv`, `uPush`, `adjSet : uInv ⊣ uPush`, and `[PreservesFiniteLimits uInv]`. The right adjoint supplies colimit preservation of inverse image. `Geometry.inverseImage` uses the recorded `AlgebraicInverseImage`, including its ring and module operation equations. |
| C_n = u-inverse-image B_n, including coefficient transitions | `Geometry.coefficients`, `inverseImage.ringUnderlying`, and `coefficient_compatibility` identify the underlying coefficient sheaves and the inverse images of the actual tau maps. |
| V on actual systems and derived systems | `Geometry.pull` acts between the displayed `Systems B` and `Systems C`. `ordinaryPullEvaluation` identifies its actual module components; additive and finite-limit/colimit fields express exactness. The derived V is `pull.mapDerivedCategory`. |
| G = total right derived module direct image | `levelPush`, `levelAdjunction`, `levelPushUnderlying`, and `level_unit_underlying` specify the ordinary module direct images and their normalization by `adjSet`. `push` is the ordinary system right adjoint. G is its actual `rightDerivedFunctor`, with K-injective resolution structures on the real module categories. |
| V adjoint G, evaluations and units/counits | `Geometry.adjunction` and `derivedLevelAdjunction` are now normalized by `derived_transpose_model` and `derivedLevel_transpose_model` on K-injective targets. `pullEvaluation_model` fixes exact derived pull evaluation as localization; `pushEvaluation` satisfies both `unit_evaluation` and `counit_evaluation`. The ordinary identifications are identities on section carriers and satisfy `ordinary_unit_evaluation`. |
| Transition compatibility for inverse image | `Geometry.PullTransitionFormula` is the equation obtained from coefficient pullback and the actual system reductions. |
| b_{m,n} is the specified mate | `Geometry.coefficientMate` is defined by `mateEquiv` on `coefficientPullback.hom`. `restrictionPullback_underlying` fixes ordinary coefficient restriction by the identity on underlying sheaves, and `coefficientPullback_transpose` fixes its derived scalar-adjunction transpose. This comparison is oriented as the inverse of `S u^{-1} ≅ u^{-1} T`, precisely as the node requests. It is not an arbitrary natural transformation. |
| Transition of GN | `Geometry.TransitionFormula` explicitly equates reduction of GN, transported by `pushEvaluation`, to `T(pushEvaluation_m)` followed by `coefficientMate` and `G_n(reduction N)`. |
| Actual open localization | `openRings` and `openTransitions` restrict the ring sheaves and tau using `J.overPullback`. `openSite` is `(𝟭 ℕ).prod (Over.forget U)`. `openRestriction` is the actual continuous module restriction along it. |
| Exact j-shriek adjoint j-star and ordinary level adjunctions | `OpenSystems.extension`, `ordinaryAdjunction`, exactness fields, and `extensionEvaluation`/`restrictionEvaluation` refer to the dependency's actual direct-sum/sheafification extension and `overFunctor`. Its `unit_evaluation` and `counit_evaluation` are the specified ordinary level equations. `adjunction` is on their ordinary derived functors; `transpose_model` fixes it as the localized ordinary adjunction. |
| Compatible map of coefficient systems | `F`, `σ`, `α : ∀ n, B n ⟶ F n`, and `hα : ∀ n, α (n+1) ≫ σ n = τ n ≫ α n`. `systemMap_existsUnique` prescribes its section components to be α_n; `systemMap` is that unique ring map. |
| Scalar extension and evaluation to level tensor | `ScalarSystems.scalar` is the recorded change of rings for `systemMap`, and `levels n` is change of rings for α_n. `evaluation` is the natural derived comparison. `transpose_evaluation` fixes it by the actual, identity-on-sections, localized `restrictionEvaluation`. |
| System tensor evaluates to level tensor | `Data.closed.tensor` has domain `DS × DS`, covariant in both inputs. `Data.tensorEvaluation` is the functor isomorphism to the tensor of the actual two evaluations; `Data.tensorEvaluationModel` supplies the total-complex comparison, and `tensorEvaluationModel_ordinary` identifies its ordinary field with `ordinaryEvaluationTensor` exactly. |
| K-flat resolutions and total tensor | `Data.tensorModels` and `levelTensorModels` use the existing `CoefficientTensorModels`: its universal comparison and pure-generator formula retain `CochainComplex.mapBifunctor`, the Koszul total differential, and the independent-coefficient K-flat notion. `Data.scalarTensorModel` adds `ScalarTensorComparisonModel`, whose `derived` field uses `scalarEpsilonIso` and whose `summand` and `ordinary_pure` fields fix the inverse change-of-rings/tensor map on every total summand and pure section tensor. |
| Actual derived internal Hom | `internalHom` is `derivedInternalHomOfUniverses` on the actual ringed site and its chosen ordinary localization. |
| Cartesian first input only; arbitrary second input | `Data.homEvaluation` requires `hM : Normalized ... M`, quantifies arbitrary N by a natural functor isomorphism, and has no comparison for a general first input. |
| System evaluation becomes tensor-Hom evaluation | `Data.homEvaluation_evaluation` is the full component equation between the two evaluation morphisms, including `tensorEvaluation.inv`. |
| Exact Hom reduction transpose | `Data.cartesianReduction` uses the inverse supplied by `hM h`. `homReductionTranspose` is exactly `1 ⊗ t_M^{-1}`, inverse scalar-tensor comparison, scalar extension of evaluation, and `t_N`, followed by the closed transpose. `HomReductionFormula` equates it with the actual system reduction after both Hom-evaluation comparisons. |
| General tensor projection map | `Geometry.tensorProjection` is defined by the normalized derived adjunction Hom equivalence applied to `tensorPullback.hom` followed by `counit ⊗ 1`. `levelTensor_pure`, `TensorComparisonModel.summand` and `.derived`, and `tensor_ordinary_evaluation` canonically fix that tensor map before derived evaluation. `levelTensorProjection` is the same actual level word. |
| Evaluation of projection | `Geometry.tensorPullback_evaluation` specifies the tensor square. `ProjectionEvaluation` is the full equality for evaluation of the constructed projection map and the level projection word. |
| Exchange and evaluation of specified transposes | `evaluation_mate` is a concrete equality for `mateEquiv`, for an evaluated square satisfying the displayed component equation. `AdjunctionEvaluation` requires the actual left/right comparison isos and both normalized unit/counit equations. Thus it applies to the preceding geometric and localized adjunctions, and to their composites, rather than postulating unspecified exchange propositions. |
| Composition, including proper direct-image composites, and mate pasting | The existing `CategoryTheory.mateEquiv_vcomp` and `mateEquiv_hcomp` give the two ordinary pasting identities for these actual squares. `evaluation_mate` expresses compatibility with evaluation for each constructed word. Composition of functors/natural transformations is the ordinary Mathlib construction; no new category of diagrams or equality-detection assumption intervenes. |
| Scope limitations | Neither theorem nor data asks evaluations to reflect equality of arbitrary maps, asks all comparisons to be invertible, asks evaluation to preserve K-injectives, or supplies a right adjoint on normalized objects. |

Dependency declarations used, not merely imported:

- `Sheaf.Paper.SemilinearSystemModels`: the new generic system construction, evaluation, restriction, reductions, `ScalarData`, `Closed`, `Models`, and `TensorComparisonModel`, imported by the theorem module.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules` in `Mod`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: `SheafOfModules.restrictScalars`, in `res` and all reduction adjunctions; its actual `changeOfRings` and sheafification unit normalize `ScalarData.ordinaryAdjunction`.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex` on the real module categories.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory.standard`, `DerivedCategory.Q` in the categories and localization maps.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`: `SheafOfModules.DerivedChangeOfRingsCochainModel`, including E, T, its K-flat comparison counit and universal property; used by every `ScalarData`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`: `Functor.rightDerivedFunctorObjQIso` in both new derived-transpose normalizations; this is the actual right-derived comparison from its unit.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`, `TwoSquare`, the component identities and both pasting identities.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`: the delivered equivalent generic interface described below, with the actual dependency constructions.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`, the exact sheaf-tensor predicate used by `flatTerms`.
- `Sheaf.Algebra.Homology.KFlat`: `IsKFlatIndependentCoefficients`, and canonical coefficient-universe sheafification instances.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, through the recorded total-tensor representative interface `CoefficientTensorModels`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: `derivedInternalHomOfUniverses` in `internalHom`.
- The site notion is Mathlib `GrothendieckTopology`, with the recorded site's covering axioms imported from `Sheaf.CategoryTheory.SiteCoveringAxioms`.
- Already landed `Sheaf.Paper.CoefficientRingedSequenceSite`: reuse its generic `coefficientSequenceTopology`. The coefficient-specific ring constructions in that module do not state this arbitrary-ring-tower theorem.
- Already landed `Sheaf.Paper.CoefficientRingedTensorHomModel`: `CoefficientClosedStructure`, `CoefficientTensorModels`, evaluation and transpose; reused instead of a private tensor/Hom notion.
- Already landed `Sheaf.CategoryTheory.AlgebraicInverseImage`: `SheafOfModules.AlgebraicInverseImage`, including its operations and module-map normalization.

## Dependency modules

Dependency node: `lem-pur-site-restriction-module-adjunction-exact`.

Section 1(B): the recorded localized-module interface fixes site object universe
to u+1, morphism universe to u, and coefficients to u+1. It cannot instantiate
the arbitrary site of this item. The new module
`Sheaf.CategoryTheory.LocalizedModuleExactForSystems` states the same node's
exactness and adjunction with independent site universes c,v and common
coefficient universe max c v r. Its extension is the *same*
`extensionByZeroPresheaf` followed by `PresheafOfModules.sheafification`; its
restriction is the *same* `SheafOfModules.overFunctor`. The normalized adjunction
is uniquely specified by the actual direct-sum summand injection followed by the
actual sheafification unit. The dependency node changes only its `lean` record.
No universe equality and no new mathematical assumption was introduced.

## Searches and edge cases

The retained packet's three search kinds were inspected. Repair searches:

- `msearch.py ... leanfinder 'ordinary derived category of inverse systems of sheaves of modules with varying coefficient rings, evaluation and adjunction mates'`: eight hits (local cohomology diagram, condensed-module and exact-derived linear-functor interfaces); none states the node.
- `msearch.py ... loogle 'SheafOfModules.overFunctor, CategoryTheory.mateEquiv, DerivedCategory'`: no hits.
- `msearch.py ... grep 'Semilinear.*[Ss]ystem|semilinear.*[Ss]ystem' CategoryTheory`: no hits.
- `rg` for the item id in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`: no hits.
- `rg` in `lean/Sheaf` found the already-landed specialized coefficient sequence and tensor/Hom modules. Their full interfaces were read; the generic topology and representative models are reused.
- Source reads of Mathlib `EssentiallySmall`, continuous module pushforward, `overFunctor`, exact-derived factorization, and `Adjunction.Mates` resolved the relevant universe and orientation questions.

Edge checks: empty sites and zero modules/complexes remain legal; no category
inhabitant or nonzero coefficient is assumed. The equality-index reduction is
included. Nonflat coefficient maps are legal. A constant tower and the identity
coefficient map use the same actual restriction and adjunction constructions.
Zero complexes do not make the nontrivial exactness and functor equations into
free propositions. Tensor is covariant in both variables; only internal Hom
has an opposite first input. The cartesian condition quantifies every reduction
simultaneously. Two sites are taken in a common ambient object/Hom universe;
c and v remain independent, and there is no equation between them. The returned
PUnit/PEmpty counterexample is inapplicable: the system and level categories
are derived categories of their actual module sheaves, not supplied parameters.

## Repair of returned H3

The returned defect was real: giving an invertible tensor comparison and an
adjunction, with equations only after derived evaluation, did not specify the
canonical choices. Compatible sign changes could alter the projection word.
The repair fixes the maps at their construction level. `Geometry` contains all
the underlying operations and every normalization below:

1. `ordinaryPullEvaluation_sections` and `ordinaryPushEvaluation_sections`
   require the ordinary identifications to be the identity on section carriers.
   The chosen levelwise construction of each system has exactly those carriers;
   evaluation's coefficient transport does not change them. This specifies a
   realization of the ordinary componentwise functors, rather than a new
   hypothesis on the site or ring tower. `ordinary_unit_evaluation` fixes the
   ordinary system adjunction against the already normalized level adjunctions.
2. `derived_transpose_model` and `derivedLevel_transpose_model` give the exact
   derived Hom-equivalence formula for every complex and K-injective target.
   It is the localized ordinary transpose followed by the inverse of
   `rightDerivedFunctorObjQIso`. Every target has such a resolution, so this
   fixes both derived adjunctions, including units and counits. These equations
   are on the system category itself. They never assume evaluated K-injectives
   are K-injective. `pullEvaluation_model` is the actual composition of the
   exact-derived factorization isos with the localized ordinary realization.
3. `restrictionPullback_underlying` fixes coefficient restriction comparison
   by the identity on the underlying inverse-image sheaf. The specified
   `coefficientPullback_transpose` is its localization, composed with the actual
   scalar-extension unit, transposed by the recorded scalar adjunction. Thus
   `coefficientMate` is now the mate of that canonical comparison.
4. `InverseTensorPure` uses every generalized section, not just global sections:
   an inverse image of a local pure tensor is the tensor of the two inverse
   images via `AlgebraicInverseImage.moduleUnderlying`. `levelTensor_pure`
   imposes this formula. The actual sheafification unit and
   `tensorObjIsoSheafification` construct `tensorSection`.
5. `TensorComparisonModel.summand` fixes the inverse ordinary comparison on
   every summand of the actual signed total complex. The summand inclusions
   determine the chain map. `.derived` states the exact localization square on
   K-flat representatives with flat terms, using the dependency's canonical representative
   comparisons. `flatTerms` is the existing `SheafOfModules.IsFlatOnSite`
   predicate in every degree. The preservation field requires K-flatness and
   flat terms, exactly as Stacks `lemma-pullback-K-flat`; it does not postulate
   preservation of an unnecessarily larger representative class. Such
   resolutions exist for every complex. The square is imposed on systems
   before evaluating them.
6. `ordinaryEvaluationTensor_existsUnique` characterizes ordinary evaluation's
   tensor comparison by its identity on local pure tensors. Its uniqueness is
   why the definition's choice determines an object, as required by the
   no-hollow-definitions rule. `tensor_ordinary_evaluation` uses it to fix the
   system ordinary tensor comparison by its components. Ordinary evaluations
   determine module morphisms; this makes no equality-detection claim for
   derived evaluations. `tensorModel.derived` then fixes the derived system
   tensor comparison independently of that false inference.

7. `Geometry.derivedLevelAdjunction_canonical` and
   `Geometry.derivedAdjunction_canonical` require the displayed derived
   adjunctions to be exactly Mathlib's
   `Adjunction.mapDerivedCategoryRightDerivedAdjunction` applied to the actual
   ordinary adjunctions. The K-injective transpose equations therefore check
   the canonical adjunction itself; changing a unit or counit by a sign cannot
   satisfy these equalities, and the mate used by `tensorProjection` is fixed
   before any evaluation comparison is supplied.

The geometric helpers render the canonical clauses already in this node and
are listed in its `lean.declarations`. The generic construction extracted into
the new definition node is described above; it adds no mathematical requirement
to the theorem.
The main theorem's proof docstring explains their construction. Only the proof
of the uniquely characterized ordinary evaluation comparison is postponed;
its data is uniquely determined by that theorem, not a mere existence choice.

Counterexample/self-check: take a constant integer tower on the punctual site,
identity inverse image, and the degree-zero unit complex. The pure tensor
`1 ⊗ 1` must map to itself, so negating the ordinary tensor map violates
`levelTensor_pure`. Negating the system map violates the ordinary component
square once its component identifications are fixed to the identity. A sign
inserted only after deriving violates `TensorComparisonModel.derived` on these
K-flat representatives. A sign inserted in the derived Hom equivalence violates
the transpose-model formula already for an identity representative map into a
K-injective resolution. The unaltered maps satisfy these tests. The empty site,
zero coefficient ring, zero complexes, identity-index maps, arbitrary unbounded
complexes, and nonflat coefficient maps remain allowed. Site object and morphism
universes remain independent; explicit canonical instances resolve inference
without imposing a universe equality.

## Source-record findings

The current shared node's `source.place` still mentions an enhanced comparison
and attributes only the resolution foundation to Stacks 079P. That text is stale
after the human's ordinary-derived route pivot. Its stage-1 review record says
a corrected source record was prepared, but the actual field in the shared node
still contains the older wording. The Lean module and this report do not claim
that 079P proves the whole statement. The source field is retained under this
worker's lean-only node-edit contract; the discrepancy is also recorded in
`lean.note` for the maintainer.

Sources read for the repair:

- Zheng, *Six operations and Lefschetz--Verdier formula for Deligne--Mumford
  stacks*, local arXiv-1006.3810 PDF, Construction 4.1 (p.21), Lemma 4.10
  (pp.23-24), Definition 4.12 and Proposition 4.17 (pp.24-25). The sequence
  topos and finite left extensions are Construction 4.1; derived direct-image
  evaluation is Lemma 4.10; cartesian-first-input internal Hom is Proposition
  4.17. Zheng calls the all-reductions condition *weakly normalized* in
  Definition 4.12. This node explicitly calls it normalized/cartesian; its
  Lean `Normalized` follows the node's displayed condition, not an asserted
  equality with Zheng's stronger normalization definition.
- Stacks `sites-modules.tex`, `lemma-tensor-product-pullback`: the ordinary
  comparison is the bilinear universal-property map. Stacks
  `sites-cohomology.tex`, `lemma-pullback-tensor-product`: the derived map is
  obtained by totaling those ordinary maps on K-flat representatives.
- Stacks `sites-cohomology.tex`, `lemma-adjoint`: the derived adjunction comes
  from the ordinary one. The actual Lean `rightDerivedFunctorObjQIso` and the
  exact-derived factorization isos were read in full to fix its formula.

The whole arbitrary-ring-tower ordinary calculus is the agent's generalization
of these sources, as the mathematical node itself explains; it is not a verbatim
single-source theorem. No statement is disputed or changed in this repair.

## Validation

The retained packet's first prescribed dry run passed at `7a42c568c9` before
these semantic repairs. That pass is not evidence for the repaired source.
The final repaired compile and delivery checks are recorded below.

## Second reading by NF

This is the fresh repair worker's reading of the retained packet and returned
review, not an endorsement by the independent maintainer. I read the complete
item statement beside all three delivered modules and checked the added
normalization fields against findings 1--2 of the immutable-head review.
The clause table in Worker report records the full hypothesis-by-hypothesis
and clause-by-clause correspondence. In particular:

- The site's object and Hom universes remain independent, and the coefficient
  tower and all transition maps are the actual given ring sheaves and maps.
  The generic definition node gives module sheaves on their vertical sequence
  site; it supplies neither an arbitrary category nor a new tensor operation.
- `Data` asserts componentwise exactness, termwise localization, joint detection
  of isomorphisms, scalar composition and reductions, the all-index cartesian
  condition, and the cartesian-first-input Hom evaluation and transpose formula.
  Nonflat ring maps and arbitrary second Hom inputs remain permitted.
- The geometric fields use actual algebraic inverse image and actual total
  right-derived ordinary direct images. `derived_transpose_model` and
  `derivedLevel_transpose_model` use the ordinary chain adjunction and the
  inverse of `rightDerivedFunctorObjQIso` on K-injective targets. Their
  directions agree: the ordinary transpose lands in Q(push I), and the inverse
  comparison lands in Rpush(Q I). These fix the derived units and counits.
  `pullEvaluation_model` fixes exact pull evaluation by localization.
- `levelTensor_pure` specifies the ordinary map on all generalized pure
  tensors, including the coefficient-ring factor and its unit section 1.
  This is the ordinary unit normalization: m tensor 1 is carried to the
  inverse image of m tensor 1, so the right-unitor square is the usual one.
  `tensor_ordinary_evaluation` imposes the corresponding ordinary system map.
  `TensorComparisonModel.summand` fixes every total-degree summand, and its
  `derived` equation fixes the localized map before derived evaluation.
  Thus the review's simultaneous sign twists fail these equations.
- `restrictionPullback_underlying` and `coefficientPullback_transpose` fix the
  coefficient comparison. `coefficientMate`, `tensorProjection` and their
  level words use the normalized adjunctions and comparisons. Transition and
  projection evaluation equations concern these particular maps.
- Open localization uses the actual slice restriction and the dependency's
  direct-sum/sheafification extension. Its normalized unit and chain transpose
  fix the derived adjunction. The compatible-tower scalar comparison is the
  transpose of the identity-on-sections restriction comparison.
- The final mate equation includes the specified left/right comparisons and
  unit/counit equations; Mathlib's ordinary pasting identities apply. No
  detection of equality by derived evaluations or preservation of
  K-injectives by evaluation has been introduced.

The additional definition node was read against its module: its ordinary
ringed-system construction, normalized scalar unit, horizontal maps, tensor
summands and representative square agree with the listed clauses. The
localized dependency repair retains exactly the actual extension presheaf,
sheafification, slice restriction and section-normalized adjunction at
independent site universes. The two sign counterexamples in the return are
excluded on the constant integer tower; empty sites and zero rings still
admit the constructions. No mathematical statement correction is required.

The source-record discrepancy in finding 4 remains explicitly reported under
Source-record findings and in `lean.note`, as the stage-2 contract permits
only Lean-record changes there. Proposed replacement source attribution:
Zheng Construction 4.1, Lemma 4.10 and Proposition 4.17 (quotient-constant-ring
case); Stacks 079P for K-injective resolutions, 06YY for scalar extension,
03DI--03DJ for localized module adjunctions, 03EL/07A4 for canonical tensor
pullback, and 08J7--08JB for internal Hom. The arbitrary ring-sheaf tower
calculus is the ordinary-derived generalization formulated by this node.
It contains no comparison with enhanced sections.

## Compile-limit repair and final self-check

The retained packet was tested unchanged. The dry run reproduced a 60-second
compile timeout in `SemilinearDerivedSections` on both compilation paths; the
localized dependency and generic system models passed. The repair extracts the
ordinary interfaces unchanged into `Sheaf.Paper.SemilinearDerivedCalculus`,
owned by the new definition node `def-coef-semilinear-derived-calculus`.
The parent imports it publicly and retains all geometric normalization fields,
the existence theorem and the mate equation. This splits elaboration work
without changing a signature, hypothesis, map or equation.

## Compile repair

The retained H3 repair is unchanged mathematically: `GeometryBase` carries the actual ordinary coefficient, pull/push, and unit-normalized fields; `Geometry` extends it with derived evaluations, K-injective transpose models, restriction transposes, and the `TensorComparisonModel`/`InverseTensorPure` representative normalization. The same fields therefore exclude compatible sign twists before evaluation. To satisfy the per-file 60-second compiler limit, the Geometry structure was split into `Sheaf.Paper.SemilinearGeometryCore` and `Sheaf.Paper.SemilinearGeometryDerived`; `Sheaf.Paper.SemilinearGeometryOps` contains the coefficient mate, transition, tensor projection, pull-transition, level projection, and projection-evaluation words. The parent module imports the operations module, so all declarations remain available under their original names and signatures. `scompile.py` compiled all seven sandbox modules cleanly with no diagnostics (the derived structure took 57.9 seconds).

## Retained-packet verification, 2026-10-18

The initial prescribed dry run found a syntax error in the extracted derived
geometry module: the structure docstring preceded `set_option` instead of the
structure. Moved the option and explanatory comment above the docstring. Added
source/blueprint module docstrings to the three extracted geometry modules.
These are documentation and command-placement changes only; the normalized
map formulas and every mathematical signature remain unchanged.

Fresh self-check against the current shared item: only `lean` and added
`stmt_deps` differ; the ordinary-derived statement, proof and source records
remain intact. Read the K-injective transpose equations, ordinary section
identities, pure-tensor formula, total-summand equation and localization square
against the returned H3 finding. They fix the constructions before derived
evaluation and exclude the compatible sign twists identified by the reviewer.
The existing clause table and edge-case analysis still apply.

## New nodes

`def-coef-semilinear-system-models` owns
`Sheaf.Paper.SemilinearSystemModels`. It extracts the generic arbitrary-ring-tower
construction and its canonical representative normalization, which the theorem
needs to state its ordinary-derived calculus. Its declarations retain their
original namespace; the theorem imports them instead of duplicating them.
Every transferred helper and postponed well-definedness theorem now cites this
new node in its blueprint docstring and is listed in its Lean record.

The new statement's clauses are rendered as follows:

| New-node clause | Lean |
| --- | --- |
| Small site and strict varying ring tower | `J`, `B`, `τ`, and the independent `c`, `v`, `r` size parameters; `siteSmall`, `abelianSheafify`, `locallyBijective`. |
| Actual sequence ring and module realization | Existing `coefficientSequenceTopology`; `rings`, `ringPresheaf`, `systemRing`, `Mod`, `Systems`. |
| Ordinary unbounded localization | `D`, `DS`, `hasDerived`, `CochainComplex ... ℤ`. |
| Identity-coefficient vertical evaluation | `evaluation_ring` and `evaluation`; exactness is the well-definedness theorem `evaluation_exact`. |
| Actual coefficient composites and horizontal maps | `coefficientMap`, `res`, `resD`, `transition`, `derivedTransition`; the chosen transformations are uniquely fixed on section carriers. |
| Scalar adjunction and normalized reduction | `ScalarData.ordinaryAdjunction` is normalized by the actual scalar-insertion unit; its `model` and `transpose_model` use the recorded K-flat scalar extension. `reduction` is the actual transpose. |
| Cartesian condition, including identity indices | `Normalized` quantifies every `h : n ≤ m`. |
| Compatible tower morphism and restriction comparison | `systemMap`, `restrictionEvaluation`, and their uniqueness theorems prescribe actual ring components and the identity on underlying sections. |
| Existing Hom, tensor and representative models | `internalHom`, `Closed`, `Models` alias the recorded definitions. `ordinaryTensor`, `tensorSection`, `totalTensor`, `tensorSummand`, and `tensorModelIso` use those constructions and their actual units/inclusions. |
| Exact-functor tensor normalization | `TensorComparisonModel.ordinary`, `.chain`, `.summand`, `.kflat`, and `.derived` specify precisely the ordinary comparison, each total summand and its localization; `flatTerms` is the existing `IsFlatOnSite` condition in every degree. This is data specifying a normalization, not a claim that every exact functor preserves K-flatness. `ScalarTensorComparisonModel` additionally records the actual scalar-extension counit `scalarEpsilonIso`, the K-flat representative square, and `ScalarTensorPure`, whose section formula is `(x ⊗ y) ⊗ 1 ↦ (x ⊗ 1) ⊗ (y ⊗ 1)`. |

Source: Zheng Construction 4.1 for the tower topos construction, generalized
to the arbitrary ring tower in the item's statement; Stacks 03D1, 06YY, 07A4
and 0G7E for the module/scalar/tensor constructions and representative formulas.
The three `msearch.py` searches were rerun for this generic construction and
are recorded verbatim in `mathlib_searches`: LeanFinder found eight ordinary
sheaf-limit/evaluation results, Loogle found no hit (including its reported
unknown `Functor.ofOpSequence` query name); the valid-name repeat `SheafOfModules.restrictScalars, DerivedCategory` also found zero hits. Mathlib grep found no hit.
The DAG/blueprint and upstream/side searches are recorded there too.
`def-coef-ringed-sequence-site` specializes to quotient coefficients on a
pro-etale site, and supplies the generic topology already reused here.
`lem-weil-pbc-diagram-site-realization` uses a constant ring, while the landed
coefficient evaluation calculus is coefficient-specific and downstream.
None gives the generic arbitrary-tower interface. The existing tensor-Hom,
flatness and scalar notions are reused, not redefined.

The scalar/tensor normalization is consumed by `Data.tensorEvaluationModel` and `Data.scalarTensorModel`; `tensorEvaluationModel_ordinary` identifies the evaluation model with `ordinaryEvaluationTensor`. The item's dependencies gain this new node and the already-landed notions
`def-coef-ringed-sequence-site`, `def-coef-ringed-tensor-hom-model`,
`def-weil-pbc-algebraic-inverse-image`, and `def-pc-flat-sheaf-modules`.
Their dependency closures contain no path to the item. The item statement,
proof and source records are unchanged.

`def-coef-semilinear-derived-calculus` owns the extracted `Data` and its Hom
reduction formula, underlying-sheaf and pure-tensor interfaces, normalized
ordinary tensor evaluation, `ScalarSystems`, and `OpenSystems` with its actual
slice constructions and localized transpose. Its source is the same Zheng
4.1/4.10/4.17 and Stacks 03DI--03DJ/06YY/07A4/08J7--08JB construction already
used by the parent. LeanFinder returned eight unrelated localization,
Kähler-differential and module declarations; Loogle returned no hits; Mathlib
grep returned one unrelated semilinear-typeclass comment. Upstream and side
source searches found no interface with these names, and DAG/blueprint searches
found the parent and coefficient-specific consumers. Full search outputs are
in the new node. Its four cited notions are recorded in its dependencies.

Self-check: the extraction moved the exact declaration text, changing only
its blueprint ownership docstrings; all declarations remain public in the same
namespace. The earlier clause correspondence tables therefore still apply.
The new module contains `Data`, its reduction formulas, `ScalarSystems`, and
`OpenSystems`; `Geometry` and its pure-tensor and representative normalization
requirements remain in the parent. The sign tests, empty and zero cases,
nonflat coefficient maps and independent site universes remain unchanged.
The new definition node and both earlier dependency interfaces have been read
against their modules. No mathematical statement correction was made.

The compiler requires one DAG node per delivered module. The three `def-coef-semilinear-geometry-*` records are implementation split records for the same geometric interface already required by this item, not extra mathematical hypotheses: `def-coef-semilinear-geometry-base` owns `GeometryBase` in `SemilinearGeometryCore`, `def-coef-semilinear-geometry-derived` owns the extending `Geometry` structure in `SemilinearGeometryDerived`, and `def-coef-semilinear-geometry-ops` owns the canonical mate and projection words in `SemilinearGeometryOps`. The item lists these records in `stmt_deps`; their statements only name the corresponding fields and preserve the original declarations and signatures.

The implementation split records are `def-coef-semilinear-derived-calculus`, `def-coef-semilinear-geometry-base`, `def-coef-semilinear-geometry-derived`, and `def-coef-semilinear-geometry-ops`; each is named explicitly here for delivery preflight.


## Preflight-record repair, 2026-10-18

All seven modules compiled cleanly in the retained-packet dry run. Server
preflight then identified 21 record/report defects. Corrected the three
geometry nodes' blueprint ancestor and via path, worker/group creation fields,
and minimal none-state audits. Recorded the complete `Geometry extends ...`
signature. Consolidated all new-node descriptions under one `## New nodes`
heading so every added node is visible to the section check.

The missing calculus LeanSearch was run: eight ordinary linear-map/localization
hits, no generic derived-system calculus. Replaced the three geometry records'
summary-only searches with fresh real LeanSearch, LeanFinder, Loogle and Mathlib
grep outputs. The first two found ordinary module pullback and composition,
already reused through dependencies; Loogle and Mathlib grep found no matches.
Upstream and side Lean searches found no interface-name matches; the existing
DAG and blueprint concern the parent calculus and its consumers. Full outputs
are retained in the search records. Expanded the geometry node descriptions
to give their input data and individual normalization clauses; recorded the
derived-interface dependency on the base and the operation dependency on the
derived interface. These repairs change no Lean declaration or parent statement.


## Derived-structure elaboration repair

A subsequent dry run timed out elaborating the large dependent `Geometry`
structure on both the local overlay and server confirmation. Disabled automatic
constructor-injectivity and size-of specification generation for that module,
following Mathlib's convention for large structures. Its fields, constructor,
projections and every stated normalization remain unchanged; these generated
auxiliary lemmas are not part of the delivered mathematical interface.


The optimized packet compiled every file cleanly. Its next preflight found only
four bracket-format errors in the new-node descriptions: combined dependency
citations must be separate `[node-id]` citations. Corrected those citations;
no mathematical or Lean source change was needed.

## Current-packet self-check and validation, 2026-10-18

The prescribed full `deliver2.py NF lem-coef-semilinear-derived-sections
--no-push` passed at commit `172cba9785`, including all seven sibling modules
and server preflight. This validates the retained edits to
`SemilinearGeometryDerived.lean`, unlike the historical recovery dry run.
No Lean source or node record was changed during this recovery attempt.

Re-read the current item and the geometric base, derived and operation modules
against H3. `derivedAdjunction_canonical` and
`derivedLevelAdjunction_canonical` identify both adjunctions with the actual
ordinary adjunctions' `mapDerivedCategoryRightDerivedAdjunction`; the upstream
construction was read. Both K-injective transpose formulas remain present.
`levelTensor_pure` specifies the ordinary inverse-image comparison;
`tensor_ordinary_evaluation` specifies its system comparison using the
section-normalized ordinary evaluation. `TensorComparisonModel.summand` and
`.derived` fix the total-complex map and its localization before evaluation. `Data.tensorEvaluationModel_ordinary` identifies the ordinary evaluation model with `ordinaryEvaluationTensor`, while `Data.scalarTensorModel` fixes scalar extension through `ScalarTensorComparisonModel.derived`, `scalarEpsilonIso`, and `ScalarTensorPure` before localization.
`tensorProjection` and `levelTensorProjection` use precisely these comparisons
and adjunctions. On the constant integer tower and degree-zero unit complex,
a negative pure-tensor map, a negative total-summand map, or a sign-twisted
derived adjunction fails the corresponding normalization. The arbitrary-input,
nonflat-coefficient, identity-index, empty-site and independent-site-universe
cases and the clause table above remain unchanged.

Comparison with the current shared item found changes only to `lean` and the
recorded dependency additions. The new-node and dependency-module descriptions
above still match their owning modules. The source records now cite the ordinary-derived semilinear calculus and its canonical
scalar/tensor comparisons; this self-check is NF's author check,
not the maintainer's independent mathematical review. Proceeding directly to
the prescribed delivery command after this successful dry run.
