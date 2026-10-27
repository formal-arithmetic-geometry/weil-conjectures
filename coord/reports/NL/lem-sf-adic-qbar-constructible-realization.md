## Worker report

Item: lem-sf-adic-qbar-constructible-realization. Group: NL. Stage 2, 2026-10-22.
The delivered theorem is `WeilConjectures.AdicQbarRealization.adic_qbar_constructible_realization`.
Its conclusion packages the canonical equivalences and every comparison in `Family`.
`FamilyCore` holds the comparison data; `Family` extends it by all normalization and
coherence laws, with no change to their quantifiers or equations.
The main theorem and the new canonical-map existence/uniqueness theorem are postponed.
Definitions contain actual constructions; comparison data in structures are constrained by section formulas, representative formulas and coherence equations.
The source statement has not been corrected or disputed.

The previous worker's stale-assignment observation concerns the stage-1 split, whose repair note
is resolved. The live node has status split and a stage-1 PASS but no stage-2 lean record. This
is its stage-2 statement; it does not redo or change the reviewed split.

Hypotheses and clauses, in order:

* The fixed geometric finite field is the recorded `FiniteFieldDatum D`. Its `k` is the chosen
  algebraic closure of its finite field `k₀`; the prime characteristic is `D.p` by its specified
  cardinality. The theorem binds `l`, `[Fact l.Prime]` and `hl : l ≠ D.p`. The coefficient closure
  is exactly the dependency's fixed `PadicAlgCl l`, not a new closure or a discrete coefficient
  ring. Finite fields are `AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)` and their
  recorded size models `Coefficient.{u}`.
* `GeometricSpace D` bundles `Over (Spec (.of D.k))` with separated, locally-of-finite-type and
  quasi-compact structure morphism. Thus it means separated finite type, not merely locally
  finite type. Every such object is quantified in `Family.data`. Invertibility of `l` is a
  conclusion field `SpaceData.units`, never an added hypothesis on T.
* `ring` is the existing native locally finite coefficient in ordinary commutative-ring-sheaf
  coordinates, obtained from `LocallyFiniteAdicRealization.ringSheaf`. `modules` is exactly
  `ringedSiteModules.{u+1}` on its underlying ring sheaf. Its sections retain the native
  finite-subextension-valued continuous functions; no constant/discrete Ω construction appears.
* The source is exactly `generalAlgebraicallyClosedConstructibleCategory` of the recorded
  dependency, hence the actual pair category with raw rationalized stages. No Karoubi envelope
  is inserted. `ordinary` is the recorded `Realization.J` followed by the actual exact derived
  section-module functor.
* `boundedConstructible` uses the existing `ProEtale.DerivedCategory.boundedAdicConstructible`
  transported by `sectionDerived`. That native predicate is bounded cohomology, with each
  cohomology sheaf admitting a finite locally closed scheme stratification and pro-etale locally
  finite free restrictions. `SpaceData.presentation` asserts that the actual section functor is
  an equivalence. This is the ordinary presentation of that same predicate, not a new
  constructibility condition defined as the image of the proposed realization.
* `SpaceData.fully_faithful` is bijectivity on every ambient derived Hom. `SpaceData.image`
  gives exactly the above full bounded constructible essential image, in both directions.
  These two clauses express the claimed equivalence to the full subcategory. `shift` and
  `exact` require exactness for the recorded shifts and distinguished triangles.
* `SpaceData.realization.integral E` is a natural isomorphism on integral representatives to
  `pbcDerivedExtend` of the actual `coefficientMap`. That map uses the stored commutativity
  proof and the recorded continuous integral identification, integral inclusion and finite-field
  inclusion. Naturality fixes all integral arrows. Raw localization fixes their fractions, and
  the existing `common_field` equation fixes arrows represented after a common finite extension.
  `coefficient_scalar` and `common_field` retain the identity and tower comparisons induced by
  the normalized completion map and balanced derived tensor multiplication.
* `At.closed`, `models`, `symmetry` and `coherence` use the recorded ambient K-injective Hom,
  K-flat total tensor, coefficient unit in degree zero, signed symmetry, associator and unitors.
  `At.tensor` is a natural tensor isomorphism and `At.unit` the coefficient-unit isomorphism.
  The fields `associative`, `left_unit`, `right_unit`, and `symmetric` are the full coherence
  squares, with the source operations precisely `commonStageDerivedTensor` and the recorded
  source associator, braiding, coefficient unit and unitors.
* `FiniteNormalization` pins this tensorator, rather than allowing an arbitrary monoidal
  structure. `completion` is the existing ordinary-to-completed tensor presentation including
  every quotient pure-section, zero shifted-coordinate, descent and completeness clause.
  `balance_sections` sends s⊗(x⊗y) to (s⊗x)⊗(1⊗y). `representative` descends that map through
  the universal derived-extension cochain counits and the ambient K-flat tensor model.
  `integral_tensor` identifies it with `At.tensor` through the literal rational tensor objects
  and the actual common-stage tensor inclusion. `SpaceData.finite` quantifies over every finite
  coefficient subfield. The recorded common-stage naturality and scalar associators thereby
  include finite coefficient extension and towers, including E=F.
* Permitted pairs are exactly `commonStageHomPairs`, including its integral-constructibility
  qualification. The source Hom is exactly `commonStageDerivedInternalHom`.
  `homComparison` is defined as `closed.transpose` of `At.tensor` followed by realized source
  evaluation from `podCommonClosed`. It is not a separately chosen map. `At.hom_isIso` states
  invertibility in the ambient unbounded derived module category. `HomLaws.naturality`
  quantifies over every morphism of permitted pairs, contravariantly in M and covariantly in N;
  in particular it includes the prescribed finite-field comparison isomorphisms.
  `HomLaws.evaluation` is the module-evaluation square. `HomLaws.transpose` expresses the
  corresponding identity for every test object and every tensor-to-N arrow. No perfectness
  assumption is imposed on a Hom pair.
* `Family.ring` quantifies over arbitrary isomorphisms of the underlying schemes. They need not
  be morphisms in `Over (Spec k)`. `RingReindex.functions` fixes the coefficient comparison
  pointwise on actual native continuous functions. `modulePull` is the existing sectionwise
  inverse image with its module action transported through this ring isomorphism; exactness is
  inherited from the recorded theorem. `derivedPull` is its actual exact-derived functor.
* `IntegralReindex.balance` and `sections` fix scalar/reindexing comparison on every balanced
  pure section. `derived` and `representative` fix its derived version through the same universal
  cochain counits. `Family.comparison` is the natural realization/pullback isomorphism;
  `integral_normalization` identifies its component on every integral representative with this
  exact base-change map and `podCompletedToTowerIso`, through the unfoldable predicate
  `integralRealizationAgreement`. The scalar and tensor representative equations are likewise
  named predicates, rather than local let-bindings in theorem signatures.
* `moduleId_sections` and `moduleComp_sections` specify identity on sections before deriving;
  HEq retains the actual site-object transports. `Family.identity` uses the derived ordinary
  identity comparison, and `composition` uses the derived ordinary composition comparison and
  the published `pullbackTensorCommonComposition`. Thus these are equations for the actual
  identity/composition maps, not existence of unrelated isomorphisms.
* `ReindexTensor.pure` specifies homogeneous tensor sections, `representative` specifies the
  derived map on K-flat representatives, and `unit_sections` specifies the coefficient map in
  degree zero. `pullUnit` derives that very unit map. `Family.tensor_compatibility` and
  `unit_compatibility` are the tensor and unit squares. The source unit in the latter is the
  unique one characterized by its recorded unit laws (`unit_spec`). `pullHom` is the ordinary
  evaluation transpose. `Family.hom_compatibility` is its square with the published
  `podCommonHomComparison` and the above realization Hom maps. Together with `At.symmetric`
  and the signed model, these give the symmetry, tensor, Hom and coefficient compatibility.
  Arbitrary scheme isomorphisms include semilinear geometric Frobenius and all its iterates;
  no k-linearity restriction silently discards that case.

Dependency declarations used:

* `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`.
* `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic` and
  `Sheaf.Paper.CompletedCondensedCoefficients`: the native condensed algebraic-closure ring and
  its continuous finite-field/colimit presentations. The ordinary ring is the section ring of
  the native object, as fixed by the following existing realization module.
* `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization`:
  `LocallyFiniteAdicRealization.Realization`, `ringSheaf`, `sections`,
  `CoefficientPresentation.integralMap`, its integral and common-field normalizations.
* `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`.
* Mathlib `DerivedCategory.Basic` and
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: the existing
  derived category and exact-functor, cochain factorization, natural-isomorphism, identity
  and composition constructions.
* `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: the recorded source pair category,
  `inclusion`, `stageSystem`, `unitor`, and the coefficient size models/inclusions.
* `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory` and localization.
* `Sheaf.Paper.DerivedPullbackTensorHom` and `DerivedPullbackTensorIso`: the actual source
  pullback/tensor/Hom, the common-stage tensor comparison, associators, units, braiding and
  pullback composition; `rationalDerivedTensor_existsUnique` supplies its literal object formula.
* `Sheaf.Paper.DerivedAutomorphismHomEvaluation`: `podCommonClosed`,
  `podCompletedModuleInverseImage`, `podCompletedDerivedInverseImage`,
  `podCompletedToTowerIso`, `podCommonPairs_pullback`, `podCommonHomComparison`.
* `Sheaf.Paper.RationalRealizationTensorComparison`:
  `ConstructibleTensorCompletionPresentation` with all four normalization clauses.
* `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`:
  `CoefficientClosedStructure`, `CoefficientTensorModels`, `RingedDerivedTensorCoherence`,
  the coefficient unit complex/sections and the existing ambient `derivedInternalHomOfUniverses`.
* `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `isoSectionwiseInverseImage`, `isoSectionwiseModuleInverseImage` and its exactness theorem.
  No competing site, coefficient, module, tensor, or derived-category instance is installed.

Source and edge checks: read BS 6.8.8/6.8.14/6.8.15 and HRS 5.2/7.7/7.9 in the supplied
local PDFs, together with the live node and all its statement-dependency records/signatures.
The empty scheme and zero complexes are included: no nonemptiness or positive rank appears.
The unit is the coefficient sheaf in degree zero. E=F, repeated fields, coefficient towers,
ramified finite extensions, zero Hom source/target/test object and arbitrary common-stage arrows
are included in the quantified formulas. The Hom qualification is constructibility, not
site-perfectness. Arbitrary underlying-scheme identity/composition and non-k-linear isomorphisms
are included. Site objects remain in u+1 and site morphisms in u; coefficients/modules are u+1.
No equality between these two site universes is introduced.

Searches for an existing statement:

* msearch LeanFinder, “Exact symmetric monoidal realization of common finite field constructible
  adic coefficients as ordinary derived modules preserving internal Hom evaluation”: eight
  condensed/LightCondensed hits, none this comparison.
* msearch Loogle, `"DerivedCategory", "MonoidalClosed"`: zero hits.
* msearch grep, `constructible.*[Rr]ealization|[Aa]dic.*[Ee]quivalence`: nine unrelated hits
  (quadratic radicals, local cohomology, monads and adic valuations).
* msearch LeanSearch, “Common stage constructible adic derived sheaves equivalence with derived
  modules preserving tensor internal Hom and evaluation”: eight general sheaf-module,
  completion and LightCondensed monoidal hits, none the theorem.
* rg on `lean/WeilConjectures` and `lean/Sheaf`, including the item id: found the existing
  locally finite realization, finite tensor comparison, source operations and isomorphism
  Hom/evaluation interfaces above, but no existing combined normalized theorem. The existing
  locally finite realization has no tensor, Hom or isomorphism normalization, as also recorded
  in the live maintainer review of the stage-1 split. It is reused, not duplicated.

Validation used only scompile.py against the live server build. Every delivered module
compiled separately in dependency order: the inclusion helper 9.8 s, native realization data
48.4 s, ordinary reindexing data 42.9 s, and the final realization theorem module 17.0 s.
The prefix probes also compiled and have been removed. No compiler errors or warnings remain.
No global build or direct edit of a shared source was run. The final delivery dry run follows.
Both named theorems remain `sorry`, as required for stage 2; each has its matching DAG statement and complete natural-language proof docstring.

## Earlier second reading by NL

A separate second pass through the source statement, all conclusion structures and all
normalization equations checks the hypotheses and clauses listed above. This worker was
explicitly instructed not to start other agents, so this is a fresh second reading by the same
worker, not a claimed independent review. The maintainer's delivery review is independent.
The pass resolved expensive implicit localization-object transports by giving the canonical
isomorphisms explicit endpoint types. It also moved local theorem-signature abbreviations
into unfoldable definition bodies and separated comparison data from laws. No source clause
was changed. The pass checks tensorator directions, all three associativity objects, both unitors, the
contravariant Hom component, the source evaluation transpose, and both routes of isomorphism
composition. The common-stage source, native continuous target and ambient Hom are retained.

## New nodes

`def-sf-common-stage-inclusion-tensor-comparison` defines the finite-stage inclusion
tensorator needed to state `FiniteNormalization.integral_tensor`. Its own module is
`Sheaf.Paper.CommonStageInclusionTensorComparison`. It uses the existing common-stage
tensor comparison at E (E∨E≤E) and the normalized reflexive scalar unit on the two inputs;
the inverse of that specified composite is the inclusion tensorator. The existence/uniqueness
statement fixes the entire isomorphism by HEq, retaining literal-object transports. Choosing
its unique witness therefore does not introduce arbitrary map data. The theorem's docstring
gives the direct construction and uniqueness argument. Source: BS Remark 6.8.15 and the
recorded raw common-stage tensor convention. This helper is not a proof of the realization
or any of its claimed tensor/Hom compatibility properties.

Searches: LeanSearch on inclusion of a finite field stage preserving derived tensor with
normalized scalar unit returned eight general filtered-category/module/ring tensor results,
none this map. Loogle `"Functor", "MonoidalCategory", "IsFiltered"` returned zero hits;
Mathlib grep `[Ss]tage.*[Tt]ensor|[Tt]ensor.*[Ss]tage` returned zero. Project rg for
`tensorInclusion|inclusionTensor|stageTensor` found only a private total-tensor summand cast,
an external Hom summand inclusion, and abstract `CommonTensorComparisonDescent.stageTensor`
data requiring an unrelated already monoidal system. Those do not supply this actual raw
common-stage inclusion. DAG search found unrelated system/operadic/duality comparisons;
`blueprint_refs.py search 'common-stage inclusion tensor'` returned zero matches. The node
records those searches and their original queries.

The item's `stmt_deps` records definition ownership of the reused native realization,
ambient ringed closed structure, tensor-completion presentation, evaluation/pullback calculus
and sectionwise module inverse image. The repair below replaces the previous theorem-node
additions with their definition owners. No source statement or proof plan changes.

`def-sf-native-adic-realization-data` owns the native section-module presentation,
`At`, the exact evaluation-transpose map and Hom laws. Module: `Sheaf.Paper.NativeAdicRealizationData`. It is a definition of
comparison data, with no existence asserted and no postponed theorem. The finite tensor
agreement is an HEq of the given tensorator with the specified canonical composite, retaining
the literal-object transports. Its closed tensor and Hom coherence clauses are detailed above; finite integral
normalization is owned by the separate node below. Source: BS 6.8.8/6.8.14/6.8.15 and HRS 7.9.

`def-sf-native-adic-reindexing-data` owns `RingReindex`, the actual exact ordinary
inverse-image functor and its derived version, the scalar base-change data, the pure-section
and derived scalar representative equations. Tensor/unit/Hom reindexing is owned by the
separate node below. Module: `Sheaf.Paper.NativeAdicReindexingData`. It asserts no existence. Source:
BS 6.8.15, HRS 7.9 and Stacks 07A4/0GMX.

For both data nodes the LeanSearch query on canonical tensor/Hom realization data with
balanced normalization and scheme-isomorphism coherence returned eight general closed-category
and adic-completion hits. LeanFinder on normalized monoidal adic realization and arbitrary
scheme isomorphisms returned eight scheme normalization/affine-limit hits. Mathlib grep on
realization tensor or adic isomorphism returned 25 unrelated completion and monadicity hits.
DAG/project searches and the recorded declarations were read. In particular
`def-sf-integral-tensor-comparison-system` uses perfect-valued D(R_E),
`def-sf-integral-open-reduction-comparison-data` concerns completed open-extension systems,
and `def-coef-semilinear-geometry-derived` concerns a strict coefficient tower. None supplies
these native continuous coefficient realization/reindexing data. Their underlying existing
operations are reused. The node records contain the queries and search results.


`def-sf-native-adic-finite-normalization` owns `coefficientMap`, `integralComplex`,
`finiteTensorAgreement` and `FiniteNormalization` in
`Sheaf.Paper.NativeAdicFiniteNormalization`. It gives the exact finite integral normalization
already described clause by clause above, including every pure-section and K-flat representative
equation, and makes no existence assertion. Source: BS 6.8.14--6.8.15, HRS 7.9. It is split
from the native tensor data for the 60-second compile limit, without changing its meaning.

`def-sf-native-adic-tensor-reindexing` owns `reindexTensorRepresentative`, `ReindexTensor`,
`pullUnit` and `pullHom` in `Sheaf.Paper.NativeAdicTensorReindexing`. It gives exactly the
ordinary cochain and derived tensor, unit-section and evaluation-transpose maps described above,
with every normalization retained. Source: BS 6.8.15, HRS 7.9, Stacks 07A4/0GMX. This is the
tensor/unit/Hom part split off from scalar module reindexing for the per-file limit.

For these two packages, LeanSearch on balanced finite integral normalization and continuous
adic realization returned eight general free-monoidal normalization, finite measure and
Noetherian adic-completion tensor hits; none supplies this data. Loogle on Functor and IsKFlat
returned zero. Mathlib grep for finite normalization or tensor reindexing found five
Zariski-main-theorem scheme-normalization lines. DAG/project searches for these data names
found no owner; broad matches concern other strict coefficient, Galois and projection data.
The new nodes preserve these queries/results. They introduce no competing operation.

The first dry run found metadata errors (grouped bracket citations, a named-argument delimiter
mistaken for the end of a signature, and docstring prose mistaken for declarations). All were
repaired. A subsequent run exceeded the fixed 60-second compile limit under server load;
the two definition-only splits above preserve all equations and reduce each file's work.

Resumed validation: confirmed the stage-1 PASS has no Lean record and is not a stage-2 delivery. The first resumed dry run hit the fixed compile timeout in tensor reindexing. Moved its pure-section and unit-section equations into named predicates in the same owning module, preserving every quantifier and equation while reducing generated structure terms. No new mathematical assumption or node was introduced by this repair.

Final resumed validation: the six-file dry run passed server compilation and preflight
(commit 32f9045c8fd, nothing pushed). Integral reindexing now uses the named predicate
`integralReindexSections`; tensor reindexing uses `reindexTensorPure` and
`reindexUnitSections`. These predicates retain the original section equations verbatim,
reduce generated dependent structure terms, and are listed in their owning nodes'
`lean.declarations`. All six files compiled separately within the unchanged 60-second
limit, with no errors or unexpected warnings. The main node differs from the current
reviewed split only in `lean` and the authorized added statement dependencies.



`def-sf-locally-finite-adic-realization-data` records the ten existing native coefficient,
section-ring, section-module, coefficient-presentation and normalized realization-data
definitions in `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization`. In particular its
main declaration is `WeilConjectures.LocallyFiniteAdicRealization.Realization`; its statement
specifies the integral and common-field equations, without asserting existence. Source:
BS 6.8.3, 6.8.8, 6.8.14--6.8.15.

`def-sf-constructible-tensor-completion-presentation` records the existing two definitions
`ConstructibleTensorCompletionNormalized` and `ConstructibleTensorCompletionPresentation`
in `Sheaf.Paper.RationalRealizationTensorComparison`. All four quotient-section, zero
shifted-coordinate, model descent, and constructible completeness/invertibility clauses
are retained. Source: BS 6.5.5 and 3.4.10. Its statement is a definition of normalized
data, not the tensor-comparison theorem.

`def-sf-proetale-sectionwise-module-inverse-image` records the existing sectionwise sheaf,
constant-coefficient and module inverse-image definitions in
`Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`. Its main signature keeps
the scheme universe t, coefficient universe max r (t+1), arbitrary given coefficient
isomorphism c, and transported action via inv c. Source: Stacks 09A5/00WX/03D2. Equivalence
and exactness remain properties of the existing functor, not additional data assumed here.

`def-sf-adic-closed-reindexing-maps` records the existing partial closed/evaluation and
common-field transpose maps, completed coefficient limit lift, completed module and
derived pullback, and completion-unit comparison to tower pullback in
`Sheaf.Paper.DerivedAutomorphismHomEvaluation`. The source common-field evaluation is
normalized at every finite stage; the completed ring map is the actual lift of all
finite coefficient projections. Source: Stacks 0GMX/08J9 and the existing node's completed
and common-field formulas, steps 1, 8 and 15--16. No arbitrary substitute map was introduced.

Searches for these four owners: LeanSearch query "Data for normalized native adic
realization coefficient presentations tensor completion and sectionwise module inverse
image" returned eight AdicCompletion algebra/tensor results, none these site data.
LeanFinder query "Normalized continuous adic coefficient realization and module inverse
image from scheme isomorphisms" returned eight scheme-normalization results, none these
data. Mathlib grep of the four declaration families returned zero. Project/DAG rg finds
the published definitions and only their theorem-node owners; the trace point-restriction
coordinate node consumes inverse image but does not own it. Blueprint searches "native
realization", "tensor completion presentation", "sectionwise inverse image" each returned
zero. These exact queries and results are recorded in all four nodes; the correct result
is reuse of existing definitions, not an unsuccessful search followed by new Lean code.


## Returned-delivery repair (2026-10-23)

Compared the retained packet with the live shared item: only `lean` and authorized
`stmt_deps` additions differ; its reviewed statement and proof plan remain byte-identical.
The mandatory initial saved-packet dry run passed at e30c8f6cc97. That mechanical pass
predated the two mathematical/ownership repairs below and was not treated as their review.

H2 (immutable returned head 07059192980c): removed the five theorem-node additions from
`stmt_deps` of the item and the newly owned data nodes. Use the already landed
`def-zl-ringed-derived-closed-symmetric-monoidal-data` for `RingedDerivedTensorCoherence`.
The four additional existing-definition records below own the other reused notions.
They have `existing: true`, reference unchanged published modules, and create no second
Lean declaration. All original live statement dependencies remain. The added definitions
are cited by the item and the relevant new data nodes; each new node's bracket citations
match its dependency list. The existence theorems of the four source modules have not
been added as hypotheses or statement dependencies.

H3: added `Family.sourceId_unit`. Write F for common-stage pullback by id and c for the
published `pullbackTensorCommonComposition id id`. For every actual common-stage object M,
the new field requires `c(M).hom ≫ sourceId.app (F.obj M) = 𝟙 (F.obj M)`, expressed by HEq
to retain the actual source-object transport along id ≫ id = id. Thus sourceId is a unit
for the already fixed composition map, not a free natural automorphism adjusted to the
realization comparison. The existing `Family.identity` still uses that same sourceId and
the section-normalized, derived `moduleId`; both conditions are required simultaneously.
The comparison isomorphism cannot define sourceId merely by full faithfulness anymore.
For the canonical pseudofunctor identity this is the ordinary unit coherence equation;
F is equivalent to identity and hence essentially surjective, so the equation determines
the natural identity comparison on all objects. No new identity existence theorem or
choice from the published bare `Nonempty` identity statement was introduced.

Read the actual common-stage composition representative formula and its unique
normalization in DerivedPullbackTensorIso.lean, and the published identity theorem in
CommonStagePullbackIdentity.lean. Read BS Remark 6.8.15 from the local paper: isomorphism
inverse image is naive inverse image, whose sectionwise identity/composition maps give
this unit coherence. The correction is to the Lean rendering of the existing clause
about specified identity/composition maps, not to the natural-language node statement.

Edge checks repeated for this repair: M=0 and the empty scheme still occur; no nonzero
object or nonempty site is assumed. The unit equation includes every coefficient stage,
including repeated/identity fields and raw rational objects. All universes and arbitrary
underlying-scheme isomorphism quantifiers are unchanged. No theorem was proved.

## Second reading by NL

Re-read the H2 ownership edges, all four new nodes and their verbatim source signatures.
All four source declarations exist unchanged and each new `lean.statement` is a literal
substring of its source module. Read their complete defining data/formulas, not only the
names. The ambient coherence owner already exists and is reused. Checked each hypothesis
and conclusion of the parent against the retained clause map above; the only mathematical
change is the missing identity normalization. Read `Family.sourceId`, new
`sourceId_unit`, `identity` and `composition` together: the unit law pins the same sourceId
used by identity against the same composition used by composition. Its direction is
F(M) → F(F(M)) → F(M), with the first domain transported from pullback by id ≫ id;
the right side is the identity on F(M), not on M. This uses no realization map and hence
cannot be satisfied by changing sourceId to absorb a failure of realization identity.
All other accepted clauses are retained verbatim. This is a same-worker second reading;
no sub-agents were started.

Validation after repair: scompile.py compiled all six delivered Lean files, including
AdicQbarConstructibleRealization.lean with the new unit field, successfully with no
errors or unexpected warnings. Compilation and delivery use only the authorized wrappers;
no shared source was edited and no Git command was run by this worker.

The repaired dry run compiled all files and found only duplicate report headings: the
preflight read the first New nodes section and missed the four entries in the second.
Consolidated all new-node descriptions into one New nodes section and repeated the dry run.
