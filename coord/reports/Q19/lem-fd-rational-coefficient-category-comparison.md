## Worker report

Item: `lem-fd-rational-coefficient-category-comparison`; group Q19; stage 2.
The node statement and proof are unchanged; its statement dependencies gain the three
new definition nodes described below. The delivery states the comparison
as one existential theorem, with named data structures spelling out its canonical maps and
normalizations. These structures package this node's conclusion; they do not replace any
coefficient category, scalar functor, pullback, realization, or Weil-pair definition.
Only the final theorem has `sorry`. All adapter definitions have actual data.

### Hypotheses and clauses

* The global datum is `(D : FiniteFieldDatum.{u})`; `[Fact l.Prime]` and
  `(hl : l ≠ D.p)` give precisely the coefficient prime condition. `Ω : Type w`,
  `[Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]` allow an algebraic closure
  independently of the scheme universe. No embedding of a general scheme in the finite
  field datum is assumed.
* The scheme quantifier is `FdCoefficientComparisonSystem.coefficients`: every
  `T : Scheme.{u}` with `[IsNoetherian T]`,
  `[Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]`, and
  `[Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]`. These are the PBC dependency's
  recorded finite-dimensionality and local invertibility hypotheses. `fdResidueInvertible`
  derives the framework residue-field inverses from stalk invertibility, rather than
  adding a new assumption.
* Finite fields are `Padic.FiniteCoefficientFields l Ω`. The finite-stage structures
  use its recorded `pbcFiniteField.{u}` small model consistently. It and the framework's
  `Coefficient.{u}` present the same subfield through the standard `Shrink` equivalence;
  heterogeneous equalities explicitly identify functors and representatives where their
  recorded typeclass presentations differ. There is no assumption equating universes.
* `FdRationalStageComparison.integral` is the equivalence of the recorded full integral
  categories. `integral_identity` identifies its underlying functor with
  `integralDetailedTransport`, whose coefficient isomorphism is fixed on every finite
  quotient. This implements identity in the common ambient category, including the
  existing coefficient-size transport rather than an arbitrary ring equivalence.
* `rational` has exactly the two raw rationalization categories as endpoints. `objects`
  gives the unchanged integral-object formula. `tensors` sends every localized pure
  tensor to the same integral arrow and scalar, through `sfRationalCoefficientEquiv`
  and `pbcRationalCoefficientEquiv`. The generic `fdRawTensor` and `fdRawScale` only
  expose the existing localization's tensor and scalar operations with their actual
  module instances. Additivity plus the tensor formula gives E-linearity; `shift`,
  `exact`, `inverse_exact`, and `inverse_triangles` retain exactness in both directions.
  `integral_shift_normalization` fixes the integral shift to the canonical exact
  scalar-restriction shift, and `shift_normalization` fixes its localized rational
  image. `finite_shift_normalization` and `pair_shift_finite` fix the family and
  common-pair shift components to these finite maps.
* `FdCoefficientComparison.family` is a `StageSystem.Morphism` between the actual two
  recorded scalar systems. `finite_functor` fixes its finite functors to the preceding
  equivalences. Its `β h` has direction J_E then PBC transition to SF transition then
  J_L; thus the node's j is its inverse. `family.coh` is the specified scalar cocycle,
  with the recorded associators, for all inclusions, including repeated fields. The
  identity cases of this equation give the normalized unit equation by cancellation.
  `scalar_shift` states compatibility with the recorded transition shifts.
* `ordinary` fixes the scalar transport on every sheafified tensor generator, including
  the inverse completed-ring comparison on the coefficient. Its `complex` adapter is
  the actual complex functor composition comparison; `completion` composes its inverse
  with `completedScalarChainComparison`. Hence its finite quotient coordinates are the
  specified quotient maps and its shifted-product coordinate is zero.
  `integral_scalar` and `integral_scalar_lift` restrict that comparison to the integral
  categories and fix `family.β` on their localizations. `chi` is the derived localization
  equation with both canonical complex-localization factors and `pbcComplexCounit`.
  Consequently β is chi in the direction ordinary PBC to completed SF, and j is its
  inverse, rather than a freely chosen scalar natural isomorphism.
* `equivalence` has the actual framework and PBC common-stage pair categories as its
  endpoints, with `pair_functor = family.functor`. The latter's definition sends
  `(E,K)` to `(E,Φ_E K)` and sends a representative to β_source, then Φ_L of the map,
  then β_target inverse. These are exactly conjugation by the node's j maps.
  Its formula on all representatives fixes the induced Hom-colimit identification;
  the identity case gives compatibility with the recorded finite-stage inclusions.
  `pair_shift`, `pair_exact`, `pair_inverse_shift`, `pair_inverse_exact` and
  `pair_additive` retain the actual common-stage triangulations. `scalar` states
  Ω-linearity on every finite representative after placing the scalar in a common
  field, using the existing PBC Ω-action. No Karoubi category is introduced.
* `FdPullbackChain` compares ordinary PBC pullback to the framework's actual whole
  strict-tower Roos complex. `quotients` prescribes every degree, every n, every
  base-changed pro-etale object, and every generator by the actual inverse-image unit
  and finite reduction unit. `shifted` prescribes zero on the shifted product. Thus
  this is a whole-chain normalization, not an arbitrary derived isomorphism or an
  assertion of unrelated levelwise reduction equivalences.
* `FdPullbackComparison` contains the integral comparison and its ambient lift.
  `normalization` uses the PBC completion unit, the framework good-complex realization,
  the two complex-localization factors, the PBC pullback counit, and the specified
  chain map. This is the identity on the common strict finite-reduction tower.
  `rationalization` fixes the finite rational comparison on every integral object.
* `FdPullbackSystem` uses the actual PBC completed pullback family; `sfFinite`, `sfBeta`,
  and `sfPair` identify its framework counterpart with the recorded rational pullback,
  recorded scalar comparison, and recorded common-stage pullback. `mixed` is a
  `StageSystem.Morphism.Hom`; its `comm` field is the mixed scalar square. Its components
  are the finite comparison by `mixed_components`. `pair_components` fixes the common
  natural isomorphism on every literal pair to the finite-stage inclusion of that map.
* All these comparisons are supplied simultaneously by `FdCoefficientComparisonSystem`.
  Its `realization` and `realization_coherent` retain the recorded
  `IntegralComparisonSystem` with every
  `IntegralComparisonRealizationCoherence` normalization. `FdComparisonSchemeCoherence`
  fixes the framework identity and composition isomorphisms to
  `integralComparisonUnit` and `integralComparisonComposition` and states the comparison
  squares with their PBC counterparts. Separate normalization clauses identify the
  target unit and composition with `pbcActualCompletedPullIdIso.hom` and
  `pbcActualCompletedPullCompIso.inv` on the underlying complete objects. Thus no
  arbitrary target unit or composition is allowed.
  Its last clause identifies the framework scalar/pullback comparison with
  `integralComparisonScalar` from the same whole-diagram realization. No k-linearity
  is imposed on a scheme isomorphism.
* The final quantifier is every `X₀ : Over (Spec (.of D.k₀))` with
  `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]`.
  `FdFrobeniusComparison` supplies, as conclusions, the necessary noetherian,
  dimension and invertibility instances for `D.geometricFiber X₀`. Its `common`
  and `finite` fields are equivalences of the recorded `sfCommonStageWeilComplex`
  and `sfWeilComplex` with `Endofunctor.IsoAlgebra` for the actual PBC Frobenius
  pullbacks. `common_functor` and `finite_functors` fix them to
  `IsoAlgebra.mapOfNatIso` of the preceding comparison. That functor sends the
  structure isomorphism to β_K followed by J(theta), and sends the intertwiner to
  J of its underlying map. Thus both pair structures and intertwining morphisms
  are specified, compatibly with the finite/common comparison.

### Dependencies read and used

The recorded declaration, signature and docstring were read for every statement dependency.
For dependency modules with several declarations, the actual relevant companions are used:

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, `geometricFiber`.
* `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `AlgebraicGeometry.Scheme.integralDetailedCoefficientComparison`,
  `integralDetailedCoefficientRestriction_exact`, `integralDetailedTransport`,
  `integralStratifiedPerfectDetailed`, `integralStratifiedPerfectClosure`.
* `Sheaf.Paper.SfRationalizationKaroubi`:
  `WeilConjectures.sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalCoefficientEquiv`,
  `sfRationalScalarExtension`.
* `Sheaf.Paper.PbcRationalCategory`:
  `AlgebraicGeometry.Scheme.PbcRationalDerivedCategory`, `PbcRationalCategory`,
  `pbcRationalization`; the recorded finite-stage specializations are reused.
* `Sheaf.Paper.PbcScalarExtension`: `pbcCoherentScalarExtension` and its recorded
  scalar maps, tensor sections, derived tensor/counit and normalized associators.
* `Sheaf.Paper.FiniteFreeCompletedScalarComparison`:
  `WeilConjectures.completedScalarTensorSection`, `completedScalarChainComparison`,
  `finiteFreeCompletedScalarComparison`.
* `Sheaf.Paper.SfScalarExtensionComposition`:
  `WeilConjectures.sfIntegralOrdinaryComparison`, `sfIntegralScalarComp`,
  `sfRationalScalarComp`, including the recorded unit/coherence normalization.
* `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory`,
  `GeneralAlgebraicallyClosedCoefficients.Stage`, `stageSystem`, `inclusion`,
  `ofHom`, `homCoordinates` and its common-stage triangulation.
* `Sheaf.Paper.PbcQbarCategory`:
  `AlgebraicGeometry.Scheme.pbcQbarCategory`, its Ω-action and finite-stage inclusions.
* `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback`,
  `rationalDerivedPullback`, `commonStageDerivedPullback`,
  `integralPullbackScalarComparison`, `rationalPullbackScalarComparison`,
  `operationStageTransitionIso` (the node record lists these companions).
* `Sheaf.Paper.PbcQbarCompletedPullback`: `pbcQbarCompletedPull`,
  `pbcQbarPullFamily`, `pbcQbarIntegralPull_mem`, together with their actual module,
  derived and completed pullback/counit/unit companions from public imports.
* `Sheaf.Paper.IntegralPullbackComparisonRealization`:
  `WeilConjectures.IntegralComparisonSystem`,
  `IntegralComparisonRealizationCoherence`, `integralComparisonUnit`,
  `integralComparisonComposition`, `integralComparisonScalar`,
  `integralPullbackComparisonRealization`.
* `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `WeilConjectures.FiniteFieldDatum.geometricFrobenius`.
* `Sheaf.Paper.SfWeilSheafComplex`: `WeilConjectures.sfWeilComplex`,
  `sfCommonStageWeilComplex`.
* Mathlib `AlgebraicGeometry.IsProper`/`IsSeparated` in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`, and
  `LocallyOfFiniteType`/`QuasiCompact` in the finite-type modules: separation and
  finite type are precisely the classes required of the structure morphism.

The stated proof-dependency modules are imported for the eleven-step postponed proof,
including scalar-localization triangulation, finite-stage pair calculus/common-stage
cones, Roos comparison, exact pro-etale countable products, K-injective resolutions,
K-flat resolutions, constructibility preservation, and resolution independence.
The existing finite-type noetherian and finite-dimension lemmas handle the Frobenius
specialization; no new versions are asserted.

### Edge cases

Checked against the node before writing and against the typed interfaces:
empty T and the empty geometric fiber (dimension may be bottom); zero and
uniformizer-torsion integral objects; degree zero and arbitrary negative cochain
indices; n = 0 in the quotient tower; E = L = M and identity coefficient embeddings;
identity and composite scheme isomorphisms; arbitrary common overfields and eventual
representative equality; X₀ = Spec k₀; finite fields in a larger-universe algebraic
closure; geometric Frobenius as a scheme automorphism without a k-linear assumption.
The prime inequality is retained, and no nonemptiness or positive-dimension assumption
was added. All diagrams quantify over actual chain maps and transition data.

### Searches and source

Read the current blueprint's
`literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-def-trace/def-fd-trace-function.md`,
including its final sentence specifying the PBC coefficient category.
Searched the named read-only upstream and side-project sources; no existing theorem
states this two-system comparison with its scalar, pullback and fixed-pair normalizations.

`msearch.py Q19 lem-fd-rational-coefficient-category-comparison` searches:

* `leanfinder`: "Equivalence between rational constructible coefficient categories
  compatible with scalar extension and pullback" — eight unrelated general equivalences,
  no exact match.
* `loogle`: "CategoryTheory.Equivalence, Functor.Linear" — no match (the latter is
  not the qualified declaration name in this interface).
* `grep`: "Rational.*Comparison|Coefficient.*Comparison", CategoryTheory — no match.
* `leansearch`: "canonical equivalence between rational constructible derived categories
  compatible with scalar extension and pullback" — generic module/derived-category
  equivalences, no comparison of these recorded coefficient systems.

Also used `rg` in `WeilConjectures` and `lean/Sheaf` for rational/coefficient comparison,
scalar localization, scalar/pullback comparison and the exact owning declaration names;
and searched the node id in upstream. Read the located dependencies rather than creating
new copies. No existing declaration packages the required comparison data;
all recorded dependency interfaces themselves are usable.
There are no dependency repairs, statement corrections or disputed statements.

### Validation

All compilation uses the prescribed `scompile.py` wrapper and the published library.
The final delivery is checked by `deliver2.py --no-push` and then delivered by
`deliver2.py`; the final tool result supplies its immutable commit.

## New nodes

`def-fd-coefficient-comparison-datum` defines the coherent coefficient comparison data
on an allowed scheme: the integral and raw rational equivalences, canonical tensor
formula, canonical shift comparisons, the generator- and chi-normalized scalar
comparisons, their actual scalar-system cocycle, and the exact common-stage equivalence
with its representative scalar formula. Its module is
`Sheaf.Paper.FdCoefficientComparison`; the primary declaration is
`WeilConjectures.FdCoefficientComparison`. This is a definition of the data whose
existence the owning theorem asserts, and asserts no existence itself. Its source is
the trace-definition final sentence's interpretation in the two recorded coefficient
systems. The searches below found no existing definition of this comparison datum;
all component categories and operations are the dependency declarations already named
above. The data do not turn the desired equivalence into an assumption: the final
existential theorem supplies them.

`def-fd-pullback-comparison-datum` defines simultaneous coefficient/pullback data, adding
the normalized whole-tower chain map, finite rational and common-stage pullback
comparisons, the mixed scalar square, and the recorded integral realization system.
Its module is `Sheaf.Paper.FdCoefficientComparisonSystem`; the primary declaration
is `WeilConjectures.FdCoefficientComparisonSystem`. It uses the first new definition
and the recorded framework/PBC operations and realization. Its source is the same
trace-definition final sentence, as specified in the owning comparison node's whole-
tower clause. Identity/composition compatibility of the inter-system comparisons is
retained in the main theorem through `FdComparisonSchemeCoherence`, not assumed as
an unstated fact. Its datum also asserts no existence.

For both new notions, the additional searches were: `blueprint_refs.py search`
"coefficient comparison datum" and "pullback comparison datum" (zero blueprint nodes),
`rg` of the DAG and the two specified Lean source trees for comparison datum/data and
the exact declaration names, `msearch.py grep`
"(Coefficient|Pullback).*Comparison.*(Data|Datum|System)" in CategoryTheory (zero hits),
`msearch.py leansearch` "A coherent datum of finite rational coefficient equivalences
with normalized scalar comparisons and common-stage equivalence" (eight generic
linear-algebra hits), and `msearch.py leanfinder` "Coherent comparison datum for
rational constructible coefficient systems with scalar cocycle and canonical pullback
tower comparison" (eight affine-limit/pullback-cocycle hits). None packages these two
coefficient systems or supplies these normalizations. The exact result declaration
names and queries are recorded in each new node's `mathlib_searches`. A broad whole-DAG comparison-data search also found unrelated affine, Cech,
six-functor and condensed comparisons; the coherent-pullback, condensed-coefficient,
and ambient-complete-raw-scalar-system definition nodes were read and define other
data, not this comparison of the two presentations. The recorded
blueprint ancestor is `def-fd-trace-function`, with the owning comparison in `via`.
Each definition has its own module/node; each file is checked independently under the
unchanged 60-second file limit.

`def-fd-finite-pullback-comparison-datum` defines the finite-stage portion of the
pullback data: the canonical chain map, its entire quotient and shifted-coordinate
normalization, its integral ambient lift with the actual completion unit and derived
counits, and its specified raw rationalization. The primary declaration is
`WeilConjectures.FdPullbackComparison`, in `Sheaf.Paper.FdPullbackComparison`.
The simultaneous-system definition now refers to this finite datum explicitly.
This is a definition of the finite comparison data already required by the source,
not an assertion of existence and not a replacement pullback. Its recorded searches
include all the comparison searches above, a zero-hit blueprint search for "finite
pullback comparison datum", and an additional LeanSearch for a datum of an integral
and rational constructible pullback comparison fixed by a whole reduction tower and
derived counits. The eight hits were generic categorical pullback comparisons,
derived counits and constructible-set data, not this datum. The definition has its
own module and node so that its canonical-chain specification and the simultaneous
common-stage specification are independently checkable.

## Resumed packet self-check

Read all four saved modules against the unchanged item and the three definition
nodes, and rechecked their signature records, JSON formatting, explicit binders,
source annotations, and single final postponed theorem. The first dry run confirmed
a 60-second timeout in `FdPullbackComparison`. A scratch profile showed substantial
time generating auxiliary `SizeOf` and constructor lemmas (including 9.5 seconds
in `Meta.sizeOf` for `FdPullbackComparison`). Disabled `genSizeOf`, `genSizeOfSpec`,
and `genInjectivity` in the four delivery modules, following existing project
comparison-data modules. This changes only unused generated auxiliaries; every
mathematical field, definition body and theorem signature remains unchanged.
The scratch profiler and its markers are outside the delivered module tree.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
