## Worker report

The item is stated by `WeilConjectures.AdicQbarRealization.Proper.adic_proper_adjunction_realization`
in `Sheaf.Paper.AdicProperAdjunctionRealization`. The definition-only supporting records, in the two new definition modules,
spell out the ambient operations and every normalization, rather than using an arbitrary
comparison or assuming the desired mate is invertible. The theorem proof is `sorry`.
The original mathematical statement is unchanged. No projection formula is asserted.

Hypotheses and objects, clause by clause:

- `D : FiniteFieldDatum.{u}` supplies the finite field, its algebraic closure `D.k`,
  and characteristic prime `D.p`. `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p`
  are exactly the coefficient hypotheses. `PadicAlgCl l` is the specified algebraic
  closure of the l-adic rationals, with the dependency's native topology.
- `Z T : GeometricSpace D` are separated, locally finite-type and quasi-compact
  schemes over `D.k`, hence separated finite-type k-schemes. `p : Z.base ⟶ T.base`
  is a k-morphism, with the theorem's premise `IsProper p.left`. There is no
  chosen descent model over the finite field, no surjectivity or smoothness premise.
- The existential `F : Family l D` is the normalized realization family of the
  recorded adic-Qbar dependency. It provides the exact fully faithful, essentially
  surjective symmetric monoidal realizations. The native ring `ring l X R` comes
  from `LocallyFiniteAdicRealization.Realization` by its section-module equivalence,
  not from a newly invented coefficient sheaf. The bounded constructible predicate
  is `AdicQbarRealization.boundedConstructible`: its dependency identifies this
  strictly full image with bounded stratified finite-free cohomology.
- `AtSpaces` installs the recorded residue-unit and k-structure instances, not
  extra assumptions. `finiteFieldDatumPrimeUnit` supplies the integral prime-unit
  proof from `hl`. The sites are the existing small pro-etale sites, including
  their distinct object/morphism universes; module values live in `Type (u+1)`.
- `Operations.coefficient` is an actual inverse-image ring-sheaf map. Its
  `functions` equality fixes its adjunct sectionwise as precomposition by the
  base-change projection. In particular it does not assume a naive coefficient
  inverse-image isomorphism.
- `ContinuousRational.modulePull` and `.derivedPull` are the published balanced
  inverse image and ordinary derived inverse image. `DirectImage.modulePush` and
  `.derivedPush` are the published actual module pushforward and its ordinary
  unbounded right derived functor. `Operations.unit_sections`, `pull_normalized`
  and `transpose` specify the canonical ordinary and derived adjunctions using
  insertion of one, the actual left-derived counit, and the right-derived unit.
- `Comparison.pull_preserves` and `.push_preserves` assert preservation of the
  specified full bounded constructible subcategories, for all ambient objects
  satisfying that predicate. They do not assume preservation as an input.
- `Comparison.a` has exactly the orientation rho_Z Lp* → Lp_B* rho_Y. Its
  `integral_normalization`, through `IntegralAgreement`, gives the formula on
  every finite integral constructible representative, with the raw-localization
  object transports, the recorded realization integral comparison, inverse of
  the actual completion unit, and balanced scalar comparison, in that order.
  `IntegralComparison.sections` fixes the balancing map on local generators;
  `.representative` fixes its derived map using the actual computation counits;
  `.completion_hom` requires the published quotient-tower completion map.
- `TensorComparison.pure` fixes the ordinary tensor comparison on homogeneous
  generators, and `.representative` fixes its derived computation on K-flat
  representatives. `.unit_sections` fixes the coefficient unit by the actual
  coefficient map; `.unit_representative` retains its actual derived counit.
  `Comparison.tensor_compatibility` is the tensor equation for a and the recorded
  `canonicalCommonStagePullbackTensor`; `.unit_compatibility` is its unit equation
  with `canonicalCommonStagePullbackTensor_unit`. These are equalities of actual
  arrows, not equality only after reduction or a choice of unrelated isomorphism.
- The source operations are exactly `commonStageDerivedPullback` and the
  universal-property extension `geometricCommonStageDirectImage` of the recorded
  finite/integral direct-image construction. `Comparison.b` is an isomorphism
  rho_Y Rp* → Rp_B* rho_Z, and `.mate` fixes its forward component to
  eta_B followed by Rp_B*(a.inv) followed by Rp_B*(rho_Z(eps)).
- `Comparison.counit` is the node's displayed equation with categorical
  composition read left-to-right. `Comparison.unit` is the corresponding
  rho_Y(eta), b at Lp*M, Rp_B*(a) composite equal to eta_B. All occur in
  ordinary ambient module derived categories. No derived Frobenius-pair category
  appears in any statement.

Dependency declarations read and used:

- `Sheaf.Paper.AdicQbarConstructibleRealization`:
  `WeilConjectures.AdicQbarRealization.adic_qbar_constructible_realization`,
  `Family`, `GeometricSpace`, `SpaceData`, `At`, `ring`, `modules`, `ordinary`,
  `boundedConstructible`, `coefficientMap`, `integralComplex`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, finite-stage `inclusion`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `commonStageDerivedPullback`, its
  existence/uniqueness specification, common-stage tensor and unit, and canonical
  tensor/unit comparisons. Rational pullback's recorded specification is used
  for the explicit representative transport.
- Mathlib proper/finite-type modules: `AlgebraicGeometry.IsProper`,
  `LocallyOfFiniteType`, `QuasiCompact`; Mathlib pro-etale site: `Scheme.ProEt`,
  `ProEt.topology`; Mathlib derived category: `DerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.Paper.ProjectionMateExact`: `SheafOfModules.ringedProjectionMateExact`
  and its actual ambient derived-adjunction convention; the statement writes
  out the needed geometric coefficient specialization, with normalization.
- `Sheaf.Paper.SfDerivedDirectImage`: `SfIntegralDirectImage` and its finite
  reduction/reconstruction helpers, retained by public import in the repair.
  `Sheaf.Paper.SfCommonStageDirectImage`: common-stage descent conventions and
  `sfModelDerivedPush` / `sfModelDerivedAdjunction` (restricted to finite-field
  models, hence the repair below for arbitrary geometric k-schemes).
- `Sheaf.Paper.ContinuousRationalDerivedRealization`: `modulePull`, `moduleUnit`,
  `derivedPull`, `IsNormalizedPullCounit`; `Sheaf.Paper.RationalDirectImageRealization`:
  `DirectImage.modulePush`, `derivedPush`, `pushUnit` (these generic definitions
  accept the native coefficient rings without a rational-field specialization).
- `Sheaf.Paper.OrdinaryCompletedIntegralPullback`: actual integral ordinary
  pullback, module adjunction, cochain counit, and ordinary/completed comparison.
- `Sheaf.Paper.DirectImagesConstructible`: `finiteFieldDatumPrimeUnit`.
- `Sheaf.Paper.BoundedConstructibleTower`: `pbcExtend`, `pbcDerivedExtend`,
  `pbcComplexCounit`, `pbcTensorSection`. The dependency tensor models and actual
  total-tensor generators are reused, not reconstructed.

Proof-dependency modules are imported for the future proof, including coefficient
realization, rational pullback/scalar coherence, whole-tower completion tensor
coherence, proper compact-support preservation, finite-Tor amplitude, normalized
ordinary scalar adjunctions, and the mate-isomorphism lemma. The main theorem's
proof docstring gives all eight steps of the DAG proof, including the whole-tower
argument rather than an inference from independent finite reductions.

Edge cases checked by reading the formulas: p=id (coefficient precomposition and
balanced multiplication become their units), empty source and empty target (no
nonemptiness premise, hence zero-category cases remain included), zero complexes
and zero local generators, tensor unit and arbitrary signed degrees, E=L and
ramified finite coefficient inclusions (no extra flatness assumption), disconnected
finite stratifications, and a proper positive-dimensional map such as P¹→Spec k.
No t-exactness of proper pushforward, naive coefficient pullback equivalence, or
projection-formula assertion is inserted. Characteristic l is correctly excluded.

Searches: the prescribed msearch wrapper ran LeanFinder for "proper pullback direct
image adjunction comparison under continuous adic coefficient realization" (eight
ordinary sheaf adjunction hits, no exact realization comparison), Loogle for
`CategoryTheory.Adjunction, CategoryTheory.mateEquiv` (twelve general mate lemmas),
and Mathlib grep for `realization.*[Aa]djunction|[Aa]djunction.*realization` (zero).
Repository rg searches for proper adjunction/realization and common-stage direct
image, and the exact blueprint id, in WeilConjectures and Sheaf found the related
interfaces listed above but no statement equal to this node. The wrapper records
are in the sandbox search log. Read the current blueprint's
`fix-lem-tensor-adjunction.proof.md`, Step 1, and BS pp. 61–62 directly: the proper
factor needs the actual counit; Remark 6.8.15 uses balanced pullback and makes no
naive inverse-image claim for general proper morphisms. No statement dispute.

## Dependency modules

`def-weil-derived-direct-image`: the recorded `SfIntegralDirectImage` is the
finite-reduction/derived-limit reconstruction, and does not itself give the
common-stage direct-image functor for arbitrary finite-type k-schemes. The existing
common-stage module only covers finite-field descent models. The dependency
module `Sheaf.Paper.GeometricCommonStageDirectImage` publicly retains these
interfaces and supplies the right adjoint and its specifying adjunction on the
actual common-stage categories. Its data are obtained from the named adjoint
existence theorem, whose universal property determines them up to the unique
adjunction-compatible isomorphism. It is not a choice from undetermined mere
existence. Its proof docstring explains the integral reconstruction, raw scalar
localization, scalar compatibility and representative-independent descent.
Only this dependency's `lean` record changes, with the required explanatory note.

## Second reading by NK

The dispatch brief forbids starting another agent and assigns the independent
review to the maintainer. This section records a fresh self-reading, without
claiming an independent worker review. Checked the coefficient map orientation,
the two raw-localization object transports, the direction of the inverse
completion map, the tensor/unit equations, the right-mate orientation, and both
adjunction identities against the node and its eight proof steps. Corrected the
missing additive structure on ordinary module pullback in the supporting record;
this is asserted as part of existence, not added as a hypothesis. The finite-field
prime-unit helper is imported from its owning module. The dependency repair
retains all formerly recorded declarations by public imports. No mathematical
statement correction or extra hypothesis was needed.

Validation: every delivered module is checked separately in dependency order by
scompile.py; the required dry run and delivery are performed after clean compilation.

## New nodes

`def-sf-native-proper-coefficient-operations` packages the native arbitrary-scheme-map
coefficient map, actual module/derived adjunction and its finite-integral normalization.
`def-sf-native-proper-tensor-comparison` packages the actual pure-generator and K-flat
representative equations for its tensor and unit. Their source is BS 6.8.14–6.8.15
and the item's explicit normalizations. Separate modules keep each compile under
60 seconds. These are fully specified types, with no sorry data and no theorem
asserting their existence. The item asserts their existence. Both new nodes were
searched by LeanSearch, LeanFinder, Loogle, Mathlib grep, source/Sheaf rg, DAG rg and
blueprint_refs.py: generic module adjunctions and isomorphism-only native reindexing
exist, but do not supply this arbitrary-proper-map normalization datum. Their
mathlib_searches retain the returned names and queries. A second self-reading
checked both new records against their definitions, including the whole completion
map and the actual derived computation counits.

Final compilation before dry-run: `GeometricCommonStageDirectImage` 11.1 s,
`NativeProperCoefficientOperations` 29.2 s, `NativeProperTensorComparison` 13.2 s,
`AdicProperAdjunctionRealization` 18.1 s (sandbox checks); their corresponding
library-mode checks also passed, all below the unchanged 60-second limit. The
long tensor formulas are named predicates to avoid repeating their dependent
types in generated record projections. Definitions contain genuine terms only;
the two postponed proofs are the named adjoint-existence and main comparison
theorems, with complete source/proof docstrings. No diagnostic commands are
present in delivered files.
