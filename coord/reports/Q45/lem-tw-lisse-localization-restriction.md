## Worker report

Q45 states `lem-tw-lisse-localization-restriction` in
`Sheaf.Paper.LisseLocalizationRestriction`, declaration
`WeilConjectures.LisseLocalization.exists_lisseLocalizationRestriction`.
Its only theorem has proof `sorry`. All helper definitions contain actual data;
the structures package conclusion data and do not assume the result. The module
contains the node's eight-step proof, with its dependency names, in the theorem docstring.

### Hypotheses and objects

- `D : FiniteFieldDatum.{u}` is the recorded finite field together with its fixed
  algebraic closure. `l`, `Fact l.Prime`, and `hl : l ≠ D.p` give the coefficient
  prime. `E : Type u`, `Field E`, `Algebra ℚ_[l] E`, and
  `FiniteDimensional ℚ_[l] E` give the finite extension. As in the dependency
  interfaces, the ambient algebraic-closure embedding is unused: the assertion
  is invariant under an isomorphism of finite coefficient extensions.
- `X : Scheme.{u}`, `X.Over (Spec (.of D.k))`, `LocallyOfFiniteType` and
  `QuasiCompact` of its structure map express finite type over the geometric
  field. There is no separatedness assumption.
- The `letI` residue-field invertibility in the conclusion is derived from
  `finiteFieldDatumPrimeUnit D l hl` and the structure map. It is not an extra
  geometric hypothesis. It permits use of the recorded lisse and unit interfaces.
- `integralRing` abbreviates the existing
  `completedIntegralCommRingSheafUnrestricted l E X`. Its inverse-limit tower has
  index `n : ℕ` representing the source's positive exponent `n+1`.
  `rationalRing` is precisely `ringedLocalizationRingOfUniverses` of that ring at
  the existing constant uniformizer section `LisseLocalizationInterfaces.completedScalarSection`, a transparent re-export
  of `AlgebraicGeometry.ProEtale.spCompletedScalarSection`.
  `localizationUnit` is the actual unit of this sheafified section localization.
- `Modules X R` abbreviates `ringedSiteModules` of `X.adicLisseForget.obj R`.
  This uses ordinary module sheaves, not completed modules. All derived
  categories are the recorded standard unbounded categories. Object universe
  `u+1`, morphism universe `u`, and coefficient universe `u+1` of the small
  pro-etale site remain distinct. Canonical specialized sheafification and
  standard-derived-category instances fix instance-search universe ambiguity;
  they introduce neither assumptions nor alternative constructions.
- `Model` is the existing `DerivedChangeOfRingsCochainModel` for the actual
  localization unit. Its ordinary functor is prescribed on objects and maps by
  `changeOfRings`; its derived functor has the universal K-flat comparison.
  Thus it is actual derived scalar extension, rather than an arbitrary functor.
- `sfIntegralConstructibleCategory`, `sfRationalConstructibleCategory`, and
  `sfRationalConstructibleLocalization` are the dependency categories and raw
  localization, used without replacing the integral objects or the arrow quotient.

### Conclusions, clause by clause

- The theorem produces `dx : LocalizationData l E X` and one such datum `du U`
  on every chart. `finiteLimits` and `finiteColimits` make its already additive
  ordinary scalar extension exact. `comparison` identifies derived scalar
  extension with `model.E.mapDerivedCategory`; `normalization` fixes this
  comparison by the universal cochain counit on every complex.
- `LocalizationData.homology i` is a natural functor isomorphism
  `F ⋙ H^i ≅ H^i ⋙ E`, for every integer `i` and every unbounded derived input.
  By `model.obj_eq`, `E` is exactly `A ⊗_B -`, not an unrelated exact functor.
- `realization` is the induced raw rational functor `J`;
  `object_eq` gives literally `J(QK)=F(K)`. `map_tensor` gives
  `J(a ⊗ f)=a F(f)`, transported through those object equalities and the
  existing fraction-normalized coefficient equivalence. `additive` records
  additivity. The field action on the target is the existing scalar-localization
  derived action, composed with `sfRationalCoefficientEquiv.symm`.
- `halves` uses `sfRationalStandardClass` for both Boolean choices and all
  integer cuts. It asserts vanishing on exactly the forbidden side in the
  ambient derived category. It does not assume an integral heart representative.
- `∀ U : X.ProEt` has no finiteness or quasi-compactness condition on `U.left`.
  `SliceCoefficients.integral` and `.rational` identify the actual restrictions
  with the completed and localized rings on `U.left`. `residue`, `projections`
  and `constants` identify all finite quotient maps, identically on constants.
  `unit` identifies localization units. `fractions` identifies every actual
  sheafified local fraction `b/t^n`, including `n=0`, with the same fraction
  after the integral section comparison.
- `LisseLocalizationInterfaces.coefficientRestriction` re-exports the actual
  coefficient restriction `completedRingRestriction`, equivalently the recorded
  slice equivalence transport;
  `moduleRestriction` composes actual `SheafOfModules.overFunctor` with
  `pushforward` along `ProEt.sliceFrom`, transporting coefficients by the
  specified ring isomorphism. Its section data are literal restriction.
- `SliceTensorCompatibility` states the existing sheaf tensor comparison on
  the literal ringed slice, for all module sheaves over either B or A, natural
  in both factors. Its last equation fixes the image of every sheafified pure
  tensor to the same restricted tensor. This uses `siteSheafTensorRight` and
  `siteSheafTensorTmul` from the dependency interface, not a second tensor.
- `SliceLimitCompatibility` is for the B-module strict tower category. It
  supplies exact ordinary and tower restrictions, total right derived limits
  on both sites, universal right-derived units invertible on K-injective
  towers, and their natural comparison. The first normalization equation fixes
  it on all cochain complexes by the actual `LisseLocalizationInterfaces.limitComparison`
  (compatible-tuple/limit.post map). The final equation fixes every tower
  projection using `LisseLocalizationInterfaces.limitProjection` on K-injective models.
- `StrictLimitRealizes` additionally requires these very same total-derived
  limits to realize `IsDerivedLimitTriangle` for the actual levelwise evaluated
  strict tower; evaluation is identified on complexes with termwise evaluation
  followed by localization. Its projections are normalized using the same
  right-derived unit and strict tower projections. Thus the clause is about
  the completed-coefficient derived limit, not arbitrary unrelated Roos cones.
- `SliceLocalization` supplies exactness and additivity of both transported
  module restrictions. `ordinaryComparison` is natural in modules; `tensors`
  fixes it by `a ⊗ x ↦ a|_U ⊗ x|_U`, using actual sheafification and the
  specified model's object equality. `comparison` is the natural derived
  isomorphism `F_X ⋙ res_A ≅ res_B ⋙ F_U`. Its `normalization` ties it to the
  ordinary tensor comparison and the two universal cochain counits. Combined
  with `map_tensor`, this also fixes scalar-fraction compatibility of raw arrows.
- On `rationalLisseHeartProperty l E X K` the theorem provides the derived
  isomorphism `J K ≅ singleFunctor 0 (H^0 (J K))`, and
  `SheafOfModules.IsFiniteLocallyFree (H^0 (J K))`. That existing predicate
  allows varying finite ranks and zero rank; no constant global rank is imposed.
- The actual recorded `pullbackTensorRationalUnit` goes to
  `singleFunctor 0 (SheafOfModules.unit A)`.
- For each pair of lisse heart objects the theorem provides their degree-zero
  isomorphisms `eK,eL` and asserts bijectivity of
  `f ↦ eK.hom ≫ (singleFunctor 0).map f ≫ eL.inv`. Its domain is precisely the
  ordinary module-sheaf Hom and its codomain the derived Hom of their images.
  This makes no assertion about higher Ext and no assumption of full
  faithfulness of realization on arbitrary constructible objects.

### Dependency declarations used

- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `over`, `Hom.over`, `pushforward`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and its
  publicly imported tensor interfaces:
  `SheafOfModules.siteSheafTensorRight`, `siteSheafTensorSecondMap`,
  `siteSheafTensorTmul`; the underlying tensor is the dependency's sheafified
  section tensor. `SheafOfModules.changeOfRings` and `changeOfRingsPresheaf`
  are the upstream scalar tensor construction.
- `Sheaf.Paper.RationalLocallyFree`:
  `WeilConjectures.rationalLisseHeartProperty`, `IsRationalLisse`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory.standard`, `homologyFunctor`, `Q`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and
  `Sheaf.Paper.CompletedIntegralCoefficients`:
  `integralConstantToCompletionOfUniverses`,
  `completedIntegralCommRingSheafUnrestricted`,
  `integralCoefficientCommRingSheaf`,
  `completedIntegralCommRingProjectionUnrestricted`.
- `Sheaf.Paper.SfConstructibleHeart`: `sfRationalStandardClass`;
  `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructibleCategory`;
  `Sheaf.Paper.SfRationalizationKaroubi`:
  `sfRationalConstructibleCategory`, `sfRationalConstructibleLocalization`,
  `sfRationalCoefficientEquiv`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimitTriangle` (hence `IsDerivedLimit`).
- Recorded coefficient-extension API: `Padic.coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`, `coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `ProEt.topology`, `Scheme.ProEt`;
  the weakly-etale localization module supplies `ProEt.sliceFrom`, `sliceDense`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `ringedStrictTowerHomotopyLimitIndependentCoefficients`, used for the
  total right-derived and normalized Roos realization interpretation.
- `def-tw-lisse-localization-interfaces`, module
  `Sheaf.Paper.LisseLocalizationInterfaces`: the nine declarations in namespace
  `WeilConjectures.LisseLocalizationInterfaces` listed under New nodes below.
  The statement uses these transparent definitions; their original host theorem
  modules are retained as proof imports.
- `Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses`:
  `ringedLocalizationRingOfUniverses`, `ringedLocalizationRingUnitOfUniverses`,
  `ringedLocalizationRingPresheafOfUniverses`.
- `def-sfb-derived-change-of-rings-cochain-model`, module
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel`.
- `def-a1-common-stage-coefficient-unit`, module
  `Sheaf.Paper.DerivedPullbackTensorIso`: `pullbackTensorRationalUnit`;
  `Sheaf.Paper.DirectImagesConstructible`: `finiteFieldDatumPrimeUnit`;
  `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`.
- `def-sc-finite-locally-free-sheaf`, module
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree`, whose finite local generator data allow
  varying ranks, including zero.
- The theorem's proof dependencies are imported, including the literal
  pro-etale restriction comparison, derived completeness on slices, exact
  derived factorization, ringed tensor pullback, and derived-limit uniqueness.
  Mathlib's single-functor full/faithful and degree-concentration APIs supply
  the last two proof steps.

The statement dependencies cite the owners of the constructions actually used.
The new definition node re-exports nine existing canonical definitions, without
asserting their hosts' theorem conclusions. The remaining comparison helpers are listed in the item's `lean.declarations`;
the moved strict-limit predicates and canonical instances are listed in the
new definition owner's record, as authorized by brief-stage2 §1.
The established continuous-coefficient realization package
`LisseRationalRealizationData.At` was read but does not state this node: it uses
a continuous rational coefficient presentation and bundles other, stronger
lisse equivalence data; it does not state exact localization on all unbounded
inputs and normalized strict-limit restriction on every site object.

### Edge cases and source reading

Checked BS 6.8.2 and 6.8.3 and the rational equivalence in 6.8.14(2), in the
local paper PDF, together with the current blueprint's real-linear unit and
proof. Checked zero modules, empty local generator families/rank zero, varying
finite local ranks, empty schemes, degree zero, positive and negative
cohomology degrees, unbounded complexes, the exponent-zero fraction, both
standard halves, non-separated finite-type schemes, and arbitrary pro-etale
charts whose source is not finite type. No chart is restricted to an affine,
etale, finite-type, or quasi-compact subclass. No invertibility of a geometric
structural coefficient map and no global integral heart lattice is assumed.
No statement fault or `STATEMENT-DISPUTED` issue was found.

### Searches

- `msearch.py ... leanfinder "Exact scalar localization of completed pro etale
  coefficients commutes with slice restriction and sends rational lisse sheaves
  to finite locally free modules"`: 8 hits, led by `BDeRham` and ring-theoretic
  etale localization results; none states this node.
- `msearch.py ... loogle "SheafOfModules.overFunctor,
  DerivedCategory.singleFunctor"`: 0 hits.
- `msearch.py ... leansearch "Exact localization of sheaves of modules commutes
  with cohomology and restriction to slice sites"`: 8 hits, including
  `SheafOfModules.over` and `ModuleCat.localizedModule_functor_map_exact`;
  useful components, no complete statement.
- `msearch.py ... grep "localization.*(exact|sheaf)|sheaf.*localization"`:
  25 hits, including `Mathlib/Algebra/Module/LocalizedModule/Exact.lean`;
  no sheaf-derived lisse/slice assertion.
- `rg` in `lean/WeilConjectures` for localization/lisse and the exact item id:
  the tensor and local-freeness APIs are present, no statement of the item.
- `rg` in `lean/Sheaf` found the generic continuous localization, normalized
  slice tensor and strict-limit theorems, and existing lisse realization data;
  each was opened. They provide components, not the requested conjunction.
- `rg` of `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and
  `lean/Sheaf` found no existing `WeilConjectures.LisseLocalization` namespace
  or the new theorem/helper names.

## New nodes

`def-tw-lisse-localization-interfaces` owns
`Sheaf.Paper.LisseLocalizationInterfaces`. It re-exports the following existing
constructions with transparent `abbrev` definitions and no postponed proofs:

| New declaration in `WeilConjectures.LisseLocalizationInterfaces` | Existing construction |
| --- | --- |
| `completedScalarSection` | `AlgebraicGeometry.ProEtale.spCompletedScalarSection` |
| `coefficientRestriction` | `WeilConjectures.completedRingRestriction` |
| `towerRestriction` | `CategoryTheory.sliceTowerRestriction` |
| `derivedTowerRestriction` | `CategoryTheory.sliceTowerDerivedRestriction` |
| `limitComplex` | `CategoryTheory.sliceStrictTowerLimitComplex` |
| `limitComparison` | `CategoryTheory.sliceStrictTowerLimitComparison` |
| `limitProjection` | `CategoryTheory.sliceStrictTowerLimitProjection` |
| `derivedLinear` | `CategoryTheory.scalarLocalizationDerivedLinearOfUniverses` |
| `coefficientMap` | `CategoryTheory.scalarLocalizationCoefficientMapOfUniverses` |

The new node states the completed scalar section and chart restriction, strict
ordinary and derived tower restrictions, strict limit complex and its canonical
comparison/projections, induced derived scalar action, and canonical localized
coefficient map. Its hypotheses reproduce the existing general interfaces with
independent site, coefficient and derived universes. Derived restriction requires
the exactness/additivity needed to construct it; no existence or isomorphism
conclusion from the host theorem nodes is assumed. There is no finiteness
condition on a chart. All nine bodies are the existing constructions themselves.
The source references are BS 6.8.2 and 6.8.14(2), and Stacks 04IX, 04J0, 0940,
0941. The definition node cites the existing coefficient, site, sheaf-module,
localization and derived-category owners required by its statement.

After the first successful two-file compile, the delivery dry run exceeded the
60-second limit for the main file. To keep each file within that limit, its
unchanged `StrictLimitRealizes` and `SliceLimitCompatibility` predicates and
seven canonical site/derived instances now live in the definition-owner module,
under their original declaration names. Their docstrings and declaration
ownership follow the new node; its statement specifies both full normalized
predicates and cites `def-weil-derived-limit`. This moves actual definition data
and introduces no theorem, hypothesis, arbitrary choice or changed comparison.

Before creating the definition owner, the following searches were run; their raw
results are stored in the node's `mathlib_searches`:

- `msearch.py ... leansearch "Definitions of completed coefficient constant
  sections slice restriction strict inverse limit complexes projections and
  localized scalar actions"`: eight results, including basic adic completion;
  none packages these definitions or owns the project's canonical helpers.
- `msearch.py ... leanfinder "Canonical definitions for restriction of strict
  towers to slice sites and scalar actions on localized module derived
  categories"`: eight results, including ordinary localization and derived
  linearity; none is the new definition interface.
- `msearch.py ... grep "sliceStrictTowerLimit|scalarLocalizationDerivedLinear|spCompletedScalarSection|completedRingRestriction"`:
  zero Mathlib matches.
- `rg` for these names and `scalarLocalizationCoefficientMap` in
  `lean/WeilConjectures` and `lean/Sheaf` found the canonical definitions in the
  four theorem modules named in the return. Their complete signatures and
  documentation were read and re-exported verbatim in type and value.
- `rg -l` in `dag/nodes` found the exact nine helpers only in those four
  theorem nodes. Other hits included
  `def-weil-pbc-scalar-localization-coefficient-actions`; its existing
  `CategoryTheory.scalarLocalizationDerivedLinear` and
  `scalarLocalizationCoefficientMap` were read in
  `Sheaf.CategoryTheory.ScalarLocalizationCoefficientActions`. They require
  `C : Type u`, `SmallCategory C` and coefficient universe `u`, unlike the
  already published `OfUniverses` interfaces needed here. The re-exports retain
  those independent universes, without introducing a second construction. `tools/blueprint_refs.py ancestor` located
  the parent blueprint unit `lem-tw-dual-negation`; the new node records its
  derivation from that unit via this item. The blueprint search for slice
  restriction also found no existing owner for the nine interfaces.

## Returned-delivery repair

The return at immutable head `2e5da8240aec` requested ownership/dependency repair
H2. Each requested change is made:

- The new definition owner above replaces the four theorem nodes
  `lem-sp-completed-coefficient-regular-quotients`,
  `lem-tw-completed-coefficient-ringed-coherence`,
  `lem-sp-slice-restriction-strict-derived-limit`, and
  `lem-per-rational-continuous-coefficient-derived-localization` in `stmt_deps`.
  The main module now names the new owner's aliases for all nine definitions.
  The four theorem modules remain plain imports for the postponed proof.
- `def-a1-common-stage-coefficient-unit` replaces
  `lem-pur-derived-pullback-tensor-iso` as owner of `pullbackTensorRationalUnit`.
- `lem-sfb-localized-site-tensor-restriction` is removed from `stmt_deps`;
  its theorem is used only in the proof outline.
- `lem-weil-structure-direct-images-constructible` remains a statement
  dependency because its theorem `finiteFieldDatumPrimeUnit` supplies an actual
  proof used to form the residue-field invertibility instance.
- The previously uncited owners `def-sfb-derived-change-of-rings-cochain-model`
  and `def-sc-finite-locally-free-sheaf` are added to `stmt_deps`.

The returned sandbox node was compared with the current shared node: all fields
other than `lean` and `stmt_deps` agree. The delivery retains the live statement,
proof, and proof dependencies. No source-based statement correction is needed;
all changes are transparent definition re-exports, ownership records and the
unchanged helper-definition split required by the per-file compile limit.
Current live declarations were read before compiling against the live build.

### Validation

The initial two-file compile passed; a later dry run exposed the main-file
time limit and prompted the definition-module split described above. All
compiler probes use `scompile.py`, with
module mode and the same import
visibility as the delivery. Both delivered modules bind variables and universes
explicitly, contain no diagnostic commands or file-local notation/local
instances, and have no postponed definition data. There is one postponed
statement theorem, with the matching DAG node and source/proof docstring.
The delivery dry run and final push use the prescribed `deliver2.py` wrapper.
Independent semantic review belongs to the maintainer, as stated in the dispatch
brief; no second worker was started.

The repaired two-module packet passed `scompile.py` and then the prescribed
`deliver2.py --no-push` preflight and per-file compilation (dry-run commit
`cf42f692e6c`). No compiler error or unexpected warning remains.

## Second reading by Q45

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
