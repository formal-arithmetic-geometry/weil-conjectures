## Worker report

Item: `lem-sfb-supported-common-field-scalar-models`, stage 2, group NR.
The module `Sheaf.Paper.SupportedCommonFieldScalarModels` states the common-field
model theorem. Two new definition modules give the real scalar maps, support
comparisons and model predicate appearing in its statement. The dependency
order is `NormalizedInternalSupportScalars`, `SupportedCommonFieldScalarData`,
then `SupportedCommonFieldScalarModels`. The only postponed proof is the named main theorem,
whose docstring gives the nine-step DAG proof. No definition contains `sorry`.

### Hypotheses and coefficient objects

* `ℓ : ℕ`, `[Fact ℓ.Prime]`: the fixed prime. `PadicAlgCl ℓ` is the
  algebraic closure with its extended norm, as in the recorded coefficient nodes.
* `k`, `[Field k]`, `[CharP k p]`, `hp : 0 < p`, `hpℓ : p ≠ ℓ` render
  the characteristic hypotheses separately.
* `X : Over (Spec (.of k))`, `[LocallyOfFiniteType X.hom]`,
  `[QuasiCompact X.hom]`, `[IsSeparated X.hom]` give the finite-type separated
  scheme over the field using the dependency's bundled presentation.
* `S`, `T`, `a`, `b` are independent. `[IsImmersion a]` and
  `[IsImmersion b]` say locally closed; `haCons`, `hbCons` impose constructible
  ranges. No equality or disjointness condition on the supports occurs.
* `E F : PadicAlgCl.FiniteIntermediateField ℓ` are independent finite
  intermediate fields. Their subtype coercions carry the restricted norm.
  `L`, `M` are internal modules over the corresponding pulled-back coefficient
  objects, with separate `IsLisseCoefficientModule` hypotheses.
* `Modules` abbreviates exactly `Mod` in abelian sheaves on
  `Scheme.ProEt.topology`; `D` is the ordinary unbounded `DerivedCategory`.
  The site/coefficient sizes remain respectively `u+1,u` and `u+1`.
* `Profinite.padicAlgClRingObj ℓ` is C, finite-subextension-valued functions;
  `Profinite.continuousMapRingObj (PadicAlgCl ℓ)` is B, all norm-continuous
  functions. `toB` is the previously defined actual sectionwise inclusion.
  `toC`, `finiteInclusion`, and `coefficientMap` are the existing canonical maps.
  `scalar`, `restrict`, `adj` use the existing K-flat derived extension and
  exact restriction, including their actual adjunction maps.

### Clauses of the conclusion

* The existential proof witnesses `IsNoetherian X.left`, `IsNoetherian S`,
  `IsNoetherian T` allow the exact functors to elaborate without adding any
  Noetherian hypothesis. `IsNoetherian a.image`, `IsNoetherian b.image` and the
  three universal `IsCompact` clauses give the claimed closures and their
  quasi-compact open subsets. The support schemes are Noetherian consequences.
* `commonField ℓ E F` is literally the lattice supremum `E.1 ⊔ F.1`, with
  Mathlib's finite-dimensional-sup instance. Thus it is the smallest common
  intermediate field and is finite; no larger overfield or arbitrary choice
  substitutes for the compositum.
* `ordinary ℓ h` is the actual ordinary `Mod.extendScalars` of the relevant
  inclusion. `singleComparison` is the transpose of the ordinary scalar unit through
  the actual derived scalar adjunction, using exact restriction on singles. The
  conclusion asserts `IsIso` of this specified map, rather than assuming it.
  The first conjunct of `ModelAssertions` says the ordinary module is lisse.
* `support` is the composite of the termwise derived open lower shriek for
  `a.toImage` and closed lower star for `a.imageι`. The ordinary support is
  exactly `coefficientHeartLocallyClosedExtension`. `finiteModel` is
  `(a_! ordinary)[0]`, and `supportSingle` is the canonical exact realization
  comparison. `constantModelBoundedConstructible` is the existing finite
  constant local-model predicate. The two `ModelAssertions` give K and N.
* `generator` is the original supported C-scalar extension G (and H).
  `finiteReassociation` uses the existing equality of coefficient maps,
  the canonical `tower`, and the actual `singleComparison`. `alpha` applies
  support, the inverse normalized support comparison and `supportSingle`.
  Using E,a,L and F,b,M separately gives alpha and beta.
* `alphaB` is J(alpha) followed by the canonical A-C-B tower isomorphism;
  the analogous second instance gives beta_B. `directB` assembles the
  direct normalized B-support comparisons. Their equality is a conclusion.
* `SupportComparison` contains natural isomorphisms on full unbounded
  categories. `PullComparison.normalized` fixes inverse-image comparison as
  the mate of the actual restricted-action square. `SupportNormalized` fixes
  the closed isomorphism to the prescribed counit construction.
* The second `SupportNormalized` conjunct is the open-unit identity after
  scalar extension and inverse image. The first conjunct characterizes the
  closed restriction through the actual closed-adjunction Hom equivalence:
  new counit after the comparison equals inverse theta followed by scalar
  extension of the old counit. This is the definition of `closedScalarMap`,
  not an unspecified natural isomorphism. The last conjunct states both open
  restrictions are zero and the restricted morphism is zero. These assertions
  are quantified over every derived object, without a cohomological bound.
* `UnitEquation` is the displayed U(alpha_B) eta_G alpha-inverse equation,
  followed by restriction to the common A and its canonical restriction
  associator. The right side is `inducedMap`, defined independently by the
  transpose of the direct A-B unit under the A-C adjunction. It is the
  coefficient-induced map z tensor v mapped to c(z) tensor v.
* `tower` is canonical left-adjoint uniqueness for the actual scalar
  adjunctions and the actual restriction-composition identification.
  `UnitTower` asserts its identification of successive and direct units.
  The A-C-B and original-field-A-C towers are included on each support,
  closure and ambient scheme.
* `forward` is the existing section-ring equivalence localized termwise; the
  existing internal/section tensor-Hom comparison proves preservation of tensors,
  internal Homs and evaluation for this fixed equivalence. The repeated
  `SectionTensorHom` proposition has been removed.
* `sectionSupportComparison` is a **defined** natural isomorphism: localize
  `InternalModuleOperations.lowerComparison A a.imageι` and
  `InternalModuleOperations.openComparison A a.toImage`, insert the exact
  functor composition comparisons and compose through the closure. Its
  underlying closed map is identity on sections; the open comparison is pinned
  by the existing adjunction mate. There is no bare `Nonempty` support iso.
* `SectionScalarComparison` abbreviates the existing
  `OpenInternalScalar.scalarTransport c X`. Its first component is the actual
  universal normalized section `ScalarDerivedPair`; restriction is identity on
  sections, and the extension comparison's inverse mate is its localized
  restriction square. The duplicate scalar transport proposition was removed.
* `sectionSupportScalar c a d qS qX V` conjugates the **specified**
  `supportComparison c a d.closedIso` by `sectionSupportComparison` and the
  fixed scalar comparisons. Thus its support factor is the same normalized
  comparison, including the closed counit, open-unit and open-zero clauses.
* `sectionGeneratorComparison` identifies the image of G with the actual
  section support of the section E-to-C scalar extension. `sectionAlpha` is
  assembled independently of `alpha`: reassociation on S, inverse section
  support square, and section support/single comparison. The first equality
  of `SectionModelAssertions` says this composite is the image of alpha.
* `sectionAlphaB` applies the actual section C-to-B functor to `sectionAlpha`
  and then `sectionTower`; the second equality identifies it with the image
  of alphaB. Together with `alphaB = directB` this also identifies the direct
  B-support comparison. The two copies of `ModelAssertions` give beta and
  betaB without identifying either field or support.
* `SectionUnitEquation` uses section alpha inverse, the **actual** section
  pair's scalar unit, and restriction of section alphaB. The explicit canonical
  restriction comparisons identify the common A endpoints. Its right side is
  `forward A X` applied to the independently defined `inducedMap`. This is
  an additional section equation on the actual maps, not an assertion of a
  generic equivalence. The existing mate normalization and the two comparison
  identities identify this equation with `UnitEquation`.
* Neither scalar flatness of c nor a bound on its scalar extension is
  a hypothesis. Empty schemes, empty support factors and rank zero are not
  excluded anywhere.

### Dependency declarations used

* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField` (setting convention).
* `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic` and
  `.FiniteSubextension`: `Profinite.padicAlgClRingObj`,
  `PadicAlgCl.FiniteIntermediateField`, `Profinite.padicSubfieldRingObjMap`,
  `Profinite.padicSubfieldRingObjToPadicAlgCl`, and
  `Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl`.
* `Sheaf.Topology.ContinuousMapCondensedRing` / upstream continuous-map
  coefficients: `Profinite.continuousMapRingObj`.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` and
  `.ChangeOfCoefficients`: `condensedRingObj`, `coefficientMap`,
  `coefficientMap_comp`, `CondensedRing.derivedComapUpperStarIso`,
  `CondensedRing.derivedOpenImmersionShriekIso`.
* Mathlib's `Scheme.ProEt.topology`, `CategoryTheory.Mod`,
  `DerivedCategory`, `IsImmersion`, `IsOpenImmersion`, `IsClosedImmersion`,
  `IntermediateField.finiteDimensional_sup`; locally closed factorization
  `a.toImage` and `a.imageι`.
* `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`:
  `Mod.derivedExtendMapDerivedCategoryAdjunction`; the ordinary scalar unit
  and exact derived/single comparisons.
* `Sheaf.Paper.CondensedOpenClosedRecollement`:
  `CondensedRing.condensed_open_closed_recollement`.
  Its selected witness `closedExact` is only a proof of exactness.
* `Sheaf.Paper.CoefficientHeartFiltration`:
  `coefficientHeartLocallyClosedExtension`.
* `Sheaf.Paper.CoefficientHeartStratificationDefs`:
  `IsLisseCoefficientModule`; `Sheaf.Paper.CondensedConstantConstructibility`:
  `constantModelBoundedConstructible`.
* `Sheaf.Paper.KFlatScalarComparisonNormalization`:
  `SheafOfModules.ScalarPullback.mate`; `Sheaf.Paper.ClosedSupportedScalarComparison`:
  `SheafOfModules.ScalarPullback.closedScalarMap`.
* `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `InternalAbelianSheafModule.sectionModuleEquivalence`;
  `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`:
  `InternalAbelianSheafModule.InternalSectionScalarAdjunction`.
* `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`:
  `InternalModuleOperations.extension`, `InternalModuleOperations.lowerStar`.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`:
  `CondensedRing.derivedHom`; `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison`
  and its public tensor comparison module: `ModuleObjectRingedComparison.hom`,
  `.ring`, `.TensorComparison`, and the native coefficient closed/tensor structures.
  Their definition owners are cited explicitly; the general comparison theorem
  is a proof import, rather than a duplicated conclusion.
* `Sheaf.Paper.ConstructibleAlgClTopologyComparison`:
  only `algClTopologyInclusion`, the canonical map already used downstream;
  its topology-comparison theorem is not used as a proof of this obligation.

### Edge cases checked

E=F and E contained in F give the same supremum and canonical inclusions.
The theorem does not identify E and F or S and T. The identity immersion S=X
has the ordinary identity support comparisons. Empty S or T and rank-zero
lisse modules give zero extensions and zero single complexes; no nonempty
or positive-rank constraint appears. Characteristic p=0 is excluded exactly
by hp, and p=ell by hpell. No flatness or bounded-scalar-extension hypothesis
has been introduced. All support comparison quantifiers are unbounded.

### Searches

* `msearch.py ... leanfinder`: “Locally closed supported lisse sheaves over two
  finite l-adic fields have common compositum scalar models with derived
  support and unit comparisons” returned eight unrelated condensed-category
  and sheaf construction hits, no match for this combined statement.
* `msearch.py ... loogle`: `IntermediateField, Module.Finite` returned twelve
  field-theoretic results, no supported scalar model or normalization statement.
* `msearch.py ... grep`: `(supported|Supported|commonField|common_field).*(scalar|Scalar)|(scalar|Scalar).*(supported|Supported)`
  returned two unrelated Haar results.
* `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `SupportedCommon`, `supported.common.field`, `commonFieldScalar`: no match.
* `rg` for `supportSingle`, `finiteReassociation`,
  `derivedCoefficientHeart`, `coefficientHeart.*(Derived|derived)`, and
  `closedScalarMap`: reused the existing closed scalar map; other hits did
  not provide this theorem or its degree-zero composite support realization.

The new definition-node dependency edges form the chain from the main item
to the finite-field data to the generic normalized support data. Their
existing prerequisites have no path back to the item. No original dependency
edge was removed.

No mathematical statement fault or source correction was found. No existing dependency
node is replaced. Primitive notions use the recorded declarations. The new
public packages collect the exact canonical comparisons needed by this node;
every helper is listed in its owning definition node’s Lean record. The return
revealed ownership omissions and an insufficient section-ring clause; those
repairs are detailed below, without changing the item’s mathematical statement.


## New nodes

`def-sfb-normalized-internal-support-scalars` owns
`Sheaf.Paper.NormalizedInternalSupportScalars`: the actual internal K-flat
scalar functor and adjunction, restriction and scalar tower, coefficient-induced
map, single-complex comparison, exact closure support and normalized support
comparison data. It builds on existing module/scalar/support constructions;
it does not posit their existence by a hollow choice. The generic conditional
`lem-sfb-normalized-immersion-comparison-coherence` does not supply this
specialized internal-module package: its functors and comparisons are given
parameters, while these definitions fix the actual coefficient maps and mates.
Its source is scalar-six pullback proof (1)--(3).

`def-sfb-supported-common-field-scalar-data` owns
`Sheaf.Paper.SupportedCommonFieldScalarData`: compositum and finite-field models,
the actual alpha/alpha_B/direct-B composites, unit equations, canonical section
transport predicates and `ModelAssertions`. The theorem then asserts this
predicate separately for the two supports with their fixed common compositum.
The source is the direct-image proof (3) common-field obligation and scalar-six
pullback (1)--(3). The existing `def-sfb-scalar-hom-comparison-data` concerns
ringed-module tensor/Hom scalar-adjunction packages; it has neither these
supported finite-field objects nor their support/field comparison composites.
Its underlying tensor and Hom models are reused through the published
internal/section comparison, rather than copied.

For both packages the exact Mathlib search records are stored in
`mathlib_searches`: LeanSearch (the relevant new package), Loogle
`"extendScalars", "DerivedCategory"` (zero hits), and grep
`SupportComparison|SupportNormalized|commonFieldScalar|finiteReassociation`
(zero hits). The first LeanSearch returned eight unrelated sheafification,
localization and module results; the second returned eight elementary
intermediate-field/scalar-tower results. Exact-word searches for the three
new declaration names in `dag/nodes`, `lean/WeilConjectures` and `lean/Sheaf`
found none. `tools/blueprint_refs.py search 'supported common'` found zero
blueprint nodes; the ancestor tool returned `None` for this agent-created
obligation. The definition nodes therefore retain `blueprint.from.node=null`
and the originating item’s full via chain. Earlier broad searches found
unrelated compact-support comparisons, not this internal pro-etale package.

These are real definitions with no postponed theorem or proof. Separating
the generic normalized support data and the finite-field model data avoids
re-elaborating their concrete functor implementations in one large file and
keeps each delivered module within the compiler’s fixed per-file budget.


`def-sfb-scalar-pullback-mate` records the existing
`SheafOfModules.ScalarPullback.mate` definition in
Sheaf.Paper.KFlatScalarComparisonNormalization: the inverse scalar-adjunction
mate of the fixed action square. It adds ownership only, not a module.

`def-sfb-closed-scalar-map` records the existing
`SheafOfModules.ScalarPullback.closedScalarMap` in
Sheaf.Paper.ClosedSupportedScalarComparison: the closed-counit transpose.
It adds ownership only, not a module.

`def-sfb-section-module-operations` records the existing ring, equivalence,
section lower/upper star and open extension, their adjunctions and normalized
comparisons in Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport.
Its comparison maps are exactly those localized by sectionSupportComparison.

`def-sfb-internal-section-scalar-adjunction-data` records the existing
`InternalAbelianSheafModule.InternalSectionScalarAdjunction` predicate in
Sheaf.CategoryTheory.InternalSectionScalarAdjunction, including the ordinary
and derived normalizations. It adds ownership only, not a module.

`def-sfb-algcl-topology-inclusion` records the existing
`algClTopologyInclusionRing` and `algClTopologyInclusion` definitions in
Sheaf.Paper.ConstructibleAlgClTopologyComparison: the actual coefficient
inclusion used as toB. It adds ownership only, not a module.

`def-sfb-open-internal-scalar-transport-data` records the existing
`OpenInternalScalar.ScalarTransport`, `restrictionComparison`, and their
specialized actual pair in Sheaf.Paper.OpenInternalKFlatMateNormalization.
It adds ownership only and reuses the existing scalar pair and section-map
owners. The common source, three-kind searches and nonduplication evidence
for these six definition-owner nodes are detailed in the repair section below;
each node also stores its own full search records and source place.

## Repair of returned head 50fcdd0e86ee

H3: removed `SectionScalarTransport`, the copied `SectionTensorHom`, and the
bare `SectionSupportTransport`. The replacement explicitly builds the section
support comparison from localized canonical lower/open comparisons and states
transport of alpha, alphaB and the actual section scalar-unit equation, as
mapped clause by clause above. `sectionAlpha` does not refer to internal alpha;
its equality with the transported alpha is a conclusion. All internal support
normalizations remain unchanged and are used by `sectionSupportScalar`.

H12/H2: replaced plain-definition citations to theorem nodes with their actual
owners: `def-sfb-locally-closed-coefficient-extension`,
`def-sfb-internal-section-total-comparison`,
`def-sfb-internal-section-derived-tensor-comparison`,
`def-coef-ringed-tensor-hom-model`, and
`def-sfb-native-derived-koszul-braiding`. Added the requested canonical-map
owners `def-sfb-derived-open-immersion-shriek-iso`,
`def-sfb-derived-comap-upper-star-iso`, `def-sfb-qlbar-subextension-map`, and
`def-sfb-qlbar-subextension-to-qlbar`. Existing theorem citations remain only
where they supply proof-irrelevant exactness properties, and the new node text
says so. The unchanged theorem statement, commonField, internal alpha/alphaB,
UnitEquation, finite-model conclusions, hypotheses and universes are retained.

The following additional definition nodes bind existing published declarations;
no source module is changed or copied:

* `def-sfb-scalar-pullback-mate`: `ScalarPullback.mate`, inverse adjunction
  mate of the specified action square; source KFlatScalarComparisonNormalization.
* `def-sfb-closed-scalar-map`: `ScalarPullback.closedScalarMap`, transpose of
  inverse pullback comparison followed by the old closed counit.
* `def-sfb-section-module-operations`: the existing section ring, equivalence,
  actual `lowerStar`, `upperStar`, `extension`, adjunctions and canonical
  `lowerComparison`, `upperComparison`, `openComparison`. The section support
  comparison composes these exact canonical maps.
* `def-sfb-internal-section-scalar-adjunction-data`: the existing
  `InternalSectionScalarAdjunction` predicate and its full ordinary/derived
  normalization, separately from its existence theorem.
* `def-sfb-algcl-topology-inclusion`: `algClTopologyInclusionRing` and
  `algClTopologyInclusion`, the actual subtype inclusion of C into B.
* `def-sfb-open-internal-scalar-transport-data`: the existing `ScalarTransport`,
  `restrictionComparison` and `scalarTransport`, which fix the actual internal
  adjunction used here. The general scalar pair is already owned by
  `def-sfb-scalar-hom-comparison-data`, and its section map by
  `def-sfb-section-scalar-map-data`; both owners are reused.

Each is an `existing:true` ownership extraction with no extra module. Their
sources, full signatures, source docstrings and surrounding universe binders
were read; their Lean records quote the source signatures verbatim. The three
kinds of Mathlib search are stored as returned JSON records in each new node:
LeanSearch and LeanFinder returned eight ordinary ring/module adjunction hits,
Loogle reported unknown `mateEquiv` and zero hits, and grep returned zero hits.
Exact DAG definition-owner searches found only the already reused section-map
owner; source searches found these existing Sheaf declarations and no upstream
copy. Blueprint searches returned zero 'section scalar' hits and eight
unrelated 'support comparison' hits. The existing ScalarTransport discovered
by that source search is reused instead of the initially drafted structure.

## Repair self-check

The prescribed initial saved-packet dry run completed with
`OK (dry run): commit 7b04b2dae01`; it did not push. That checked the saved
packet against current server sources and the current branch. The substantive
return was then repaired as described above. A read-only comparison with the
current main node confirmed no changes outside `lean` and authorized additions
to `stmt_deps`; no source statement correction was necessary.

The new scalar data are the existing mate-normalized interface. Canonical
support and scalar comparisons determine every endpoint of sectionAlpha and
sectionAlphaB. SectionUnitEquation restricts the actual section-unit composite
to A, using the identity-on-sections exact restriction identifications on both
sides, and concludes equality with the image of inducedMap. Empty supports,
rank zero, E=F and S=X remain allowed. No nonempty, flatness, boundedness or
universe-equality assumption was added. Only the main named theorem is sorry;
definitions contain real data and the newly selected exactness witnesses are
proof-irrelevant properties, not choices of functors or isomorphisms.

Continuation validation (2026-10-22): the prescribed initial saved-packet dry run
found a concrete instance-resolution failure at the localization of the closed
section comparison: `PreservesFiniteColimits` for section `lowerStar` and its
composition with the equivalence could not be synthesized. The repair supplies
`sectionClosedExact A a.imageι` and `sectionOpenExact A a.toImage` explicitly in
the body of `sectionSupportComparison`. These are the already declared
proof-irrelevant exactness witnesses. No signature, canonical comparison, node
statement, hypothesis or conclusion changed.

The required `scompile.py` check of all three modules passed with no errors or
unexpected warnings. The library-form compiles took 32.4 seconds for
NormalizedInternalSupportScalars, 37.1 seconds for SupportedCommonFieldScalarData,
and 2.1 seconds for SupportedCommonFieldScalarModels. The wrapper also checked
the sandbox forms separately; every compile stayed below 60 seconds.

The continuation self-check compared the node signature strings against their
source files. The subsequent preflight found that the theorem record was only
a prefix (truncated at a named argument), the existing lowerStar signature
needed to start at abbrev, and a removed projection helper remained in the
declaration list. These record defects are now repaired; the theorem record
contains its entire signature and the stale helper is removed. Against the current read-only main node, only `lean` and the
authorized additions to `stmt_deps` differ. The canonical section support
comparison still localizes exactly `lowerComparison A a.imageι` and
`openComparison A a.toImage`; section alpha, alphaB and the unit equation use
those actual comparisons and the fixed-adjunction scalar transport. All
requested definition-owner citations and six existing-declaration owner nodes
are present. The immutable-head return is repaired substantively, not merely
rebased or re-pushed.

The next dry run compiled the Lean successfully and reported the three record
faults above plus the missing six owner-node names in the New nodes section.
The records and report section were repaired in the sandbox. No change to the
Lean was needed for these preflight diagnostics. The final prescribed dry run
passed: `OK (dry run): commit cf8168197e8 passes the preflight and compiles;
nothing pushed`. The final source self-check found no sorry in either
definition module, exactly one sorry (the named theorem) in the statement
module, and all delivered source lines at most 100 characters. The matching
node signature records are complete. This success is recorded before the
authorized final deliver2.py push.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
