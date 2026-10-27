## Worker report

The delivery states `WeilConjectures.MixedCupCoefficientChange.mixedCupCoefficientChange`
in `Sheaf.Paper.MixedCupCoefficientChange`. All theorem proofs are postponed with
`sorry`, and all definitions have explicit data. The supporting module
`Sheaf.Paper.AdmissibleCupCoefficientPassages` organizes the existing four coefficient
stages and their actual scalar functors. The item statement is unchanged.

Hypotheses and clauses:

- The implicit `D : FiniteFieldDatum` contains p prime, a positive, q=p^a, the finite
  base field and its algebraic closure. `C : D.CoefficientDatum` contains ell prime,
  ell distinct from p, and the fixed algebraic coefficient closure.
- `d : Nat`, `G : PoincareDualitySetting D.k₀ d` express smooth pure dimension d≥0,
  separated, finite type and geometrically connected X₀. `pairingGeometricSpace D d G`
  is its actual geometric fibre and actual structure morphism. The separation
  instance is derived inside the statement from base change, rather than assumed.
  The compactification argument names the presentation used by the recorded cup.
- `Operations C` ranges over the existing normalized `SixFunctorDatum` at every
  finite subextension and every positive level. This supplies construction data
  already used by the cup definition; it assumes no coefficient comparison.
- `Stage.finite F n` means A_(F,n+1); `integral`, `rational`, `closed` are O_F, F,
  Qbar. `domain` uses intrinsic `finiteTorConstructible`, completed integral
  `finiteTorConstructibleIntegral`, and the full recorded rational/common categories.
- `Passage.finite` accepts every unital ring map between the finite quotients.
  No flatness, coefficient-linearity or projective-dimension hypothesis is imposed.
  In particular arbitrary nonflat same-field quotient maps are included.
  `reduction`, `integral`, `rational`, `localization`, `closure` are precisely the
  other five families in the item. The fields literally lie in the fixed closure.
- `siteChange` uses the canonical ringed-site derived scalar extension, recorded
  derived integral reduction, completed integral transition, raw rationalization,
  rational scalar transition and actual common-stage inclusion. `pointChange`
  uses the recorded ordinary-module derived scalar extension along `coefficientMap`.
  `change_domain` records preservation of the stipulated input domains; `change`
  is its restriction, not an independently supplied functor.
- `cohomology ... true` is the recorded compact-support operation followed by the
  actual point fibre; `false` is ordinary direct image followed by that fibre.
  Finite and integral values already have the correct common coefficient universe.
  At field stages the recorded fully faithful coefficient/carrier lift puts the
  existing complexes in that universe; no replacement ambient field category occurs.
- `cup` uses exactly `finitePairingCup`, `integralPairingCup`, `rationalPairingCup`,
  `commonPairingCup`; `sourceCoordinates` uses the prescribed point lift tensorator,
  and `targetCoordinates` identifies the exact recorded tensor target.
  `normalizedCup` is that same arrow in the displayed square's coordinates.
- `Comparisons.cohomologyIso f true/false` gives natural u_c/u_o on these actual
  functors. `ringed_cohomology_normalized` pins finite maps, reductions and
  completed integral inclusions to the actual ordinary counit mate or proper/open
  compactification comparison, conjugated by fixed operation realizations and
  canonical point-section maps. `localization_cohomology_normalized` and
  `field_cohomology_normalized` pin all remaining elementary maps to recorded
  SixFunctorCoefficientComparison supportAdjunction.left/directAdjunction.right
  and point-fibre identifications. The tensor-input instance and `tensorIso` give u_(c,tensor), by applying
  the compact comparison and then compact cohomology of the site tensor comparison.
  `finite_tensor_normalized`, `integral_tensor_normalized`,
  `rational_tensor_normalized` prescribe the existing derived balancing components.
  `reduction_tensor_normalized` fixes the Roos-projection tensor map on every
  good pair of integral representatives, with actual finite reduction models.
  `localization_tensor_normalized` fixes the identity on raw localized tensor
  objects; `closure_tensor_normalized` fixes the inverse common-stage comparison
  represented at the input field with its specified unitors. `tensor_natural`
  records their two-variable naturality.
- `pointTensor` is the fixed strong tensorator of the ordinary derived universal
  pair, normalized on K-flat complexes. `Comparisons.square` is the exact equality
  of the top/right and left/bottom composites, including this tensorator first on
  the left edge. Both inputs remain arbitrary objects of the specified domains.
- `identity`, `composition`, `tensor_identity`, `tensor_composition` express identity
  and successive-passage coherence. `PointUnitNormalized` and `PointCompNormalized`
  prescribe the ordinary balancing and reassociation maps on K-flat cochains.
  Every elementary component has its canonical-map equality; composition then fixes
  every passage expression. The formerly free `siteCongruence` field and its
  congruence fields are removed. No extra site isomorphism remains to be chosen.
- Taking `f := Passage.reduction F n` states reduction of the integral cup for every
  n+1≥1. Field and common-stage objects have actual integral finite representatives
  in the raw localization/common-stage constructions. `Passage` has no field-to-
  finite quotient generator; the statement asserts no such reduction functor.

Dependency declarations used:

- `WeilConjectures.AlgebraicGeometry.PoincareDualitySetting`:
  `AlgebraicGeometry.PoincareDualitySetting`, `structureMorphism` (sk-def-set upstream).
- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `CoefficientDatum`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructible`,
  `finiteTorConstructibleIntegral` and their existing categories.
- `Sheaf.Paper.DerivedPullbackTensorHom`: actual finite/integral/rational/common
  tensors and `integralTensorScalarComparison`, `rationalTensorScalarComparison`.
- `Sheaf.Paper.PodMixedSupportCupProduct`, through its public PairingData import:
  `SixFunctorDatum.*PairingCup`, `pairingGeometricSpace`, `pairingPointIdentifications`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionDerivedExtension`.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`: the public actual completed
  integral scalar construction, used through `integralTransition`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalScalarExtension`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `integralTransition`,
  `transition`, `inclusion`, `generalAlgebraicallyClosedConstructibleCategory`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`:
  `ModuleCat.ordinaryDerivedExtendScalars`, its prescribed monoidal structure and
  universal K-flat counit. This module publicly retains generic ringed scalar extension.
- `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`:
  `PurCompactSupport.scalarTensor_existsUnique`, the normalized ringed derived tensor
  comparison, selected inline from its unique balancing characterization. Its owning
  definition node `def-sf-compact-support-scalar-tensor-identification` and the coefficient-data
  owner `def-pur-integral-compact-support-coefficient-data` are stmt_deps.
- `Sheaf.Paper.PointSectionsDerivedReduction`: `pointReductionQuotient` and the
  actual point section coefficient conventions.
- `Sheaf.Paper.FinitePullbackTensorComparison`: `pullbackTensorFiniteModel`,
  `pullbackTensorFiniteModelIso`; owner
  `def-pur-finite-pullback-tensor-comparison` is now explicitly in stmt_deps.

Edge cases checked: n+1=1, equal quotient levels, nonflat quotient maps, identity
finite-ring maps, degree-zero and zero input complexes, d=0, nonproper X₀, ramified
finite integral extensions, localization and inclusion through further finite fields.
No choice of finite basis is part of a construction. The small pro-etale site retains
object universe u+1, morphism universe u. The coefficient-module localization uses
Hom universe u+1 and field carrier lift; no universe equality is assumed.

Searches made: LeanFinder `Mixed support cup product commutes with extension of
coefficient rings and integral reduction` returned eight unrelated cotangent hits;
Loogle `mixedSupportCupProduct, derivedScalarExtension` returned zero hits (unknown
first constant); Mathlib grep `mixedSupportCup|mixedSupport.*scalar` returned zero.
Project rg found the existing PairingData cups and PodMixedSupportCupProduct; these
are reused. Searching the item id in WeilConjectures returned zero. The additional
notion searches are recorded verbatim in the new node's `mathlib_searches`.

Validation: the prescribed scompile.py wrapper compiled all eleven delivered
modules cleanly in dependency order (including both sandbox and library forms).
The repaired main module compiled in 8.6 seconds. Delivery uses the required
deliver2.py dry-run and push wrappers. Named domain, coordinate
existence and main theorems have matching source and proof docstrings. Definitions
select only uniquely specified maps or structures whose fields fix their data.

No statement correction or disputed mathematical statement is proposed.

## New nodes

Additional existing:true owners: `def-sf-compact-support-scalar-tensor-identification`,
`def-sf-constructible-operation-scalar-transport`, and
`def-sf-integral-tensor-finite-comparison`; their statements and searches are
detailed in the repair sections below.

`def-sf-mixed-cup-coefficient-passages` defines tagged coefficient stages, precisely
admissible composable passages, their actual ring homomorphisms, existing ambient and
finite-Tor domains, and the specified scalar functors. Its source is the current
blueprint mixed-cup definition's coefficient paragraphs. Searches with LeanSearch,
LeanFinder, Mathlib/project grep and blueprint_refs.py found no single existing
notion organizing these four stages; individual constructions are all reused.

`def-sf-mixed-cup-normalized-scalars` owns `MixedCupNormalizedScalars`: ordinary pure-tensor point comparison, its unique all-K-flat derived descent, actual coefficient/section maps, exact scalar counit and carrier-lift comparison. Its source is the same final coefficient-compatibility sentence, expanded by proof steps 2–9. The searches recorded in the node find no exact existing assembly; all individual operation, scalar, tensor and point-fibre constructions are reused.

`def-sf-mixed-cup-coefficient-data` owns `MixedCupCoefficientData`: recorded cohomology/cup and tensor coordinates, their domain restriction, and point identity/composition normalization predicates. Its source is the same final coefficient-compatibility sentence, expanded by proof steps 2–9. The searches recorded in the node find no exact existing assembly; all individual operation, scalar, tensor and point-fibre constructions are reused.

`def-sf-mixed-cup-ringed-normalization` owns `MixedCupRingedNormalization`: finite/integral ambient coordinates and the exact canonical-map equality fixing both cohomology support choices. Its source is the same final coefficient-compatibility sentence, expanded by proof steps 2–9. The searches recorded in the node find no exact existing assembly; all individual operation, scalar, tensor and point-fibre constructions are reused.

`def-sf-mixed-cup-field-coordinates` owns `MixedCupFieldCoordinates`: fixed point-fibre scalar maps, localization comparisons, and integral-model bridges between independent normalized operation data. Its source is the same final coefficient-compatibility sentence, expanded by proof steps 2–9. The searches recorded in the node find no exact existing assembly; all individual operation, scalar, tensor and point-fibre constructions are reused.

`def-sf-mixed-cup-field-normalization` owns `MixedCupFieldNormalization`: component equations fixing rational scalar and closure cohomology to the recorded SixFunctorCoefficientComparison maps. Its source is the same final coefficient-compatibility sentence, expanded by proof steps 2–9. The searches recorded in the node find no exact existing assembly; all individual operation, scalar, tensor and point-fibre constructions are reused.

`def-sf-mixed-cup-tensor-normalization` owns `MixedCupTensorNormalization`: six elementary tensor equations, including every-good-representative reduction, identity localization, and the explicit common-stage closure representative. Its source is the same final coefficient-compatibility sentence, expanded by proof steps 2–9. The searches recorded in the node find no exact existing assembly; all individual operation, scalar, tensor and point-fibre constructions are reused.

`def-sf-mixed-cup-field-operations` owns `MixedCupFieldOperations`: the explicit normalized rational and common-stage operation isomorphisms. It is split from the field-coordinate module solely to bound elaboration time. Its sources and actual searches are recorded in its node.

`def-sf-mixed-cup-tensor-elementary` owns `MixedCupTensorElementary`: the
finite, completed integral and finite-field scalar tensor predicates. It imports
the recorded finite tensor model and integral/rational comparisons and defines
only their normalization equations. `def-sf-mixed-cup-tensor-closure` owns
`MixedCupTensorClosure`: the literal common-stage representative formula with
its fixed transition unitor. Its normalization uses HEq between morphisms whose
source and target objects are identified by the prescribed tensor-normalization
equalities; equality proofs provide no extra map choice. Its source is the
common-stage paragraph and coefficient compatibility sentence. Both use the
actual tensor-normalization searches recorded in their nodes; no existing node
packages these predicates. They are split from the tensor-normalization module
to respect the fixed compilation limit.

## Repair of the returned delivery

Compared against returned immutable head f591df956e53 and the live recorded
interfaces. H3: the former identity/composition/square-only cohomology witness
allowed a per-stage sign twist. The revised `Comparisons` includes component
equalities for every elementary passage, with both support choices. The ringed
maps are literally `PurCompactSupport.properComparison` and `comparison`, not
free isomorphisms. Integral support coordinates use `recordedIdentification`,
which is fixed by finite reductions. Point balancing sends b tensor x to the
actual sheaf tensor section and descends through both universal counits.
Field operations use the recorded rationalization, coefficientTransition and
commonStageComparison. Bridges between independently supplied normalized
SixFunctorDatum values are constructed through the specified integral
realizations, then rationalized. Scalar coefficient lifts are fixed on pure
tensors. Thus the independent per-(F,n) datum does not leave a sign choice in a
cohomology or tensor component. The unconstrained siteCongruence data is removed.
All six elementary tensor passage families have canonical component equations.

H2 of the first return: finite scalar balancing is selected inline from
scalarTensor_existsUnique. The second ownership return is repaired below by
a definition owner for that unique construction and recordedIdentification. The finite tensor-model owner is explicitly cited for
pullbackTensorFiniteModelIso. The item statement and proof are unchanged.

The helper modules are split to stay within the fixed per-file compile limit.
They contain real definitions and named, source-documented postponed existence,
uniqueness or domain theorems. The moduleDerived instance is the same standard
Grothendieck derived-category instance as in the accepted returned file; no new
derived category or universe identification is introduced. The overgeneralized
IntegralHom instance imported by the recorded reduction dependency is disabled
where it would leave a stuck universe during elaboration.

Additional search: each new owner node records actual LeanSearch and LeanFinder
queries plus Mathlib grep. Project rg in lean/WeilConjectures and lean/Sheaf found
no existing names for these combined normalization predicates or coordinate maps.
blueprint_refs.py search for coefficient comparison normalization returned zero.
The broader DAG search found lem-sfb-normed-point-derived-scalar-sections: it uses
internal modules over continuous normed-field coefficient sheaves, not arbitrary
finite/completed ringed module coefficients. Its interface cannot supply the
arbitrary nonflat finite-ring comparison needed here. The existing individual
ringed scalar, operation and fibre constructions are reused throughout.

## Second reading by Q72

The dispatcher explicitly forbids other agents; no independent second reader is
claimed. I reopened the node and the repaired modules for the clause-by-clause
audit above. The additional repair audit checked every elementary passage and
both support choices, including reduction of u_c, the omitted tensor families,
canonical point maps, nonflat finite quotients, equal fields, and independent
normalized operation data. The maintainer's independent review remains the
independent reading required by the dispatcher. No mathematical statement
correction is proposed.

## Ownership repair of immutable head 126ae4cf2bd6

H2 is repaired without altering any Lean file or the item statement. I compared
the retained delivery records with the live declaration signatures and current
definition-owner records. The compact-support theorem is removed from statement
dependencies of the item and all three helper nodes that cited it for definitions;
its uses as a proof prerequisite remain in proof_deps. The ringed and tensor
normalization nodes also replace the operation-reduction theorem's statement-data
citation with definition owners.

The item and ringed-normalization node now cite the landed definition owners
`def-pur-finite-compact-support-scalar-data`,
`def-sp-coefficient-mate-comparisons`, and
`def-sf-finite-tor-integral-inclusion`. These own finiteImageIso,
finiteReductionIso, finiteDirectImage_eq; reduction, completedChange,
properComparison; and coefficientPrimeUnit, respectively. The normalized point
scalar node directly cites the coefficient-mate owner for its integral reduction
and completed change. The field-coordinate node directly cites the finite-Tor
inclusion owner for coefficientPrimeUnit.

OperationScalarTransport already has the reviewed landed definition owner
`def-pur-operation-scalar-transport`; it is reused, not defined a second time.
The new constructible-restriction owner below cites that datum. The existing
restriction formula takes its T argument, composes the recorded ordinary-model
isomorphism with T.derived, and adds no scalar-isomorphism choice.

## New nodes added for the ownership repair

`def-sf-compact-support-scalar-tensor-identification` has existing:true and re-exports
Sheaf.Paper.IntegralCompactSupportCoefficientComparison, without a new module.
It owns scalarTensorTotal and its invertibility, scalarTensor and its determining
existence/uniqueness statement, recordedSupport, IsRecordedIdentification,
recordedIdentification and its determining existence/uniqueness statement. It
also records the ordinary pure-tensor balancing construction, uniqueness and
naturality used to define the signed total. Each arbitrary ring-sheaf map is
allowed; the derived normalization quantifies over every flat-term K-flat pair,
with the actual universal counits. The recorded-support normalization quantifies
over every input and every finite level and uses the fixed Roos projections.
The same elementary finite scalar tensor and recorded-identification data in
the accepted Lean statements are now definition-owned. No new mathematical
assertion is introduced.

`def-sf-constructible-operation-scalar-transport` has existing:true for
WeilConjectures.operationConstructibleScalarTransport in
Sheaf.Paper.BasicOperationsCoefficientReduction. Its hypotheses are exactly
prime ell, finite Q_ell-extensions E,L, embedding iota, scheme W, and the supplied
normalized transport T. Its single clause is the actual natural isomorphism
from constructible scalar extension followed by ambient inclusion to ambient
inclusion followed by completed derived scalar extension, constructed by the
recorded ordinary-model comparison and T.derived. The existing structure owner
is cited. Identity embeddings and arbitrary W introduce no extra hypotheses.

Searches for both records: actual LeanSearch and LeanFinder queries returned
eight unrelated declarations each; Loogle returned unknown-identifier/no hits;
Mathlib grep returned zero. Exact machine results are embedded in each node.
DAG and project rg found the existing structure owner and the two published
construction families, with no definition owner for the constructible restriction
or scalar-tensor/recorded-identification family. blueprint_refs.py searches for
scalar tensor recorded identification and constructible scalar transport returned
zero. Thus both new nodes reuse exact existing data, with no copied definitions.

Validation of the ownership repair: scompile.py checked all eleven delivered
Lean modules in dependency order against the live server build; exit status 0,
no errors or unexpected warnings. The two new existing:true signature records
were checked verbatim against the published source, and all helper statement
citations agree with their stmt_deps. Lean files remain unchanged from the
accepted mathematical formulation at the returned head.

## Repair of immutable head 375e0a415594

F1: new existing:true definition owner `def-sf-integral-tensor-finite-comparison`
re-exports WeilConjectures.integralTensorFiniteComparison from
Sheaf.Paper.IntegralOperationsPreserveConstructible. The recorded signature is
verbatim from the live source. The item and tensor-normalization node cite it;
the latter statement brackets it at the canonical reduction arrow. The node
introduces prime ell, finite E/Q_ell, arbitrary W, ambient inputs M,N, every good
pair P,Q, isomorphisms e,d, and each n. Its arrow is exactly the inverse homEquiv
applied to tensor(e.inv,d.inv), the recorded tensor representative comparison,
the actual Roos projection, and the inverse exact-restriction factorization.
No invertibility or constructibility assertion is added. Its only use of the
scalar-adjunction theorem is its normalized adjunction assertion, not an
unrelated helper definition. No comparison is inlined or redefined.

F2: `def-sf-mixed-cup-coefficient-passages` now cites the landed definition node
`lem-pod-point-sections-derived-reduction-data` in both statement and stmt_deps,
in place of the theorem used only for pointReductionQuotient. Its declaration
is the same coefficient quotient map in the same imported module chain.

The good representative predicate now cites its existing definition owner
`def-a1-flat-term-kflat-complex` in tensor-normalization and the item. The
moduleDerived instance is scoped to WeilConjectures.MixedCupCoefficientChange;
the remaining delivery modules explicitly open that scope. Its value, universe,
priority and uses are unchanged. The item statement, every comparison formula,
and proof_deps are unchanged from the returned head. The sources and current
landed owners were reread before applying these changes.

## New nodes for the finite tensor repair

`def-sf-integral-tensor-finite-comparison` owns exactly the published canonical
reduction arrow, with no new Lean module. It is valid for zero complexes, n=0
(exponent one), arbitrary representative isomorphisms, and schemes without an
invertibility assumption. The normalization uses every supplied good pair and
the actual Roos projection, so no sign or scalar-isomorphism choice is added.
LeanSearch and LeanFinder returned eight unrelated declarations; Loogle and
Mathlib grep returned zero matches. Exact results are embedded in the new node.
DAG/project rg found the published definition and its theorem-only ownership;
blueprint_refs.py found no node matching integral tensor finite comparison.
The existing construction is reused with existing:true.

Validation of F1/F2: scompile.py checked all eleven delivered Lean files in
order against the live published library, exit 0, with no errors or unexpected
warnings. Every individual compile was within the 60-second limit. The
instance-scope change passed through all ten dependent modules and the main
theorem. A separate metadata check verified the new existing signature verbatim
and the equality of helper-node bracket citations with their stmt_deps. The
current re-reading matched each new owner hypothesis and the full transpose
composite against the live declaration; no statement correction is needed.

The first dry run compiled the full delivery on the updated live branch, but
preflight's declaration scanner did not recognize the scoped-instance syntax.
The same moduleDerived value is now a named def registered with the scoped
instance attribute at priority 10000, preserving the exact value and scope while
using declaration syntax recognized by preflight.

## Delivery tool failure after successful repair validation

The corrected F1/F2 delivery passed dry run, commit 12c3d337b46, including
preflight and compilation. The subsequent delivery refreshed upstream overlay
dependencies and failed; a second authorized delivery attempt reproduced the
same failure. No commit was pushed. Both attempts used immutable overlay
snapshot 6fb4a4e7ce063918e141eb946bb58835491947f594d16958e34572b9e7dc0764.
EtaleSupportMapCompatibility failed at its imports because
WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf
redeclares AlgebraicGeometry.Etale.moduleLowerStar already imported from the
CohomPresheaf module. Live source inspection through scompile.py --source
confirmed FreeSheaf and FreeSheafCohomology still import CohomPresheaf.

The mandatory PodMixedSupportCupProduct import reaches the failing module via
PairingData, ConstructibleProjectionMates, FiniteRingConstructibleDerivedOrigin,
ProEtale.FiniteCoefficient.Derived.Perfect, Etale.Derived.Stability, SmoothDuality,
SfEtaleUnitTensorArbitraryBase, EtaleSumRightAdjointCoherence and
EtaleSupportExchangeRightMate. The delivery has no direct import of either
conflicting presheaf module to remove. The published cup and projection data
cannot be discarded or privately duplicated. The read-only upstream and
launcher-owned snapshot were left untouched. The remaining failure is in the
shared overlay compilation, after all requested ownership repairs and scoped
instance registration passed their dry run.

## Retry after the shared overlay failure (2026-10-25)

The retained repair was checked against the current main node: its statement,
proof and proof_deps remain identical. F1 has the existing:true owner
def-sf-integral-tensor-finite-comparison, cited by the item and bracketed in
the tensor-normalization statement. F2 cites the landed point-reduction data
owner instead of the theorem. The good-complex owner and scoped moduleDerived
registration remain in place. Existing signatures were checked verbatim again.

The refreshed server compilation now succeeds for all eleven supplied modules,
with no errors or unexpected warnings; all delivered files are within the
60-second limit. The earlier shared-overlay duplicate did not recur. The
historical tool failure above records the previous attempt only and is no
longer a compilation blocker.
