## Reviewer corrections (2026-10-21)

The independent reviewer re-applied the corrections of the FIX at head 9f44006e, which this
re-delivery did not carry over; sentences below that say otherwise are superseded.

- OrdinaryFiniteP1Kummer keeps its live text: ordinaryFiniteConstant stays an
  abbreviation and ordinaryFiniteIntegralExt/ordinaryFiniteModuleExt are not added.
  The delivered def broke the unchanged consumer SupportedKummerSupportHomNaturality
  (type mismatch at line 297, failed rewrites at 1019 and 1033), which compiles
  against the published build. Its node def-asd-ordinary-finite-p1-kummer-class keeps
  its live record. No delivered module needs the change: all twenty delivered modules
  compile against the live OrdinaryFiniteP1Kummer.
- OrdinarySupportedCartierKummer and its B3/C3 support modules are not restored by
  this delivery: C3's landing of 2026-10-21 00:29 is the base and is used unchanged.
  The node records lem-asd-ordinary-supported-kummer, lem-asd-derived-single-unit-exact,
  lem-asd-supported-kummer-boundary-pullback, lem-asd-supported-kummer-boundary-scalar
  and lem-asd-supported-kummer-chern-realization keep their live records (the delivery
  had changed lean.by or tool_uses although their modules are unchanged).
- lem-asd-ordinary-supported-chern-normalization: the copied `reviewed` and
  `reviewed_proof` records of A7's removed landing are dropped.
- GeoCartierCycleClassDefs gains the instance geoCartierSourceConstant_isIso (recorded in
  def-sfb-geo-cartier-interface): the unclaimed user ProEtaleProjectiveLineTrace, changed in live
  at 10:44 after the earlier review, proves IsIso of geoCartierSourceComparison by unfolding and
  infer_instance, which fails once geoCartierConstant is a typed def. With the instance it
  compiles unchanged.
- The forced N1 adaptations of this re-delivery (CartierReductionData line 9,
  the private GeoCartierCycleClass import of CartierReductionSiteComparison, the rfl in
  CartierProIntegralScalar, the unfold/simpa normalization in CartierProIntegralDerivedUnit
  and CartierProKummerDerivedUnit) are kept: the originals fail against the changed
  interface (import cycle; unsolved goal at line 45; rcases "not an inductive datatype").

## What changed

Repair of the return at head 711481a06: list the two omitted direct users,
ProEtaleP1DiagonalComponents and OrdinaryFiniteClassArbitraryBase, in
T3-geo-cartier-interfaces.md under Users. Their existing declarations keep the
same constant objects, Tate lines and Ext types. This record-only return repair
changes no Lean signature or proof and adds zero holes. A current DAG scan also
adds the newer citer lem-sp-p1-diagonal-integrals-family to the existing
statement-change review list; its normalized diagonal construction still uses
the same supported-source comparison and constant/roots formulas. The refreshed
downstream table also lists all current transitive importers, including newer
projective-line modules and adopted-source consumers; none requires an edit.

Repair of return C-9f440: add all six omitted direct users to the interface
change record. Rebase the N1 comparison module to the current shared refactor, add its needed
private proof import of GeoCartierCycleClass, and apply the required one-line definitions-only import adaptation in
CartierReductionData, where that import now resides. The detailed proof and
profiling account below describes the retained delivery; references to the old
site-comparison import adaptation are superseded by this foundation adaptation.


Current return checks: CartierReductionData compiles in 33.2 s on its first full
check. CartierProIntegralResidueDerivedUnit and CartierProRootScalar compile unchanged
in 7.6 s and 6.0 s. The adapted CartierProIntegralScalar compiles in 10.8 s;
CartierProIntegralDerivedUnit in 38.8 s; CartierProKummerDerivedUnit in 32.8 s;
and the current CartierReductionSiteComparison in 19.5 s. All checks pass without
warnings. Byte-identical restored modules already in the current shared source
are omitted from the final Lean packet; their checking copies are retained outside lean/.
This return repair adds no new holes and closes no further holes beyond the
retained decomposition reported below.

A fresh current-source scan also lists five newer direct users in the change
records: ProjectiveLineDiagonalChernComponents, EtaleSupportedIntegralDerivedUnit,
SupportedIntegralResidueSequence, ComparisonConstantGenerator, and
ProjectiveLineDiagonalData. Their declarations retain the same referenced formulas.
All five compile unchanged against the repair, in 19.0 s, 7.4 s, 8.3 s, 6.5 s,
and 23.6 s respectively, with no warnings.

The first final preflight passed the source and user-record checks and requested
four newer node citations in sk-lem-geo-cartier.statement_change.citers.
The list now includes lem-sp-cartier-pro-integral-derived-unit,
lem-sp-cartier-pro-integral-scalar, lem-sp-cartier-pro-kummer-derived-unit, and
lem-sp-cartier-pro-root-scalar. Their signatures and mathematical meanings remain
unchanged; the necessary proof adaptations are detailed below.

Construct the simultaneous family in exists_geoCartierCycleClass from the unique
ordinary supported Kummer class, exact comparison inverse image and the inverse of
the specified supported-source comparison. Its Ext comparison equation follows by
cancelling that isomorphism. Prove source invertibility directly from the existing
qcqs ordinary comparison theorem. The original existence signature is preserved.

GeoCartierCycleClassDefs re-exports the original twelve interface names and adds the
named inverse-image commutation square. It also names the existing integral pro-etale
Ext smallness proofs as geoCartierIntegralExt and geoCartierModuleExt. The ordinary
caches ordinaryFiniteIntegralExt and ordinaryFiniteModuleExt are defined in
OrdinaryFiniteP1Kummer, so ordinary consumers see them through that public interface.
These proposition-only caches avoid rebuilding localization smallness in Ext composites. Typed
constant/Tate definitions and explicit
transparency boundaries avoid expanding sheaf data unnecessarily. The scalar-unit
predicate uses the existing derived-base-change API with the same Hom universal
property, by associativity. The original module publicly re-exports these definitions.

OrdinaryFiniteP1Kummer changes ordinaryFiniteConstant from an abbreviation to a
typed definition with the same formula, and names the two existing ordinary Ext
smallness proofs described above. No existing formula changes. OrdinarySupportedCartierKummer is restored
byte-for-byte from B3's reviewed landing cf48da8d1bd, including its complete main proof and
unique-boundary helper. The current CartierReductionData changes only its public
GeoCartierCycleClass import to GeoCartierCycleClassDefs, breaking the cycle without
changing any declaration. The current CartierReductionSiteComparison adds only
the private proof import of GeoCartierCycleClass. N1's current declarations and
complete proofs are preserved. No adopted source-library file is changed or withdrawn.

CartierReductionModulus proves exponent compatibility by an actual morphism of
Kummer sequences, its short-exact Ext naturality, the pure-tensor formula and
uniqueness of the ordinary relative boundary. Three genuine source obligations
remain separately stated: Chern normalization across comparison, arbitrary finite
coefficient extension, and Cartier-preserving pullback. Each has its own module,
node, source and complete proof in words. Each is only one part of the conclusion;
none rephrases the full existence theorem.

The cached-unit diagonal argument passes without warnings in 25.2 s, and the
shorter ordinary Chern-normalization proof passes without warnings in 44.3 s.
The three additional unchanged consumers GeoCartierCoeffExtension,
FiniteP1DiagonalKummerComponentFormula, and FiniteP1DiagonalChernComponents pass in
24.8 s, 39.1 s, and 31.5 s. EtaleDegreeZeroHom, OrdinaryFiniteClassInjectivity, and
VectorIntegrationLocalTraceCompatibility are also listed in the change record and
pass unchanged in 6.7 s, 27.0 s, and 11.6 s. The last check also compiles the unchanged
charts dependency (8.2 s), whose artifact was not yet in the published server build.
The final artifact-producing checks pass without warnings for
CartierReductionSiteComparison (24.5 s), GeoP1Cohomology (40.4 s),
OrdinaryFiniteClassComparison (39.6 s), SupportedDerivedUnitForget (28.7 s),
SupportedKummerBoundaryPullback (22.1 s), SupportedKummerBoundaryScalar (19.7 s),
and SupportedKummerChernRealization (39.9 s). Together with the Chern-normalization
check above, this verifies all six users named in the return. Unchanged copies used only
for checking are kept outside the delivered Lean source directory.

The next preflight identified one further current-branch consumer,
OrdinaryFiniteTwistTransportUniqueness. Its public-interface dependency is now
listed in the change record; its unchanged source compiles in 8.0 s. A fresh
source import scan also adds all seven remaining transitive ordinary-interface
importers to the user table, without claiming additional source adaptations.

An earlier repair restored B3's support after batch recovery. The current shared
source already contains OrdinarySupportedCartierKummer, DerivedSingleUnitExact,
SupportedKummerChernRealization, SupportedKummerBoundaryPullback and
SupportedKummerBoundaryScalar verbatim, so their identical Lean copies are omitted.
The final packet retains the generic expansion API in DerivedSingleUnit, its
SupportedDerivedUnitForget consumer, and the canonical derived-unit cache in
OrdinarySupportedKummerSystem. The original cache change record accompanies it.
The mathematical constructions are B3's reviewed work, not new T3 splits.
The previously checked A7 OrdinarySupportedChernNormalization consumer and its node
were also absent after batch recovery. Restore its unchanged signature with a shorter
proof composing the unit-forgetting and supported-Chern identities.
FiniteP1DiagonalAlpha gains a private generic pasting lemma for the cached units.
It expands the cache at abstract categories and applies the existing pasted-unit
argument, then specializes without expanding concrete sheaf-derived adjunctions.
The public signature and the composite-unit argument are unchanged.

The current return recheck compiles all 22 checked files successfully. The two
users named by the return compile unchanged: ProEtaleP1DiagonalComponents in
55.1 s and OrdinaryFiniteClassArbitraryBase in 44.1 s, with no diagnostics.
The main item compiles in 9.4 s; all other retained modules also pass within
60 seconds each. Checking copies of the two unchanged users are kept outside
lean/, so the delivery includes no edits to them.

## Proved and sorry left

The original item's one hole, AlgebraicGeometry.ProEtale.exists_geoCartierCycleClass,
is replaced by a complete assembly proof. This is a decomposition, not an axiom-free
proof of the target: one upper hole is closed and three lower holes are added
(net minus two before any change in imported baseline).

New proved declarations:
- AlgebraicGeometry.ProEtale.geoCartierIntegralExt and geoCartierModuleExt;
- AlgebraicGeometry.Etale.ordinaryFiniteIntegralExt and ordinaryFiniteModuleExt
  (all four are existing smallness facts);
- CategoryTheory.Adjunction.derivedSingleUnit_eq;
- AlgebraicGeometry.Etale.ordinary_supported_kummer_chern (restored with shorter proof);
- AlgebraicGeometry.Etale.geoCartierEtaleClass_spec;
- AlgebraicGeometry.ProEtale.geoCartierSourceComparison_isIso;
- AlgebraicGeometry.ProEtale.geoCartierCanonicalClass_comparison;
- AlgebraicGeometry.ProEtale.geoCartierCanonicalClass_modulus;
- six new private helpers, all proved (four modulus lemmas, Ext isomorphism
  cancellation, and cached-unit pasting).

The canonical data definitions contain zero holes. Their only choice selects a unique
Ext class from a theorem determining exactly that class.

Every added sorry:
- AlgebraicGeometry.ProEtale.geoCartierCanonicalClass_chern,
  node lem-sfb-geo-cartier-canonical-chern;
- AlgebraicGeometry.ProEtale.geoCartierCanonicalClass_scalar,
  node lem-sfb-cartier-reduction-scalar;
- AlgebraicGeometry.ProEtale.geoCartierCanonicalClass_pullback,
  node lem-sfb-cartier-reduction-pullback.

B3's ordinary_supported_kummer and ordinary_supported_kummer_uniqueBoundary
proofs are preserved byte-for-byte in the current source; that module has zero holes
and its unchanged Lean file is omitted from the final packet. OrdinaryFiniteP1Kummer
has zero holes before and after the definition repair. The two existing source holes
AlgebraicGeometry.Etale.supported_kummer_boundary_pullback
(lem-asd-supported-kummer-boundary-pullback) and
AlgebraicGeometry.Etale.supported_kummer_boundary_scalar
(lem-asd-supported-kummer-boundary-scalar) are unchanged and are not added by this
final packet. The current packet closes the one item hole and adds the three named
T3 obligations above. The return repair itself adds zero holes.

## No longer needed

The restored ordinary Chern-normalization proof removes its direct proof import of
OrdinarySupportedCartierKummer and its direct dependency on
lem-asd-ordinary-supported-kummer. It composes the two smaller proved realization
identities instead. The ordinary existence module remains needed by the canonical
Cartier construction and is not pruned.

The original eight public imports are re-exported by GeoCartierCycleClassDefs, so
the existence module keeps only that public interface import. The redundant direct
imports removed are ProEtaleInverseImage, ComparisonDerivedPullbackFixed,
OrdinarySupportedKummerBoundary, OrdinaryFiniteP1Arrows, EtaleFiniteTwistPullback,
Paper.RingedTopoiDerivedTensorPullback, source ProEtale.ConstructibleSheaf and source
ProEtale.Comparison.LowerStarAcyclic. Their public declarations stay re-exported.

The canonical construction does not directly import CartierReductionSiteComparison.
B3's ordinary theorem still requires SupportedCartierBoundaryExistence and therefore
CartierReductionData transitively; neither module is pruned. The current foundation
holds the pole-boundary and reduction-uniqueness helpers used by the ordinary proof.
The stronger cartier_reduction_site_comparison theorem, in CartierReductionSiteComparison,
is not a proof dependency of this construction. The foundation needs only the
Cartier definitions and now imports GeoCartierCycleClassDefs. Its former import
of the Cartier existence proof is the dependency removed to break the cycle.
This packet makes no withdrawal claim from the absence of current Lean importers.

The original main proof's following direct proof dependencies are no longer direct
dependencies of this proof (some remain transitively needed by the ordinary Kummer
construction and the three source obligations):

- def-pc-divisor-line-bundle
- def-sc-gm-torsor
- def-weil-pbc-direct-image
- lem-weil-pbc-etale-algebra-flat
- def-weil-pbc-flat-ring-map
- lemma-weil-pbc-finite-stalk-formula
- prop-weil-pbc-geometric-stalks-exact
- lemma-weil-pbc-geometric-stalk-conservative
- lem-weil-pbc-constant-sheaf-geometric-stalk
- lem-amb-kummer-any-base
- lem-sfb-divisible-extension-derived-reduction
- lem-sc-line-bundle-torsor
- lem-sc-torsor-h1
- lem-geo-cartier-coeff-extension
- lem-geo-cartier-exponent-independence
- lem-sfb-successive-derived-quotient-normalization
- lem-asd-finite-etale-twist-line
- lem-kun-kflat-criteria
- lem-kun-inverse-image-monoidal
- lem-kun-stalk-as-pullback
- prop-weil-pbc-inverse-image-modules-exact
- lem-kun-pullback-constant
- lem-weil-pbc-ringed-topoi-derived-tensor-pullback
- lem-sf-comparison-pullback-exact
- def-sf-comparison-derived-pullback
- lemma-weil-pbc-finite-direct-image-exact
- sk-thm-pe-direct-image-comparison
- lem-weil-proetale-module-direct-image-left-exact
- lem-weil-pbc-left-exact-injective-resolution-degree-zero
- prop-pur-kinjective-resolutions-exist
- lem-sp-grothendieck-enough-injectives
- sk-def-sfb-derived-extension-of-scalars

The corresponding obsolete top-level tool-use approvals removed, in their original
order, are:

- lem-weil-pbc-etale-algebra-flat
- lemma-weil-pbc-finite-stalk-formula
- lemma-weil-pbc-geometric-stalk-conservative
- lem-amb-kummer-any-base
- lem-sc-line-bundle-torsor
- lem-sc-torsor-h1
- lem-pur-derived-change-of-rings
- lem-asd-finite-etale-twist-line
- lem-kun-kflat-criteria
- lem-kun-inverse-image-monoidal
- lem-kun-stalk-as-pullback
- prop-weil-pbc-inverse-image-modules-exact
- lem-kun-pullback-constant
- lem-weil-pbc-ringed-topoi-derived-tensor-pullback
- lem-sf-comparison-pullback-exact
- lemma-weil-pbc-finite-direct-image-exact
- sk-thm-pe-direct-image-comparison
- lem-weil-pbc-constant-sheaf-geometric-stalk
- lem-weil-proetale-module-direct-image-left-exact
- lem-weil-pbc-left-exact-injective-resolution-degree-zero
- prop-pur-kinjective-resolutions-exist
- lem-sp-grothendieck-enough-injectives
- lem-sfb-successive-derived-quotient-normalization

The original unit has no separately pinned realized nodes. Its six steps are retained:
the pole extension and positive relative boundary through the ordinary Kummer
construction; exact comparison for its source and target; coefficient extension;
the dual-ideal Chern sign; and Cartier-preserving pullback. Only the auxiliary
modulus argument is replaced by direct Kummer-sequence naturality.

## Where the brief, the DAG or earlier work was wrong

The prior packet used stale OrdinarySupportedCartierKummer text and would have
reverted B3's landed proof. The current source preserves B3's reviewed module, whose identical Lean copy is omitted. Its boundary-existence dependency is necessary and remains in the DAG.
The current cycle is removed at the definitions-only import in the N1-held
CartierReductionData foundation. N1's current comparison module receives a private
proof import for its actual use of the existence theorem.

The project's default backward unifier ignores transparency annotations. The new
proof modules explicitly respect them. The ordinary constant was an abbreviation
of a large sheaf construction; making its type boundary explicit preserves its
formula and allowed the projection to compile within the ordinary file's limit.
The artifact-producing delivery compile exposed a separate N1 timeout at 60 s.
Profiling identified cartierProBoundary._proof_3 as the integral pro-etale Ext
smallness proof (8.8 s kernel time for cartierProBoundary, plus repeated public
interface linting). The four named Ext smallness instances address both integral and module coefficients
without changing N1's bodies: its artifact-producing compile passes in 24.5 s.
The interface module itself compiles with artifacts in 24.7 s.
No compiler time limit, safety setting or launcher script is changed.

The boundary predicate fixes an Ext class, so selecting its unique representative
is legitimate determined data. No unproved mere-existence witness is used to
supply arbitrary data.

## Forced adaptations

Sheaf.AlgebraicGeometry.CartierReductionData is held by N1. The current original
fails the import-cycle check with:
CartierReductionModulus -> GeoCartierCanonicalClass -> GeoCartierCanonicalEtale
-> OrdinarySupportedCartierKummer -> SupportedCartierBoundaryExistence
-> CartierReductionData -> GeoCartierCycleClass -> CartierReductionModulus.
Only line 9 changes:

```diff
-public import Sheaf.AlgebraicGeometry.GeoCartierCycleClass
+public import Sheaf.AlgebraicGeometry.GeoCartierCycleClassDefs
```

Every existing declaration, signature, visibility, attribute, proof and data body
in the foundation is preserved. CartierReductionSiteComparison is rebased to the
current shared file, preserving N1's newer factorization and complete proof.
Its original against the changed foundation fails at line 208 with
Unknown identifier exists_geoCartierCycleClass. Add only the private proof import
import Sheaf.AlgebraicGeometry.GeoCartierCycleClass after DerivedScalarExtUnitZero.
The ordinary boundary construction imports the foundation, so this proof import
introduces no cycle. No existing public import or declaration is changed.
The six direct users omitted by the return C-9f440 are now listed in the interface
change record: CartierProIntegralDerivedUnit, CartierProIntegralResidueDerivedUnit,
CartierProIntegralScalar, CartierProKummerDerivedUnit, CartierProRootScalar, and
CartierReductionData.
CartierProIntegralScalar (N1) additionally fails in private source_comparison_unit
with an unsolved goal after erw [← hh]: the final argument is the constant-sheaf
formula on one side and geoCartierConstant A D on the other. Add only rfl after
that rewrite. This closes their definitional equality and preserves every existing
signature and every other line. CartierProIntegralDerivedUnit and CartierProKummerDerivedUnit (both N1) report
that hcompat is not an inductive datatype at their original obtain because
GeoCartierScalarCompatibility is now irreducible. Add an explicit unfold before
that obtain. At the extracted unit, unfold GeoCartierScalarUnit and normalize
Functor.DerivedUnit, Sheaf.IsDerivedBaseChange, Sheaf.derivedRestrictScalars and
Category.assoc with simpa only, then use the normalized unit in the existing
composition argument. The original change tactic fails because the revised
predicate groups the first two composition factors. Existing signatures, visibility,
and all other proof lines stay identical. CartierProIntegralResidueDerivedUnit and
CartierProRootScalar remain unchanged.

The current shared OrdinarySupportedCartierKummer already contains B3's proved
text, so the byte-identical checking copy is omitted. This return makes no forced
adaptation to that module. Its declarations and complete proofs are preserved.
The ordinary constant repair is in an unclaimed module. The six additional users
from the return are now listed in the change record. The Chern consumer uses the
shorter proof described above; the others have unchanged bodies:
OrdinaryFiniteClassComparison, OrdinarySupportedChernNormalization,
SupportedDerivedUnitForget, SupportedKummerBoundaryPullback,
SupportedKummerBoundaryScalar, and SupportedKummerChernRealization.

FiniteP1DiagonalAlpha (unclaimed) originally fails at the final application of
isIso_pasted_units after unfolding the new cache: the left side contains
Adjunction.derivedSingleUnit while the expected morphism is the explicit derived
adjunction unit composite. Add the private generic isIso_pasted_single_units lemma, which expands
derivedSingleUnit_eq and uses the original generic isIso_pasted_units argument.
The final specialized application now uses that cached-unit helper and the two
constant sheaf comparisons. Local captured category proofs and respecting
transparency prevent expensive instance-proof conversions.
The compiler reported Type mismatch at that original final application.
OrdinarySupportedChernNormalization (unclaimed) exceeded 60 s while destructuring
the full ordinary theorem; its replacement composes the already proved two
realization identities. No signature or visibility changes.

## New nodes

- def-sfb-geo-cartier-interface: extracted ordinary-module objects and normalization diagrams.
- def-sfb-geo-cartier-canonical-etale: the uniquely normalized ordinary boundary class and its spec.
- lem-sfb-geo-cartier-source-comparison: invertibility of the specified supported source mate.
- def-sfb-geo-cartier-canonical-class: exact comparison construction and cancellation equation.
- lem-sfb-geo-cartier-canonical-chern: the positive Chern equation under the actual unit mate.
- lem-sfb-cartier-reduction-scalar: arbitrary finite coefficient compatibility of this class.
- lem-sfb-cartier-reduction-pullback: Cartier-preserving pullback with one normalized transport.
- lem-sfb-cartier-reduction-modulus: proved action of the specified normalized modulus maps.

The six restored B3 records retain their original sources, proof plans and Lean
attachments. Preflight requires the reintroduction's created/by metadata to name
T3 and this item; the restoration field preserves B3's original metadata and commit.
The records are: def-asd-derived-single-unit, lem-asd-derived-single-unit-exact,
lem-asd-supported-derived-unit-forget, lem-asd-supported-kummer-chern-realization,
lem-asd-supported-kummer-boundary-pullback, and lem-asd-supported-kummer-boundary-scalar.

The restored A7 node lem-asd-ordinary-supported-chern-normalization records the
shorter two-identity route and retains its original source and signature; its
restoration field preserves the A7 provenance.

Change records: coord/changes/T3-geo-cartier-interfaces.md and
coord/changes/supported-derived-unit-comparison-cache.md.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
