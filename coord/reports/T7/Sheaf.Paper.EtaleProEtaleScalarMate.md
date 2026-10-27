## What changed

Repair of returned delivery 9276d80929d (C-9276d, 2026-10-25): the independent
review passed, but landing rejected the basename supplied to --apply-fixes.
The report belongs at coord/reports/T7/Sheaf.Paper.EtaleProEtaleScalarMate.md;
Sheaf.Paper.EtaleProEtaleScalarMate.md alone is not a delivery path. This packet
retains the reviewed public statements and definitions, compares all eight source modules with current
sheaf-dag, and refreshes existing nodes from current metadata before reapplying
only the worker-owned fields. The replacement delivery performs a fresh server
compile and preflight on its fetched sheaf-dag base. The stored 2026-10-24 bad-import
build log predates this delivery and is not a failure of the reviewed packet.

The first replacement compile passed the four prerequisite modules but timed out
on the data module. The repair factors the reviewed private normalization calculation into proved
generic mate and representative-square lemmas, and applies unique_choice_eq to
the same canonical comparison. The normalization section uses the neighboring
derived modules' backward-definitional-equality elaboration settings. Public
statements, constructions and mathematical arguments are unchanged. (Reviewer correction:
the change of directImageComparisonAmbientPullbackIso to exactDerivedComparisonSquare
is reverted; its published five-factor body is kept.)

Proved all three original holes in Sheaf.Paper.EtaleProEtaleScalarMate.
The main equation applies the existing proved scalar/pullback cube and counit
transposes, uses injectivity of the geometric adjunction, then cancels scalar
extension of the A-comparison. No B-scalar mate is inverted and no extra
boundedness or flatness assumption is introduced.

The canonical comparison data move unchanged, with their proved private normalization
API, to EtaleProEtaleScalarMateData, publicly reexported by the original
module, to remove the cycle with the cube and transpose modules. Their proof
imports now name the data module. The original module retains forwarding
lemmas for its existing private import-all interface, so downstream consumers
keep their original sources. DerivedScalarRestrictionPullbackMate proves the
etale and pro-etale inverse scalar-mate isomorphisms by iterated mates, flat
resolutions and transport across canonical derived comparisons. A generic pointwise inverse-normalization lemma avoids expanding the concrete
site functors in the final uniqueness calculation. The ambient
comparison uses comparison-unit invertibility on bounded-below objects and the
existing qcqs direct-image isomorphism, then the iterated-mate criterion.

Added proved private representative equations and the generic exact-derived
restriction-square identity, with its inverse comparison factor already cancelled. The geometric representative retains its original
construction verbatim, so its consumers retain their original proofs.
EtaleUnboundedRestrictionComparison names the same categorical square and exact
representative formulas generically, so concrete site applications compare named
terms rather than expand localization constructions. Its existing comparison is
definitionally unchanged. The scalar representative names its previous inline cochain-unit composite as
scalarRepresentativeUnit, with identical construction after unfolding. The
coefficient pullback comparison factors its identical composite through
exactSingleCoefficientIso to avoid repeated concrete monoidal instance elaboration.
Change record: coord/changes/T7-etale-proetale-scalar-mate-data.md.

## Proved and sorry left

Closed the three original holes:

- AlgebraicGeometry.ProEtale.scalarPullbackReverse_isIso.
- AlgebraicGeometry.ProEtale.directImageComparisonAmbient_isIso.
- AlgebraicGeometry.ProEtale.etaleProEtale_scalar_mate.

Holes added: zero. Split off with sorry: zero. The new helper modules are proved.
The relocated definitions contain no holes. The main theorem retains its exact
original signature.

The existing hole AlgebraicGeometry.Etale.scalarTensorIso_existsUnique in
EtaleDerivedScalarTensor is unchanged (node lem-pur-derived-change-of-rings).
The independent compilation and delivery checks will record these dependencies;
they are not counted as holes closed by this item.

## No longer needed

No node or module is withdrawn. The original public imports are preserved directly
in the original module. The shared data module omits inherited imports of
ProEtaleConstantDerivedDirectImage, DerivedCategories, ComparisonDirectImageCanonicalMate,
ClassicalContinuityMap, LowerStarAcyclic, both derived UpperLowerStar modules,
Etale.UpperLowerStar.FlatModuleCat, RingedTopoiCanonicalTensorPullbackOfUniverses,
EtaleUnboundedRestrictionComparison, and Mathlib.Adjunction.Mates; their needed APIs
are already available through its retained imports. It omits the unused proof
imports DerivedChangeOfRingsCochainModel, ProEtaleConstantRingOperations,
ProEtaleDirectImageComparison, RingedDerivedMonoidalComparisons, and
Etale.Derived.LowerStarProjection. The cube and transpose proof imports now use
the data module to avoid the import cycle. The cube explicitly unfolds the new
name for its identical restriction square. Private normalization consumers retain their original imports through proved
forwarding lemmas in the item module.
The proof follows the recorded four-step parent route and needs both existing
cube and counit-transpose declarations. The separate general tensor comparison
and monoidal coherence nodes are not imported anew by the main assembly; their
existing uses by the canonical comparison helpers remain.

Unused private instance-cache wrappers cachedEtaleGroth, cachedEtaleSheafify,
cachedEtaleMonoidalPreadditive, cachedEtaleCoproducts, cachedEtaleColimits,
cachedEtaleFlatResolution, cachedEtaleInjectiveResolution, cachedEtaleExactColimits,
cachedEtaleTensor4, cachedEtaleTensor12, cachedEtaleTensor23,
cachedEtaleTensorColimits and cachedEtaleTensorFlipColimits
were removed from the item by the delivery, but Sheaf.Paper.AffineCounitScalar uses them
through `import all`; the review restores them in the item module. The private scalarRightAdjoint
cache is retained in the shared data normalization section. The generic private
complex_square_hom, square_cochain_fac and representative_eq proofs now live next
to the representative API that uses them. No mathematical node is pruned.

## Forced adaptations

- Sheaf.Paper.EtaleProEtaleScalarPullbackCube and Sheaf.Paper.EtaleProEtaleScalarCounitTransposes
  (unclaimed): the item now imports both, and both imported the item, so the original modules
  form an import cycle with the proved item. Changed lines: `public import` and `import all` of
  Sheaf.Paper.EtaleProEtaleScalarMate become the same imports of Sheaf.Paper.EtaleProEtaleScalarMateData,
  where the declarations they use now live unchanged; the cube also sets `Elab.async false`.
- Sheaf.Paper.EtaleUnboundedRestrictionComparison, Sheaf.Paper.ScalarPullbackRepresentativeData and
  Sheaf.Paper.EtaleDerivedScalarTensor (unclaimed): not forced; new generic definitions and
  private equations are added for the speed of the new proofs. scalarCoefficientPullbackIso is
  factored through exactSingleCoefficientIso (identical after unfolding).

## Reviewer correction (independent review of 9276d80929d2)

The delivery had rewritten the bodies of Etale.scalarRestrictionPullbackIso (through
exactDerivedComparisonSquare) and Etale.scalarExtensionRepresentative (through
scalarRepresentativeUnit) and dropped the private cachedEtale* wrappers. Eleven downstream
modules that compile against the published library then failed (EtaleCounitScalarModel,
EtaleOpenScalarExchange, DerivedScalarExtensionLocalSystems, EtaleSumCounitScalar,
ProperOpenCoefficientMate, EtaleOpenTensorDefs, FiniteCoefficientDirectImage,
ExceptionalCoefficientMaps, ExceptionalCoefficientUnitCoherence, EtaleHomComparisonModels,
AffineCounitScalar). The review restored both published bodies verbatim (the new names stay as
separate definitions, equal by `rfl`), reverted the cube's unfold list, and restored the
thirteen wrappers in the item module; all seventy users then compile.

## Where the brief, the DAG or earlier work was wrong

The already-proved cube and counit-transpose modules imported comparison definitions
from the item itself. Directly importing those planned dependencies creates a
cycle; sharing the unchanged comparison data is necessary. The prior ambient
invertibility hole requires arbitrary discrete coefficients and ambient derived
objects; the existing comparison adjunction and qcqs comparison iso provide that
argument without a finiteness hypothesis. A source-only DAG traversal also finds
the pre-existing exchange-replacement / termwise / unbounded-transport /
bounded-comparison cycle; this packet does not change those nodes.

## New nodes

lem-sfb-proetale-scalar-pullback-mate-invertible records the fully proved inverse
scalar-mate isomorphisms on both sites. Its source is the constant-ring
specialization of flat-resolution pullback and normalized derived scalar change.

lem-sfb-scalar-site-comparison-normalized-data records the relocated canonical
data, their proved scalar invertibility and normalization, and the bounded-below
ambient comparison invertibility. The original definitions and theorem signatures
are unchanged; this node owns the shared module needed to remove the import cycle.

Change record: coord/changes/T7-etale-proetale-scalar-mate-data.md.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer correction (independent review of 3d8a79c3924f)

This replacement was built from the uncorrected 9276d80929d files, so the corrections of
the review of 9276d80929d2 above were lost; the review re-applies them. It also restores the
published body of directImageComparisonAmbientPullbackIso, which the replacement had routed
through exactDerivedComparisonSquare (OpenProEtaleCounitScalar unfolds the published
composite). The new private normalization lemmas are kept.
