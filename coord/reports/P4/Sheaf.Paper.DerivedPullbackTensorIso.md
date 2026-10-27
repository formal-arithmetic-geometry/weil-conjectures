## What changed

Lifted the integral associator, braiding, and both unitors through the already proved
fully faithful coherent-reduction functor. The proofs conjugate the corresponding
system isomorphism by the specified tensor and unit reduction isomorphisms, then
use fullness for existence and faithfulness for uniqueness. Proved private
categorical helpers encapsulate this argument. Existing statement and definition
signatures are unchanged.

Proved the integral unit's constructibility and counit invertibility using the
normalized completed-operation model and the reconstruction theorem. A proved
private lemma transports normalization under system isomorphisms. Another explicit
comparison identifies finite evaluations of the unit with the constant coefficient
object, giving constructibility and uniform cohomological support in [0,0].

Proved rational associativity and braiding coherence by explicitly transporting the object equalities
of rational pullback and tensor, applying their prescribed action on localized
integral maps, and mapping the integral coherence equalities through localization. For associativity, the
bilinear tensor map law handles tensor products of localized integral arrows.

## Proved and sorry left

Closed eight existing holes, with zero holes added and zero split off:

- `WeilConjectures.pullbackTensorIntegralAssociator_existsUnique`
- `WeilConjectures.pullbackTensorIntegralBraiding_existsUnique`
- `WeilConjectures.pullbackTensorIntegralLeftUnitor_existsUnique`
- `WeilConjectures.pullbackTensorIntegralRightUnitor_existsUnique`
- `WeilConjectures.canonicalRationalPullbackTensor_braiding_spec`
- `WeilConjectures.canonicalRationalPullbackTensor_associative_spec`
- `WeilConjectures.pullbackTensorIntegralUnit_constructible`
- `WeilConjectures.pullbackTensorIntegralUnit_counit`

The following eleven original holes remain, all attached to
`lem-pur-derived-pullback-tensor-iso`:

- `WeilConjectures.pullbackTensorCommonComposition_existsUnique`
- `WeilConjectures.pullbackTensorCommonAssociator_existsUnique`
- `WeilConjectures.pullbackTensorCommonBraiding_existsUnique`
- `WeilConjectures.pullbackTensorRationalScalarUnit_existsUnique`
- `WeilConjectures.pullbackTensorCommonLeftUnitor_existsUnique`
- `WeilConjectures.pullbackTensorCommonRightUnitor_existsUnique`
- `WeilConjectures.canonicalIntegralPullbackTensor_associative_spec`
- `WeilConjectures.canonicalCommonStagePullbackTensor_associative_spec`
- `WeilConjectures.canonicalIntegralPullbackTensor_braiding_spec`
- `WeilConjectures.canonicalCommonStagePullbackTensor_braiding_spec`
- `WeilConjectures.derivedPullbackTensorIso`

The four integral constraint proofs use the already proved
`integralSystemReduction_fullyFaithful`; the specified reduction comparisons still
use their existing named prerequisite theorems. No axiom or hollow definition was
introduced. The complete eight-hole proof packet compiled with lcompile.py in
47.7 seconds (result adbd1b78d4b31e7a184ab994). Final independent whole-file
validation is recorded by the delivery tool. Local transparency
settings prevent repeated unfolding of chosen operation implementations during
statement checking; they do not alter any definition or public attribute.

## No longer needed

The four lifts require no new resolution construction, cochain computation, or
individual finite-evaluation faithfulness assertion. Their route uses coherent
full faithfulness directly. No node or module is withdrawn, because the other
eleven holes still follow their original planned arguments.

Removed the following private imports from this module; their declarations are
not used by its current proof bodies (public statement imports are preserved):

- `Mathlib.Algebra.Homology.BifunctorShift`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatTotalTensorModel`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.Paper.CoefficientExtensionReductionModel`
- `Sheaf.Paper.CompletedOperationTowerSubstitution`
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`
- `Sheaf.Paper.IntegralCoherenceTower`
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`
- `Sheaf.Paper.IntegralOperationsScalarComparisons`
- `Sheaf.Paper.IntegralOperationsWellDefined`
- `Sheaf.Paper.IntegralScalarExtensionUniverses`
- `Sheaf.Paper.IntegralTowerLimitComparison`
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Paper.NormalizedDVREffectivity`
- `Sheaf.Paper.NormalizedDVRTower`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.ScalarExtensionTowerCoherence`
- `Sheaf.Paper.SfDerivedComplete`
- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.Paper.SfRationalizationKaroubi`
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The original constraint docstrings already
specified the full-faithfulness argument, but the item did not use the library's
completed coherent-reduction theorem. This delivery supplies that argument in Lean.
The current parent proof remains unfinished; the original finite normalization,
quotient realization, and coefficient descent dependencies therefore remain needed.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
