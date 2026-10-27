## What changed

Proved `WeilConjectures.finiteCoefficientClosedShriek_naturality` and
`WeilConjectures.finiteCoefficientLocallyClosedShriek_naturality` without changing
any existing signature, definition body, or public import.

Closed naturality applies the existing relative exceptional Hom bijection. Its inverse
is ordinary closed pushforward followed by the specified counit. Naturality of that
counit and of the inverse ordinary coefficient comparison identifies the transposes.
The main closed comparison theorem supplies the normalization equations, invertibility
of the ordinary comparisons, and their required finite-Tor domains.

Locally closed naturality first proves that the published derived inverse image
preserves the actual finite-Tor predicate. It translates bounded constructibility
through the already proved `intrinsic_bc_realization_iff` helper (accessed by a private
`import all`) and translates the Tor interval through the proved intrinsic transport
lemma. The source library's pullback preservation then applies. The proof pastes closed
naturality on the restricted morphism with naturality of `finiteClosedScalarPullIso.inv`.

Added four proved private helpers for counit naturality, counit-transpose injectivity,
inverse ordinary-comparison naturality, and pullback preservation. No new public
statement or hole was added. Updated the existing node's proof description to distinguish
the proved naturality clauses from the remaining obligations. The unit has empty
`realized.statement` and `realized.steps`; its route is unchanged.

The required remote single-file compiler accepted the final module without warnings
(21.5 seconds). All 21 existing non-theorem declarations and all public imports were
compared against the source and are unchanged.

## Proved and sorry left

Original holes: 8. Closed: 2. Added: 0. Remaining: 6.

Closed by declaration name:

- `WeilConjectures.finiteCoefficientClosedShriek_naturality`.
- `WeilConjectures.finiteCoefficientLocallyClosedShriek_naturality`.

The following existing named theorem holes remain unchanged, all attached to
`lem-coef-finite-closed-shriek`:

- `WeilConjectures.finiteCoefficientClosedShriek`.
- `WeilConjectures.finiteCoefficientClosedShriek_comp`.
- `WeilConjectures.finiteCoefficientClosedShriek_coefficientChain`.
- `WeilConjectures.finiteCoefficientLocallyClosedShriek`.
- `WeilConjectures.finiteCoefficientLocallyClosedShriek_coefficientChain`.
- `WeilConjectures.finiteCoefficientLocallyClosedShriek_comp`.

The two closed holes are proofs from existing declarations; the first still depends on
the existing main closed comparison theorem. This is a partial delivery of two of the
module's eight holes, not a claim that the complete comparison theorem is axiom-clean.
No decomposition or split-off statement was introduced.

## No longer needed

Removed unused private proof imports:

- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel`.
- `Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`.
- `Sheaf.Paper.ComparisonTorAmplitude`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`.
- `Sheaf.Paper.DerivedPullbackTensorIso`.
- `Sheaf.Paper.EtaleKFlatCriteria`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`.
- `Sheaf.Paper.FiniteDirectImageComposition`.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`.
- `Sheaf.Paper.PullbackTorAmplitude`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.Paper.SfLocalizationAllStages`.
- `Sheaf.Paper.SfPreservationClass`.
- `Sheaf.SecSmoothPurity.ClosedUnitAllStages`.
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`.
- `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`.

These modules are not required as direct imports for the two completed proofs or the
existing constructions. Some remain transitively available through the preserved public
imports. No module is withdrawn, and no existing source-library declaration is removed.
The dependencies of the still-unproved comparison and cocycle clauses remain recorded
in the DAG; none is claimed globally obsolete.

For the closed naturality clause, `lem-coef-closed-transpose-cocycles` is unnecessary:
the existing relative Hom equivalence gives a direct proof. For locally closed
naturality, `lem-coef-locally-closed-scalar-pasting` and
`lem-coef-open-scalar-adjunction-counit` are unnecessary: naturality of the already
constructed open isomorphism suffices. Those nodes remain needed by other clauses.

## Where the brief, the DAG or earlier work was wrong

Several stated dependencies cannot simply be imported into this module:
`Sheaf.Paper.LocalizationScalarUnit` and `Sheaf.Paper.LocallyClosedScalarPasting`
already import `Sheaf.Paper.FiniteClosedShriek` for its canonical constructions.
Their own node/interface documentation acknowledges this direction. Importing them
back would create a module cycle. No such cyclic import was added. The two naturality
proofs avoid this issue directly. Finishing the main localization assembly may require
moving the existing canonical constructions into a common prerequisite module while
preserving their public re-export and definitions.

LeanFinder found eight ordinary scheme-restriction identities, with no exceptional
coefficient-exchange theorem. Loogle's conjugate-equivalence search found the standard
mate API. The required Mathlib grep returned no exceptional-image declaration; source
search found the already proved relative exceptional Hom equivalence and pullback
preservation, which the proofs use.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
