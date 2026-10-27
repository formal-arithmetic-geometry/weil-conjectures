## What changed

Proved three of the five original holes in `Sheaf.SixFunctors.CoefIntegralFiniteExtension`.
The public signatures and definition bodies are unchanged.

`completion_isIso` applies the existing finite-free completed-scalar comparison after
identifying intrinsic completeness with unrestricted completeness. The proved private
bridge uses `sfDerivedComplete_iff_legacy`; its auxiliary finite field is obtained
from a prime greater than l+1, so it imposes no condition on the scheme.

`extension_complete` transports the distinguished augmented Roos triangle from ordinary
extension through the specified completion isomorphism. Its resolution and quotient
maps are retained. A proved private helper performs this transport.

`dualizingDatum_nonempty` obtains a dimension bound, applies
`prop_coef_integral_dualizing`, and composes the normalized counit isomorphisms with
the proposition's coherent finite-term origins. The proof combines their two
transition equations using restriction functoriality and the adjunction inverse law.
It does not choose unrelated finite isomorphisms or alter any data construction.

Added the private proof import `Sheaf.Paper.SfDerivedCompleteLegacyComparison` and
recorded its dependency and the three completed auxiliary arguments in the existing
DAG node. The rest of the node's plan remains for the two untouched theorems.
The unit record has no prescribed realized steps and its route is unchanged.

Validation: remote single-file compilation passed after all three proofs were added.
A second remote compile checks the pruned private imports. Edge cases checked:
identity coefficient inclusion, zero objects, empty scheme (dimension bound allows
bottom), n=0 (the first quotient has exponent one), and arbitrary n≤m transitions.
No proof needs nonemptiness of X or a positive dimension.

## Proved and sorry left

Closed 3 original holes, with no holes added or split off:

- `WeilConjectures.IntegralFiniteExtension.completion_isIso`.
- `WeilConjectures.IntegralFiniteExtension.dualizingDatum_nonempty`.
- `WeilConjectures.IntegralFiniteExtension.extension_complete`.

The two original holes left unchanged, both owned by
`lem-coef-integral-finite-extension`, are:

- `WeilConjectures.IntegralFiniteExtension.u_existsUnique`.
- `WeilConjectures.coef_integral_finite_extension`.

This is partial progress on a module with several holes, as permitted by the brief;
no claim is made to have proved the full coefficient-comparison package. The named
dependency theorems may still depend on sorry; they are the stated inputs of stage 3.

## No longer needed

Removed these unused private imports (some are also available through unchanged
public imports):

- `Sheaf.Paper.IntegralConstructibleInternalHom`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`.
- `Sheaf.Paper.SfIntegralConstructible`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`.
- `Sheaf.Paper.SfDerivedComplete`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`.
- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`.
- `Sheaf.SixFunctors.FiniteDualizing`.
- `Sheaf.Paper.IntegralResidueTor`.
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`.
- `Sheaf.Paper.FiniteFieldFiber`.
- `Sheaf.Paper.FiniteTorAmplitude`.
- `Sheaf.Paper.NormalizedDVREffectivity`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`.
- `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus`.
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`.
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`.
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.
- `Sheaf.SixFunctors.IntegralDualizing`.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`.
- `Sheaf.Paper.FiniteCoefficientHomChange`.
- `Sheaf.Paper.SemilinearDerivedSections`.
- `Sheaf.Paper.FiniteFreeCoefficientExtension`.

No public imports removed. No node or whole module is claimed globally prunable:
the two open theorem proofs still need their recorded plan. The three completed
auxiliary proofs need no new split-off theorem. The old direct proof imports for
Hom, Tor amplitude, semilinear sections and finite coefficient extension were not
needed by these proofs or by elaboration of the existing file.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The DAG's completion paragraph
omitted the existing bridge between intrinsic and unrestricted completeness; that
bridge is now explicit. The coherent datum existence assertion follows directly
from the proposition's published counit and origin equations, including the actual
exceptional transition; no additional existence lemma is required.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
