## What changed

Replaced the item’s single existence hole by the explicit assembly of the published raw rational realization, Hom comparison, finite-cone model theorem, localized t-structure and scalar coherence. The proof constructs the pointwise continuous-coefficient encoding, identifies the scalar actions, derives the integral comparison from the fraction formula, proves the image and heart clauses, and pastes the t-exact cohomology comparison.

Moved all 28 existing data declarations verbatim into `Sheaf.Paper.ContinuousRationalRealizationData`, publicly reexported by the original module. This permits supporting comparison lemmas to use the original structures without importing the existence theorem. All existing public names, signatures and definition bodies are unchanged. The change record includes the complete old/new text and consumer inventory.

Five separate supporting statements isolate the continuous finite-free criterion, filtration quotient models, actual normalized pullback transport, slice restriction transport and coherence of prescribed normalized comparisons. Each records its source argument and edge cases. They preserve actual tensor units, universal derived counits, reflector completion units and raw scalar associators.

## Proved and sorry left

Validation: all seven delivery modules compiled together. After replacing the unavailable degree-reflection dependency, the revised main module compiled cleanly (12.8 seconds); the finite-free criterion also compiled separately (14.1 seconds). All 28 extracted data declarations were checked byte-for-byte against the shared source. The import graph has no cycles and every direct proof import now has source.

The degree-bound helper was also rewritten to use the localized t-structure and full faithfulness directly, removing the unavailable `RationalRealizationDegreeReflection` source module from the packet.

The item originally contained one hole: `AlgebraicGeometry.Scheme.ContinuousRational.continuous_rational_derived_realization`. Its assembly proof is complete Lean from the named supporting results. This is a decomposition, not a net proof of the target closure.

The new `AlgebraicGeometry.Scheme.ContinuousRational.rationalContinuousFiniteFreeCriterion` is fully proved: finite bases identify the additive continuous constant models with finite free sheaves; normalized scalar transport identifies local models on every stratum. Its proof uses the stronger inverse-image isomorphism for totally disconnected coefficient rings, so it does not require pointwise normalization of the given coefficient isomorphism.

Four holes are added, each the entire proof of a named theorem in its own module:

- `AlgebraicGeometry.Scheme.ContinuousRational.rationalContinuousFiltrationModels` — `lem-per-rational-continuous-filtration-models`.
- `AlgebraicGeometry.Scheme.ContinuousRational.rationalContinuousPullbackTransport` — `lem-per-rational-continuous-pullback-transport`.
- `AlgebraicGeometry.Scheme.ContinuousRational.rationalContinuousSliceTransport` — `lem-per-rational-continuous-slice-transport`.
- `AlgebraicGeometry.Scheme.ContinuousRational.rationalContinuousComparisonCoherence` — `lem-per-rational-continuous-comparison-coherence`.

The packet replaces one original hole with four named holes and proves one new supporting theorem. This is a decomposition with three more holes in the changed files; it does not claim a net proof of the target closure.

No definition has a hole. No new axiom, unsafe code or bypass is introduced. The existing dependencies may themselves be unfinished, as intended by stage 3.

## No longer needed

The finite-free criterion uses the already proved general totally disconnected coefficient inverse-image isomorphism instead of the older immersion-only coefficient restriction lemma. The missing degree-reflection module is no longer needed: its bound conclusion is proved directly from `pbc_localized_tstructure`, the realization cohomology comparison and full faithfulness. The degree-reflection node/module is unused by this proof; its declaration and DAG attachment are retained. The stratum, pullback, slice and coherence dependencies remain needed through the supporting transport statements. No unit route is bypassed and no source-library declaration is removed. The following old direct proof imports are removed from the item; relevant material is imported by its actual consumer instead:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `Mathlib.CategoryTheory.Triangulated.Triangulated`.
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.CategoryTheory.DerivedCountableSumsExact`.
- `Sheaf.CategoryTheory.DirectedTriangulatedImage`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`.
- `Sheaf.CategoryTheory.LocalizationInverseImageCoherence`.
- `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom`.
- `Sheaf.CategoryTheory.ScalarLocalizationTriangulated`.
- `Sheaf.Paper.AdicCoefficientDatum`.
- `Sheaf.Paper.ConstantCompletionEquivalence`.
- `Sheaf.Paper.ContinuousCoefficientRealizations`.
- `Sheaf.Paper.FiniteModelStratumFiltration`.
- `Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness`.
- `Sheaf.Paper.IntegralTStructure`.
- `Sheaf.Paper.IntegralUniformCoefficient`.
- `Sheaf.Paper.IntrinsicCompletionCompleted`.
- `Sheaf.Paper.LisseEConstructibleIntegralLattice`.
- `Sheaf.Paper.PbcRationalCategory`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.Paper.SfCommonStageWeilCohomology`.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`.
- `WeilConjectures.ConstructibleSheaf.Pullback`.

## Where the brief, the DAG or earlier work was wrong

The degree-reflection source module is missing from the shared checkout, although its DAG attachment remains and the last green compiled library still supplies its declaration. There is no rework row or quarantine source for it. The assembly now proves the required bounds directly and removes that import.

The recorded proof dependencies use different but normalized presentations from the final statement. In particular the pullback comparison includes an identity coefficient tensor and strict quotient-tower completion, while the item uses ordinary inverse image with that identity tensor cancelled and the actual completion reflector. The slice comparison uses literal site restriction, whereas the item records the slice equivalence explicitly. Those transport arguments must retain the section and counit equations; an arbitrary unnormalized functor isomorphism would be insufficient.

The finite-cone theorem requires actual degree-zero integral quotient models in its Filtration record. The stratum integral-model statement supplies normalized completed-model and coefficient presentations instead. The filtration support lemma records the conversion, rather than treating the interfaces as definitionally equal.

The localized cohomology field uses double truncation followed by shift. The degree-reflection declaration’s displayed cohomology comparison puts the shift first; the assembly instead uses the canonical t-exact comparison and a proved ambient double-truncation/homology isomorphism.

## New nodes

`def-per-continuous-rational-realization-data` is an existing ownership node, updated only in its Lean module/file attachment. All of its mathematical fields and ownership metadata are preserved.

`lem-per-rational-continuous-finite-free-criterion` is the field-coefficient local-model criterion, including normalized coefficient and finite-stratification transport.

`lem-per-rational-continuous-filtration-models` converts the integral stratum construction to the degree-zero quotient models consumed by the existing finite-cone proof.

`lem-per-rational-continuous-pullback-transport` retains the ordinary tensor and actual completion normalization in the geometric pullback comparison.

`lem-per-rational-continuous-slice-transport` compares ordinary pullback with the exact restriction associated to the actual pro-etale slice, without a finiteness assumption on the site object.

`lem-per-rational-continuous-comparison-coherence` proves the identity, composition, scalar-tower and mixed equations for already prescribed normalized comparisons.

Change record: `coord/changes/E6-continuous-rational-realization-data.md`.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
