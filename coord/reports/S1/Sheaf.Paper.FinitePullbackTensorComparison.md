## What changed

Proved `WeilConjectures.pullbackTensorIndependent` directly from the K-flat representative
property. Proved `WeilConjectures.pullbackTensorFiniteRealization_existsUnique` by specializing
`AlgebraicGeometry.Scheme.openSquarePullbackModel_existsUnique` to the positive finite
coefficient quotient. Added its proof-only import. Constructed the tensor-model restriction
by whiskering the recorded comparison along the inclusion of flat-term K-flat complexes, and proved
uniqueness by tensor-functor equality and natural-transformation extensionality.

Proved `WeilConjectures.pullbackTensorSignedTotal_existsUnique` using the existing
`CochainComplex.Monoidal.braiding`. Two proved local helpers show that the ordinary
sheaf braiding swaps the sheafified pure tensors. The signed summand equation gives the
required generator formula; total-summand extensionality, the sheafification adjunction
and tensor extensionality prove uniqueness. Added the proof-only import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` for the existing tensor
instances and cochain braiding. All existing signatures and definitions are unchanged.
Moved the existing `pullbackTensorSiteSmall` instance before the representative proof so
its fixed coefficient universe is available during elaboration; its signature and body
are unchanged. The complete item module compiles cleanly with `lcompile.py` in
39.7 seconds. `leanindex.interface_changes` reports an empty list. The two helpers are local to the signed-total proof, so they introduce no top-level
declarations or public context commands. Its heartbeat allowance accounts for checking
the two sheafification calculations and the signed summand calculation together; the
60-second file limit is unchanged.

## Proved and sorry left

Closed 4 of the original 9 holes:
- `WeilConjectures.pullbackTensorIndependent`.
- `WeilConjectures.pullbackTensorFiniteRepresentative_existsUnique`.
- `WeilConjectures.pullbackTensorFiniteRealization_existsUnique`.
- `WeilConjectures.pullbackTensorSignedTotal_existsUnique`.

Added 0 holes and split off 0 theorems. The following 5 original holes remain, all recorded
by node `def-pur-finite-pullback-tensor-comparison`:
- `WeilConjectures.canonicalFinitePullbackTensor_associativity`.
- `WeilConjectures.canonicalFinitePullbackTensor_unit`.
- `WeilConjectures.canonicalFinitePullbackTensor_composition`.
- `WeilConjectures.pullbackTensorBraiding_existsUnique`.
- `WeilConjectures.canonicalFinitePullbackTensor_braiding`.

## No longer needed

Removed these proof-only imports, which neither the constructions nor the completed proofs
use; the remaining coherence statements already have their original public dependencies:
- `Sheaf.Paper.NormalizedDVRTower`.
- `Mathlib.Algebra.Homology.BifunctorShift`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`.
- `Sheaf.Paper.SfIntegralConstructible`.
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`.
- `Sheaf.Paper.SfDerivedComplete`.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.Paper.SfRationalizationKaroubi`.
- `Sheaf.Paper.NormalizedDVREffectivity`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`.
- `Sheaf.Paper.IntegralOperationsWellDefined`.
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`.
- `Sheaf.Paper.KFlatRingedToposPullback`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`.
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.Algebra.Homology.KFlatTotalTensorModel`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`.

These removals concern direct import edges. Publicly imported dependencies may still reach
some of these modules, so no claim is made that every listed module leaves target closure.
The node originally had no proof dependencies to remove. The total-tensor primitives
of `def-pc-tensor-complex-sheaves` remain in use through the cochain tensor import;
only its redundant direct Mathlib import was removed. Retained the proof import of
`Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` to preserve the unit route identified
by the delivery checker.

Node attachments for the removed direct imports (their modules may remain reachable
through public dependencies or other parents):
- `lem-pur-kflat-change-of-rings` (`Sheaf.Algebra.Homology.ChangeOfRingsKFlat`).
- `lem-pc-kflat-resolution` (`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`).
- `lem-pur-kflat-total-tensor-model` (`Sheaf.Algebra.Homology.KFlatTotalTensorModel`).
- `lem-weil-pbc-site-derived-tensor-descent` (`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`).
- `def-weil-cohomological-support` (`Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`).
- `prop-weil-pbc-proetale-constant-exact` (`Sheaf.AlgebraicGeometry.ProEtaleConstantExact`).
- `def-weil-proetale-inverse-image` (`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`).
- `def-weil-proetale-module-direct-image` (`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`).
- `lem-weil-pbc-ringed-topoi-module-pullback-tensor` (`Sheaf.CategoryTheory.ModulePullbackTensorIso`).
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit` (`Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`).
- `def-weil-algebraically-closed-coefficients` (`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`).
- `def-pur-integral-derived-operations` (`Sheaf.Paper.IntegralDerivedOperationsOnSlices`).
- `lem-pur-integral-operations-preserve-constructible` (`Sheaf.Paper.IntegralOperationsPreserveConstructible`).
- `lem-pur-integral-operations-scalar-extension` (`Sheaf.Paper.IntegralOperationsScalarComparisons`).
- `lem-pur-integral-operations-well-defined` (`Sheaf.Paper.IntegralOperationsWellDefined`).
- `def-weil-integral-scalar-extension` (`Sheaf.Paper.IntegralScalarExtensionUniverses`).
- `lem-weil-pbc-ringed-pullback-preserves-kflat` (`Sheaf.Paper.KFlatRingedToposPullback`).
- `lem-weil-pbc-ringed-topos-kflat-pullback` (`Sheaf.Paper.KFlatRingedToposPullback`).
- `lem-coef-normalized-dvr-effectivity` (`Sheaf.Paper.NormalizedDVREffectivity`).
- `def-coef-normalized-dvr-tower` (`Sheaf.Paper.NormalizedDVRTower`).
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` (`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`).
- `def-weil-derived-complete-integral-detailed` (`Sheaf.Paper.SfIntegralConstructible`).
- `def-weil-rationalization-karoubi` (`Sheaf.Paper.SfRationalizationKaroubi`).

## Where the brief, the DAG or earlier work was wrong

The node has no numbered proof plan (`proof` and `proof_deps` were empty), although this
module contains nine named proof obligations. The finite realization obligation duplicates
the existing unit-normalized pullback comparison over an arbitrary finite ring, so it needs
no new adjunction construction. The K-flat interfaces are definitionally the same here;
explicitly instantiating the equivalence lemma was unnecessary.

The signed-total obligation does not require new chain-map or sign constructions:
`WeilConjectures.Mathlib.Algebra.Homology.Monoidal` already proves the Koszul
braiding and its signed summand equation. The remaining work is its normalization
on the actual sheafified generators and uniqueness, both now proved here.

Process note: during the initial recovery I issued read-only git status/log inspections
contrary to the brief's prohibition on git commands in the shared repository. They
changed no project files. Subsequent compilation and delivery use only the required
launcher tools; all edits are in the assigned sandbox.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
