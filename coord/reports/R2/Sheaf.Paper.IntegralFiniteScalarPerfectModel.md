## What changed

Proved the assembly of AlgebraicGeometry.ProEtale.IntegralFiniteScalar.integralFiniteScalarPerfectModel from the source argument's independent parts. The original interface declarations move unchanged to Sheaf.Paper.IntegralFiniteScalarModelDefinitions and are publicly reexported by the item. This is required to state genuine substeps in separate module files without circular imports; it is not a timeout split.

Sheaf.Paper.IntegralFiniteTopologicalPresentation proves perfectModelArithmetic_of_finite_integral. It uses the already-proved Padic.finite_integral_condensed_resolution for the nonzero case, handles the zero ring with rank zero, proves the finite-power continuous-section biproduct identification by coordinate maps, and applies continuousSections_finiteDiscrete_shortExact. The actual F/G formulas and identity-underlying quotient identification are retained.

The two derived obligations are two theorems with separate nodes in the new module Sheaf.Paper.FiniteFreeScalarDerivedComparison: normalized beta/pullback/actual-mate comparison, and projection invertibility on a finite-free cone. The parent proves conservativity of exact derived restriction by cohomology, cancels the surrounding beta and restrictionPush isomorphisms, and concludes invertibility of gamma. No existing statement, target, definition body or universe changes.

## Proved and sorry left

Original holes closed: AlgebraicGeometry.ProEtale.IntegralFiniteScalar.integralFiniteScalarPerfectModel (lem-sfb-integral-finite-scalar-perfect-model), one of one original holes, by decomposition.

New proved declaration: AlgebraicGeometry.ProEtale.IntegralFiniteScalar.perfectModelArithmetic_of_finite_integral (lem-sfb-integral-finite-scalar-arithmetic). Its coordinate-module helpers and the parent's restrictionReflectsIsomorphisms helper are proved.

Two holes added, each the entire proof of its public theorem, each strictly part of the original argument:

- AlgebraicGeometry.ProEtale.IntegralFiniteScalar.derivedAssertions_of_finite_integral_resolution (lem-sfb-finite-free-scalar-derived-comparison): K-flat model, normalized beta, pullback square and actual mate equality; no projection/gamma invertibility.
- AlgebraicGeometry.ProEtale.IntegralFiniteScalar.finiteFreeScalarProjection (lem-sfb-finite-free-scalar-projection): projection invertibility for a cone of finite free point modules; no arithmetic, quotient, short exactness, beta or gamma conclusion.

Actual delivered textual hole count: 2. This is a decomposition, not a complete proof of the original mathematics; one upper hole is closed and two strictly lower holes are added.

## No longer needed

No existing node or module is withdrawn. All original public dependencies remain public through IntegralFiniteScalarModelDefinitions. The item no longer directly imports the old detailed proof dependencies; their use is represented in the two derived obligation nodes. The DVR and Smith-normal-form work is supplied through the existing proved lem-sfb-finite-integral-condensed-resolution rather than repeated. The original explicit inverse-by-diagonal-division argument is unnecessary for arithmetic: the existing theorem uses compactness and Hausdorffness for the kernel homeomorphism. The finite-sums/cone step of the unit route remains exactly the projection obligation.

The old private proof imports removed from the item are Mathlib.LinearAlgebra.FreeModule.PID, Mathlib.CategoryTheory.Triangulated.Pretriangulated, Sheaf.CategoryTheory.InternalSectionTensorComparison, Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients, Sheaf.NumberTheory.Padics.ExtensionIntegersDvr, Sheaf.Paper.ProfinitePointPullback, Sheaf.CategoryTheory.SitePullbackAbelianExact, Sheaf.Algebra.Homology.RingedDerivedTensorNative, Sheaf.Algebra.Homology.TotalTensorHomotopyConeSigns, Sheaf.Algebra.Homology.RestrictedKFlatTensorIdentification, Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients, Sheaf.Paper.KFlatScalarComparisonNormalization, Sheaf.Paper.KFlatRingedToposPullback, Sheaf.Paper.SectionDerivedPushpullNormalization, Sheaf.Paper.SectionDerivedTensorNormalization, Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations, Sheaf.Paper.RingedTopoiDerivedPullbackIndependent, and Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral. The lower derived-comparison proof plan still cites the appropriate corresponding nodes, so these are not claimed as globally pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG's arithmetic plan overlooks the already-proved finite_integral_condensed_resolution specialization. That theorem chooses card(A) generators even for the zero ring, whereas this item requires rank zero when A is subsingleton. The delivery handles that edge case explicitly rather than assuming the existing witness has rank zero. The continuous-sections theorem does accept arbitrary continuous linear maps between its ring carriers, so it can handle the O-linear matrix maps despite the parent's old proof text suggesting its ring hypotheses forbid this use.

No mathematical statement is disputed. The unit's finite-sums-and-cone route is retained. The interface extraction leaves every original declaration's signature and body unchanged and publicly visible; no target meaning changes.

## New nodes

- def-sfb-integral-finite-scalar-model-interfaces: attachment for the unchanged original interface now in IntegralFiniteScalarModelDefinitions; no new notion or mathematical construction.
- lem-sfb-integral-finite-scalar-arithmetic: proved arithmetic and condensed resolution prefix, with separate rank-zero treatment.
- lem-sfb-finite-free-scalar-derived-comparison: original steps 3--7 specialized to a given short exact finite free point resolution.
- lem-sfb-finite-free-scalar-projection: original step 8, independent of the resolution's quotient and exactness.

Change records: coord/changes/integral-finite-scalar-interface-move.md, coord/changes/integral-finite-scalar-arithmetic.md and coord/changes/integral-finite-scalar-derived-reduction.md.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Forced adaptations

None. (Reviewer fix: the delivery had replaced the whole content of the existing module Sheaf.Paper.FiniteFreeScalarProjection (group K8, node lem-pur-finite-free-scalar-projection) with finiteFreeScalarProjection. That deleted WeilConjectures.FiniteFreeProjectionExchange.finite_free_scalar_projection, which Sheaf.Paper.FiniteFreeProjectionExchange uses at line 248. The module is restored byte for byte, and finiteFreeScalarProjection is moved to Sheaf.Paper.FiniteFreeScalarDerivedComparison.)
