## What changed

Proved AlgebraicGeometry.ProEtale.FiniteModelQuotient.cohomology_descent from the supplied local
calculation and existing exactness, scalar-resolution and sheaf-detection theorems. The proof
keeps the original finite constructible strata and covers. Their scalar kernel and cokernel models
give constructibility; their zero models in every other degree give vanishing. Finite
quasi-compact jointly surjective module pullbacks detect zero directly, including the empty family
over an empty scheme. No unit realization is bypassed.

Added the proved integral_scalar_model_coordinates theorem in
Sheaf.Paper.IntegralScalarModelCoordinates. It compares the internal finitely presented scalar
model with an ordinary finitely presented integral module model using the existing
continuousScalarFinitePresentation and matrix/cokernel comparisons.

Reorganized the auxiliary definitions in Sheaf.Paper.FiniteModelSheafQuotientData to avoid
expensive kernel normalization. ChartCalculation records precisely the original seven conjuncts.
LocalCalculationAt records their universal chart property, explicitly indexed by the complex;
LocalCalculation specializes it to the actual reduction. Named category, encoding, pullback and
homology coordinates use the existing structures and functors. The quotient inverse image uses the
definitionally equal native finite-discrete coefficient presentation. No coefficient action,
topology, quotient map or reduction is changed. The item public signature is preserved verbatim; a
definitional goal conversion introduces the named coordinates only inside its proof. The parent
Sheaf.Paper.FiniteModelSheafQuotientConstructible constructs the records and uses the typed
encoding/homology APIs; its public statement stays unchanged. No Challenge declaration or adopted
WeilConjectures declaration is edited.

The change record is coord/changes/P3-finite-model-quotient-coordinate-representation.md. It
includes the old and new definitions/signatures and their consumer list. The independent reader
must check their equivalence; a global build remains the maintainer's responsibility.

## Proved and sorry left

Closed 1 of 1 original holes: AlgebraicGeometry.ProEtale.FiniteModelQuotient.cohomology_descent
(node lem-sfb-finite-model-quotient-cohomology-descent).

Also proved the new theorem
AlgebraicGeometry.ProEtale.FiniteModelQuotient.integral_scalar_model_coordinates (node
lem-sfb-integral-scalar-model-coordinates). Added 0 holes, split off 0 statements; no sorry
remains in any delivery source. All helpers in the item are proved and its scalar cohomology model
is an explicit construction. Existing imported obligations are used as permitted by stage 3; this
report does not claim those obligations are closed.

Complete diagnostic versions compiled in 50.2 and 51.5 seconds after replacing a local
chart-morphism alias by its composite directly. All eight final packet sources and direct
consumers compiled together in import order without errors or warnings (result
65ca9fbdda3b2a10db53ebc6). The four unchanged consumer sources needed no adaptation after
rebuilding their private helpers against the new coordinates. The original public signature was
also checked against the proved canonical-coordinate statement in 6.4 seconds (result
e000152b683c451fa8121eba). The delivery tool records final compilation and axiom checks. No test
changes any compile-time or heartbeat limit.

The final proof with the original statement compiled in 20.4 seconds
(result e4e743a7d7b3085e88c17950); its sole unused-parameter warning was then removed.
The delivery tool checks the complete final packet and its axioms.

## No longer needed

Removed the planned dependencies lem-fix-constructible-open-closed-refinement and
lem-exc-open-closed-detection: the proved generic module-sheaf detection theorem directly handles
the finite quasi-compact stratum immersions. Therefore no direct import of
Sheaf.SixFunctors.ConstructibleOpenClosedRefinement or
Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection is needed. No such module or declaration is
withdrawn or removed from the source library.

Replaced the direct lem-sfb-scalar-finite-free-resolutions dependency by the existing proved
scalar_resolution in Sheaf.Paper.FiniteConstantModelResolution, recorded by
lem-sfb-finite-constant-model-two-term-free-resolution, specialized to the integral DVR. The
direct lem-pe-finite-discrete-scalar-constant-models dependency is replaced by the ordinary
cohomology and finite-discrete constructibility comparisons. Its module can remain a transitive
dependency of those comparisons; no global withdrawal is claimed.

The original public import Sheaf.Paper.FiniteModelSheafQuotientData is retained. The normalized
encoding-pullback comparison remains a direct proof dependency because it transports the chart
comparisons to ordinary sheaves. No unused proof import remains.

## Where the brief, the DAG or earlier work was wrong

The planned open/closed refinement is unnecessary: the adopted source already proves finite
quasi-compact jointly surjective detection for module sheaves. An abelian-sheaf specialization
would lose the needed coefficient action, so the DAG now explicitly names the generic module-sheaf
theorem. The DAG also omitted the integral scalar-coordinate bridge needed to apply its stated
scalar resolution; that bridge is proved here.

Concrete category expressions and a local alias for the chart composite caused expensive kernel
conversions even though the mathematical isomorphisms already checked separately. The
representation repair and consistent composite expression remove those conversions. The hypotheses
and all three conclusions are preserved, including zero matrix ranks, empty schemes and empty
stratifications. No Noetherianity, completeness or extra property of stratum immersions is
assumed.

## New nodes

lem-sfb-integral-scalar-model-coordinates records the new proved theorem in
Sheaf.Paper.IntegralScalarModelCoordinates. Its source is the Local models paragraph of the
current integral ctf-equals-bc proof. The Mathlib searches found generic finite presentation and
cokernel APIs; the project's existing scalar-matrix comparisons and
continuousScalarFinitePresentation give the comparison. It introduces no sorry.

lem-sfb-finite-qc-proetale-module-detection attaches the already proved adopted declaration
AlgebraicGeometry.ProEtale.eq_zero_of_forall_upperStar_map_eq_zero in
WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Detection. It records the
generic fixed-module theorem actually used, rather than the abelian specialization. The source
declaration and its proof are unchanged; no duplicate Lean wrapper, module or hole is added. The
three recorded searches found no exact Mathlib counterpart.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
