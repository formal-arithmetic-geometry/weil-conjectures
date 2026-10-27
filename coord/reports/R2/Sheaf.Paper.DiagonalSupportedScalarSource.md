## What changed

Reduced diagonal_supported_scalar_source to the ordinary scalar-extension transpose
of the supported coefficient unit. The original signature and both public imports
are unchanged. Constructed the new normalized source explicitly from ordinary
composition and the given diagonal retraction. Proved the scalar-mate equation by
transposing under the derived scalar adjunction and applying the full restriction
square normalization on single complexes. No arbitrary witness defines data. A private generic constructor lifts the explicit
ordinary sheaf comparison to modules and carries its normalization proof alongside
the isomorphism. It handles transport along the retraction equality with a free
endomorphism before specializing the composition, avoiding repeated kernel
reduction of module coherence maps.

Added proofs of flatness in the actual internal-module category and of acyclicity
under any retraction. Flatness uses exact complementary tensor restrictions and
joint reflection. Acyclicity pushes a K-injective resolution through the exact
closed direct image and uses the retraction to identify its further pushforward.

Remote compilation passed for all four Lean files. The final clean check of the
item took 25.4 seconds. No profiling options or raised limits remain.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonal_supported_scalar_source
(node lem-diagonal-supported-scalar-source).

New proved declarations:
AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonal_supported_flat and
AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonal_supported_acyclic.

One new hole remains:
AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonal_supported_ordinary_scalars
(node lem-sfb-diagonal-supported-ordinary-scalars). Its conclusion is solely
invertibility of an ordinary extension-of-scalars transpose. It has no derived
functors, endpoints, normalized source, choice of retraction, restriction square,
or compatibility equation. Thus this is a decomposition (one hole closed and one
strictly smaller hole added), not a net reduction in the hole count.

## No longer needed

No original import was removed and no existing module was withdrawn.
Removed the redundant private MapModMonoidal import from the new flatness module;
the needed instance is already public through DiagonalCoefficientCategory.
The item's proof no longer directly uses lem-c2-internal-section-module-flatness
or lem-weil-pbc-ring-sheaf-change-adjunction
(modules Sheaf.CategoryTheory.InternalSectionModuleFlat and
Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction): internal flatness is proved directly,
and the scalar compatibility is proved using the existing scalar adjunction and
mate definitions, rather than a separate geometric change-adjunction theorem.
The old closed-localization dependency remains needed through the proved flatness
and acyclicity modules. The existing flat scalar endpoint and canonical right
derived functor remain needed. The sk-prop-diagonal-tower unit route is retained.
These omissions concern this proof's dependency edges, not global withdrawals.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically sound. Its internal/section flatness transport
is avoidable: the same closed/open reflection argument works directly for internal
modules. The existing underived projection theorem lives in a different module
encoding and does not directly prove the specified supportMap transpose invertible.
The private pushScalarSingleIso in CondensedFiniteCoefficientLocalization gives
an unnormalized object comparison, and likewise does not identify this specified
transpose. That ordinary normalization bridge is the remaining named obligation. Empty Y,
zero coefficients, and arbitrary nonflat coefficient maps introduce no extra
hypotheses in any statement of the delivery.

## New nodes

lem-sfb-diagonal-supported-flat: proved flatness of the actual supported internal
regular module; module Sheaf.Paper.DiagonalSupportedFlat.

lem-sfb-diagonal-supported-acyclic: proved invertibility of the canonical full
right-derived unit on a supported source under a retraction;
module Sheaf.Paper.DiagonalSupportedAcyclic.

lem-sfb-diagonal-supported-ordinary-scalars: the single remaining ordinary scalar
transpose obligation; module Sheaf.Paper.DiagonalSupportedOrdinaryScalars.
Each node records its source, proof, attachment and searches. No shared interface
was changed, so no change record or consumer adaptation is required.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
