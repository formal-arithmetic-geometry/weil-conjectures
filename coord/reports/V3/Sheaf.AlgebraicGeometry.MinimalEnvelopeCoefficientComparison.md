## What changed

In `Sheaf.AlgebraicGeometry.MinimalEnvelopeCoefficientComparison`, proved the two
coherence theorems and `coefficient_minimal_envelope_exists`, preserving all public
signatures, definitions and public imports. A proved private helper establishes
quasi-coherence and finite type for an arbitrary ideal sheaf on a locally
Noetherian scheme. Quasi-coherence follows from the structure-sheaf kernel and
quasi-coherent pushforward along its closed immersion; finite type follows from
Noetherian affine section rings and the existing finite-type ideal-module theorem.
The supplied smoothness of N and the etale smoothness of U give the required
locally Noetherian instances. This also covers the empty vertex list, arbitrary
marking b (including zero in the coherence claims), and zero suspension rank.

Minimal-envelope existence applies `Scheme.exists_minimal_smooth_envelope` over
`ULift ℚ`. Its characteristic-zero instance is supplied locally by injectivity of
natural-number casts through `ULift.down`; no global instance is added.

The node's step 3 now records the coherence argument and its existing declared
dependencies. Its other proof steps are preserved, including those corresponding
to the six unfinished theorems. No blueprint unit route is bypassed.

Validation: the final item file compiled cleanly through `lcompile.py` in 9.0
seconds (exit 0). Every Lean line is at most 100 characters. The source comparison
shows only private import changes, a proved private helper and three proof-body
replacements. No existing consumer or source-library declaration was changed.

## Proved and sorry left

Closed 3 of the original 9 holes, all in namespace
`AlgebraicGeometry.HilbertCoefficient`:

- `RegularHilbertCoefficientDatum.markedCoefficientIdeal_coherent`.
- `coefficient_minimal_envelope_exists`.
- `RegularHilbertCoefficientDatum.suspendedCoefficientIdeal_coherent`.

Added zero holes and zero split-off statements. Six existing holes remain,
unchanged, all attached to `lem-trf-minimal-envelope-coefficient-comparison`:

- `AlgebraicGeometry.HilbertCoefficient.coefficient_transverse_rank_pos`.
- `AlgebraicGeometry.HilbertCoefficient.coefficient_retraction_exists`.
- `AlgebraicGeometry.HilbertCoefficient.coefficient_suspension`.
- `AlgebraicGeometry.HilbertCoefficient.regular_codimension_zero_coefficient_presentation`.
- `AlgebraicGeometry.HilbertCoefficient.minimal_envelope_coefficient_comparison`.
- `AlgebraicGeometry.EmbeddedResolutionHistory.coefficient_comparison_after_admissible_histories`.

The existing minimal-envelope input itself remains unproved in its own module;
using that named dependency is the requested stage-3 proof reduction. The two
coherence proofs use the existing proved ideal-module and quasi-coherence APIs.

## No longer needed

Removed unused private proof imports:

- `Sheaf.TraceFormula.EtaleLocalRingFlatness`.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`.
- `WeilConjectures.AlgebraicGeometry.Regular`.
- `Sheaf.AlgebraicGeometry.JetDiagramHilbertControl`.
- `WeilConjectures.Blowup.Affine.Principalization`.
- `Sheaf.AlgebraicGeometry.PermissibleCoordinateChart`.

These imports are not used by the delivered proofs or the module's signatures.
Their mathematical nodes remain dependencies of the preserved plans for the six
unfinished theorems, so no whole module or DAG node is claimed as pruned.
The coherence arguments do not need a finite enumeration of the weighted
coefficients or explicit generators of the suspension ideal: local Noetherianity
handles every ideal sheaf at once. All original public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The direct specialization of minimal-envelope existence needs an explicit
characteristic-zero instance for `ULift ℚ` in this import context. The field
instance alone does not synthesize it. This is supplied locally in the proof.

The stated dependency for transverse suspension requires `IsLocallySuspended`,
quasi-compactness and boundary-adaptation hypotheses. The supplied global
`SuspensionChart` does not directly have that predicate's type; constructing its
local pullback charts and checking its off-support unit-ideal clause is additional
Lean glue. The retraction dependency also returns an existential rank, whereas
`coefficient_retraction_exists` prescribes n, requiring a rank identification from
the supplied equations and Jacobian. Those proofs remain intact as named holes.
No statement was weakened, disputed, withdrawn, or replaced.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
