## What changed

Proved `WeilConjectures.ResidueCompatible.frobenius_exact` in
`Sheaf.Paper.ResidueCompatiblePullbackFrobenius`. The proof uses the recorded
isomorphism-field transport for geometric Frobenius and its inverse. Exact module
inverse image preserves the cohomological vanishing of integral representatives;
rational object comparisons and common-stage comparisons transport these witnesses.
The inverse and recorded counits give reflection of both standard half-categories.
Private proved helpers identify the normalized descended shifts with the canonical
integral, constructible, rational and common-stage shifts, so triangulated exactness
uses precisely the shift instances specified by the theorem.

Added private proof imports of `Sheaf.Paper.IsomorphismFieldTransport`,
`Sheaf.Paper.AutomorphismConstructibleStageEquivalence`, and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
Updated Step 1 and its dependency list in the existing node to record this route.
All public signatures and definitions are unchanged. The proof context disables
the same broad completed-module instance candidates as the canonical-shift source
module, preventing unnecessary search through those instances. The new shift
normalization helpers respect transparency after the integral comparison has been
established. The existing four T1 corollary proofs are preserved. No other modules
are adapted.

## Proved and sorry left

Closed one of the six existing holes:
`WeilConjectures.ResidueCompatible.frobenius_exact`.
No holes added; no split-off statements.

Five holes remain, all attached to
`lem-zl-residue-compatible-pullback-frobenius`:

- `WeilConjectures.ResidueCompatible.residueCompatiblePullbackFrobenius`
- `WeilConjectures.ResidueCompatible.rational_heart`
- `WeilConjectures.ResidueCompatible.finite_diagram_descent`
- `WeilConjectures.ResidueCompatible.composition_scalar`
- `WeilConjectures.ResidueCompatible.transport_scalar`

These are existing named theorem holes, with their source and proof plans retained.
The existing proofs of `immersion_residue`, `rational_point_naturality`,
`common_point_naturality`, and `common_heart` are not counted as new progress.
The new proof uses stated dependencies that themselves still have proof holes;
this is a proof from the declared dependency interfaces, as required in stage 3.

## No longer needed

No existing imports removed and no modules withdrawn. Step 1 no longer uses
`lem-weil-isomorphism-derived-pullback` or
`lem-weil-proetale-isomorphism-inverse-image` directly: their transport data are
already recorded by `lem-pod-isomorphism-field-transport`. They are not globally
pruned, since that recorded transport still depends on their mathematics.
The remaining steps and unit route are retained.

## Where the brief, the DAG or earlier work was wrong

The original Step 1 describes exactness abstractly but does not explicitly identify
the descended shift structure with the canonical one used in `frobenius_exact`.
The private normalization lemmas supply that identification without changing any
statement. No statement was found false.

During the session the shared item temporarily showed the older ten-hole source,
then returned to the six-hole T1 baseline. The final delivery preserves all four
T1 proofs and measures this delivery against the current six-hole baseline.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
