## What changed

Replaced the single proof placeholder in
`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_dual`.
The public signature and public imports are unchanged. The proof adds private imports
of `WeilConjectures.WeilSheaf.VerdierDualFinite`,
`WeilConjectures.WeilSheaf.StalkRationalPoint`, and
`WeilConjectures.WeilSheaf.ConstantTwistCohomology`.

For `C = Ra_! F`, Verdier exchange and the smooth lisse duality identification give
`D(C) ≅ Ra_* (F^∨(d))[2d]`. Applying degree `-i` and the shift comparison gives the
ordinary cohomology in degree `j`, since `i + j = 2d`. A proved private helper
`AlgebraicGeometry.homology_verdierDual_equiv` identifies the other side with
`H^i(C)^∨`: shift to the degree-minus-one duality theorem on the finite reduced
point, use its degree-zero smooth duality identification, and remove the zero
Tate twist. The proved private helper
`AlgebraicGeometry.globalSections_dual_equiv` transports stalk duality at the
Frobenius-fixed geometric point to global sections, including the inverse
transpose Frobenius identity.

The pairing is ordinary evaluation transported through this Frobenius-module
equivalence. Mathlib's `LinearMap.IsPerfPair.dualEval` and
`LinearMap.IsPerfPair.compl₁₂` supply perfectness. Frobenius invariance is the
intertwining equation followed by cancellation of inverse Frobenius.

This is the derived-duality/cohomology-of-dual route of the current blueprint,
`main-20261015`, section `sk-thm-derived-duality`, specialized to the existing
rational lisse existential statement. The coefficient spaces are already
finite dimensional in the Frobenius-module interface. No finite-coefficient,
integral, or canonical-cup-product statement is claimed.

## Proved and sorry left

The delivery replaces the one original hole in
`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_dual`.
There are no placeholders in the candidate and no holes added or split off.
All three private helpers have complete proofs: `nonempty_dual_equiv`,
`AlgebraicGeometry.globalSections_dual_equiv`, and
`AlgebraicGeometry.homology_verdierDual_equiv`.

The retained candidate compiled without errors or warnings in 37.0 seconds through
`lcompile.py`. The required delivery dry run passed compilation and the axiom probe
with review class `AUTO` (dry-run commit `6bbf019114`). Holes closed: one, the
public theorem named above. Holes added: zero. Holes split off: zero.

Existing theorem dependencies, including Verdier exchange, the smooth dualizing
complex, and exactness of Verdier duality, remain their own library obligations;
no proof of those declarations is claimed here.

## No longer needed

No original imports are removed. Each added private import supplies declarations
used in the proof: finite-point Verdier duality and the Tate-tensor identification;
point global-sections/stalk comparison; and equivariant global sections of an
isomorphism, respectively. No new intermediate modules are needed.

The proof does not introduce the general finite/integral coefficient pairing or
line-valued comparison to establish this existing rational existential theorem.
Those general blueprint results are not declared obsolete: other statements may
need them. No existing attached node or module has been identified as globally
prunable by this delivery.

## Where the brief, the DAG or earlier work was wrong

The missing `VerdierDualFinite.olean` that blocked the earlier attempt is now
available. Earlier local proof errors in inverse-Frobenius rewriting,
`Opposite.op` scope, and evaluation-pairing coercions had been repaired in the
retained candidate. This resumed session checked that candidate against current
sources, and both the required dry run and the single-file compile succeeded.
No tool workaround was needed.

No DAG node has a `lean.module` attachment to this module or its theorem. The
two blueprint names in the docstring are more general statements (general
perfect complexes and the specified canonical pairing), so attaching this
specialized existential declaration as their complete realization would be
incorrect. Their statements, proof plans, and unit routes remain unchanged.
No new public statement, definition, node, change record, consumer adaptation,
launcher modification, or shared-repository write is involved.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
