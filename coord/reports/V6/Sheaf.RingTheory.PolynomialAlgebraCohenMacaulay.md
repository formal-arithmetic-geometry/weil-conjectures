## What changed

Proved `MvPolynomial.isNoetherianRing_and_local_depth_eq_dimension` with its public
signature unchanged. The proof uses the finite polynomial Noetherian and flat instances,
the fibre prime equivalence, `RingHom.depth_eq_add_of_flat_fiber`,
`RingHom.height_eq_add_of_flat_fiber`, and Mathlib's regularity theorem for polynomial
rings over regular rings. A proved private helper obtains depth equal to dimension for
regular local rings from the regular-parameters and support-dimension lemmas. Updated
the proof docstring and the existing node's proof, proof dependencies and proof origin.
All dependency imports use their current tracked `WeilConjectures` modules.

Validation: the module compiles cleanly through `lcompile.py` (3.8 seconds after import
cleanup). The delivery preflight supplies the declaration and axiom checks.

## Proved and sorry left

Closed the only original hole:
`MvPolynomial.isNoetherianRing_and_local_depth_eq_dimension`
(node `lem-trf-polynomial-algebra-cm`). Added zero holes and split off zero statements.
No sorries remain in the delivered module. The private helper is completely proved.

## No longer needed

Removed these proof-only imports:

- `Mathlib.RingTheory.Regular.RegularSequence`: provided by the regular-parameters API.
- `Mathlib.Algebra.Polynomial.FieldDivision` and
  `Mathlib.RingTheory.PrincipalIdealDomain`: no explicit PID case analysis.
- `Mathlib.RingTheory.FiniteType`: finite polynomial Noetherianity is an instance.
- `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`: use the fibre height formula API.
- `WeilConjectures.RingTheory.FlatLocalDepthFormula` and
  `Mathlib.RingTheory.RingHom.Flat`: use the fibre depth formula API.
- `WeilConjectures.RingTheory.PolynomialRingMaximalLocalizationDimension`: regularity
  of the full finite polynomial fibre replaces the one-variable dimension calculation.

Removed direct proof dependencies on `def-weil-pbc-regular-sequence`,
`lem-pur-polynomial-field-pid`, `lem-weil-pbc-finite-type-algebra-noetherian`,
`lem-weil-pbc-flat-height-formula`, `lem-weil-pbc-flat-local-depth-formula`,
`lem-weil-pbc-flat-local-ring-maps`, and
`lem-weil-pbc-polynomial-ring-maximal-localization-dimension`. Some remain transitive
requirements of the replacement APIs; no claim is made that all leave the target closure.
The updated node names the fibre depth/height and regular-parameter lemmas actually used.

## Where the brief, the DAG or earlier work was wrong

The original ten-step plan expanded polynomial induction and manually identified local
polynomial fibres. The library already provides a finite polynomial flat map, a
prime-spectrum fibre equivalence, flat-fibre depth and height formulas, and regularity of
finite polynomial rings over fields. These handle every finite number of variables at
once without changing the statement or a unit's route. The unit record does not assign
this node to a fixed realized proof step. The zero ring case is vacuous at primes and
needs no added nontriviality assumption; the zero-variable case is covered by the same
instances and fibre argument.

During the session the shared source migrated the dependency modules from `Sheaf` to
`WeilConjectures`; the final imports follow the tracked source and the public depth import
matches the current baseline. No definition, statement, or consumer adaptation was needed.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
