## What changed

Filled both proofs in `Sheaf.Paper.PbcFiniteCompletedCoefficientMap` without changing
any existing signature, definition, visibility, instance, docstring, or import.
Scoped `linter.unusedSectionVars` suppression retains the existing algebraic-closure
parameter of `pbcIntegerInclusion_ideal`, which its proof does not need.
`pbcIntegerInclusion_ideal` transports principal-ideal divisibility through `ULift`,
uses the existing proved `WeilConjectures.integralScalar_quotient_kernel`, and
transports back. `pbcCompletedScalarMap_exists` constructs the natural transformation
of constant quotient systems, conjugates it by `pbcConstantSystemComparison`, and
uses Mathlib `limMap`, `limMap_π`, and `limit.hom_ext`.

Updated the item's node proof, proof dependencies, and proof origin to record these
arguments. No new declarations or nodes are introduced. The unit's statement and
realized steps are unchanged. The construction applies at n = 0 (exponent one),
to equal coefficient fields, and to the empty scheme; neither proof requires a
nonempty scheme or a strict field inclusion. Closure and scheme universes remain
independent.

Searches actually run through msearch: LeanFinder for a unique projection-compatible
map of inverse systems (no exact sheaf result), Loogle for
`CategoryTheory.Limits.limMap` (found `limMap`, `limMap_π`), and grep for
`limMap_π|integralScalar_quotient_kernel`. Local source searches found the existing
quotient-kernel theorem and the coefficient-system comparison in
`BoundedConstructibleTower`. These supply the whole argument without new lemmas.

## Proved and sorry left

Closed 2 of 2 original holes:

- `AlgebraicGeometry.Scheme.pbcIntegerInclusion_ideal`.
- `AlgebraicGeometry.Scheme.pbcCompletedScalarMap_exists`.

Both belong to `def-weil-pbc-finite-completed-coefficient-map`.
Both proof bodies compile through `lcompile.py`; the final source compiled cleanly
in 22.9 seconds. Profiling options were removed before this check. Both transports
explicitly rewrite `map_pow` before returning the divisibility proof. The first
transport replaces an earlier simplification that failed under the delivery probe.
The final delivery checks also validate the source with its scoped linter option.
Holes added: 0. Split off: 0. Sorries left in the item: none.
Imported unfinished results remain the project's existing dependencies; this delivery
adds none and does not claim their axioms have been discharged.

## No longer needed

None. All five original public imports remain necessary for the existing exposed
statements and definitions, and no proof imports were added. No module or DAG node
is withdrawn. The general derived integral scalar-extension theorem is not used to
prove these two coefficient-map properties: only its module's already proved
integer-inclusion kernel API is needed. That module remains required by the existing
`pbcIntegerInclusion` definition. No declared statement dependency is removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The node originally had no numbered proof
steps or proof dependencies despite its two proof obligations. The sandbox node now
records the actual argument and the existing coefficient-system comparison it uses.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
