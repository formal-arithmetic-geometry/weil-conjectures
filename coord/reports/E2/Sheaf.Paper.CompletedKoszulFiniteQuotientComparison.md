## What changed

Proved `AlgebraicGeometry.Scheme.completedKoszulFiniteQuotientComparison` in its
assigned module, preserving its signature, docstring, public imports and local
monoidal instances. Added only private, proved helpers and proof imports.

The proof identifies lifted ideal-power quotients with the given finite coefficient
rings, compares their constant sheaves with finite-function sheaves, and transports
the comparison to inverse limits. The projection formulas identify the actual
completed scalar map. A scalar-tensor adjunction constructs the normalized quotient
module map; `completed_constant_algebra_flat_quotients` proves that map invertible.
The proved regular-unit normalization fixes its value on one. Finally the proof
assembles the module comparisons into complexes concentrated in degree zero and
uses the ordinary-unit projection formula and unitor naturality to prove the
required equality.

Proof imports reuse the proved private constant-sheaf and normalized tensor helpers
via Lean's `import all`. No imported module is edited. The node's proof steps,
proof dependencies and proof origin now describe this construction. The blueprint
unit route is preserved. Zero rings, empty schemes, zero and unit ideals need no
extra hypotheses: the quotient and tensor-adjunction constructions are uniform.

Searches included leanfinder for extension of scalars of a quotient, loogle for
functorial isomorphism transport, and grep/rg in Mathlib and both library roots.
There was no direct theorem for the full comparison. Mathlib's quotient equivalence,
limit preservation, extension/single-complex isomorphisms and monoidal identities
supply the elementary steps.

Validation: the complete item compiled without errors or warnings through
`lcompile.py` in 48.7 seconds, below the 60-second limit. A separate packet check
confirmed the original theorem signature and public imports verbatim, no forbidden
tokens or remaining holes, line lengths at most 100, and the DAG dependency union.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.completedKoszulFiniteQuotientComparison`
(node `new-s3-completed-koszul-finite-quotient-comparison`).
Added zero holes and zero split-off statements. No `sorry` remains in the item.
All private helper theorems and definitions have complete proofs/constructions.
Existing dependency statements are used as provided; this delivery does not claim
to close their holes.

## No longer needed

Removed the redundant trial proof import
`Mathlib.RingTheory.Ideal.Quotient.Operations` (already publicly available through
`Sheaf.Paper.AdicCoefficientDatum`). No original import, dependency node or module is withdrawn. Both original DAG
proof dependencies remain used. No new obligation replaces this one.
The proof needs only degree-zero module comparisons, so it does not add an
exactness, Koszul-resolution, cone or pro-zero dependency.

## Where the brief, the DAG or earlier work was wrong

The original single proof step omitted the comparison between constant quotient
sheaves and the supplied finite-functions presentation, the induced limit
comparison, and the normalized scalar-extension map. These constructions are now
explicit and proved. No mathematical statement correction or shared-interface
repair was required.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
