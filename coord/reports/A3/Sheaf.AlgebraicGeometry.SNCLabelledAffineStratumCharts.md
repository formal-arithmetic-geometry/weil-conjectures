## What changed

Proved `AlgebraicGeometry.exists_sncAffineStratumCharts` in the assigned module, with its
signature and `SNCAffineStratumChart` unchanged. Added proved private helpers for parameter
extension, spreading codimension-one equations, simultaneous affine restriction, integral
component refinement, and affine/stalk transports. The equations keep the prescribed label
order; parameters hold at every prime; the residual isomorphism is over the chart.

The argument follows the original six steps, with shorter existing-library implementations:
`IsRegularImmersion.of_stalk` spreads local principal generators, and lifting a minimal list
of quotient maximal-ideal generators supplies the complementary parameters directly.
The existing node's proof, dependencies and proof origin now describe the Lean proof.
No public definition, target, source-library declaration, or consumer changed.

Validation: the complete module compiles through lcompile without warnings in 14.3 seconds.
`#print axioms AlgebraicGeometry.exists_sncAffineStratumCharts` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The construction
includes the empty stratum, empty selected label set, empty boundary, and dimension-zero cases.
The empty label set gives the zero ideal and an actual isomorphism of quotient spectra.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.exists_sncAffineStratumCharts`.
Proved 1 of 1 original sorries. Added 0 sorries; split off 0 statements. No sorry remains in
any delivered Lean file. Every private helper is proved.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.RegularNormalDecomposition` and
`WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`. The public regular-scheme
API already exposes `IsRegular.exists_isClopen_isIntegral`, and the direct kernel/vanishing
ideal equality proves that the intersection ideal is radical without invoking uniqueness of
the reduced induced structure. The regular-normal mathematical dependency remains, using the
upstream theorem in `WeilConjectures.AlgebraicGeometry.Regular`.

Removed redundant direct Mathlib proof imports for Noetherian schemes, affine schemes,
closed immersions, Noetherian rings, local modules, Noetherian spaces, ideal sheaves, scheme
properties, and regular local-ring definitions; the retained imports expose the APIs used.
The retained proof imports are the affine ideal comparison, kernel/vanishing-ideal API,
regular-immersion spreading, regular quotient kernel parameters, and parameter quotient dimensions.

Removed the following proof-dependency edges from the item node:
- `lem-weil-pbc-reduced-induced-closed-subscheme`: direct equality with the radical suffices.
- `lem-weil-pbc-regular-local-cotangent-dimension`: lift minimal generators of the quotient
  maximal ideal instead of completing a cotangent basis.
- `lem-weil-pbc-nakayama-local-generators`: generation follows by mapping and pulling back
  ideals along the surjective stalk map.
- `lem-weil-pbc-surjective-image-noetherian`: the quotient and closed-subscheme Noetherian
  instances suffice.

The obsolete reduced-induced and surjective-image entries were also removed from `tool_uses`.
No module is withdrawn and no upstream declaration is removed. No claim is made that these
modules are unused by other parents. The blueprint unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was required. The DAG's cotangent-space completion
and explicit denominator-clearing plan was longer than necessary given the present library.
The proof uses existing regular-immersion spreading and a direct quotient-generator argument
for those steps. Finite ideal-sheaf suprema require explicit subtype indexing to prevent Lean
from unfolding the complete-lattice construction during elaboration; the file compiles under
the existing heartbeat and server time limits without changing either.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
