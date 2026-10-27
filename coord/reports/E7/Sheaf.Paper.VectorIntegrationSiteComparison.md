## What changed

Added the proof-only import Sheaf.Paper.VectorLocalTraceExponent and completed
vectorExponentIndependence in Sheaf.Paper.VectorIntegrationSiteComparison. Four proved
private helpers establish uniqueness of normalized ordinary integration, passage from
local to global transition equations, and transport through a natural comparison
isomorphism. Public signatures, definitions, public imports and the unit route are unchanged.
The other original hole, vectorTensorComparison, is preserved.

## Proved and sorry left

Closed one of the two original holes:
AlgebraicGeometry.ProEtale.VectorIntegrationSite.vectorExponentIndependence
(node lem-pur-vector-integration-site-comparison). Its Lean body is complete, but this
is a decomposition rather than a net proof: one strictly local hole was added.

The two holes left in this packet are:

- AlgebraicGeometry.ProEtale.VectorIntegrationSite.vectorTensorComparison:
  existing hole, node lem-pur-vector-integration-site-comparison, unchanged.
- AlgebraicGeometry.ProEtale.VectorIntegrationSite.vectorIntegrationLocalTrace_exponentTransition:
  new hole, node lem-pur-vector-local-trace-exponent, in
  Sheaf.Paper.VectorLocalTraceExponent.

Thus: one original hole closed, one added, net zero holes closed. Both modules compile
through lcompile.py --all. No definition contains sorry, and every private helper is proved.
The local statement was checked on rank zero, empty frames, equal exponents and
non-flat finite coefficient quotients in the source argument.

## No longer needed

None: no existing import, module or node is withdrawn, and no global pruning is claimed.
The existing transport node remains for the still-open tensor clause. The new exponent
proof does not use that finite-type-only specialization; it uses the strictly local
ordinary trace transition instead, followed by proved gluing and site transport.

## Where the brief, the DAG or earlier work was wrong

The final planned application of IntegrationExponentTransposeTransport does not directly
supply vectorExponentIndependence: its published specialization is finite type over the
fixed field, with the coefficient index P.level - 1, whereas the assigned declaration
quantifies over every Noetherian base and every n. No statement is weakened here. The
new lemma isolates the source's local Kummer trace argument at that generality, and the
complete Lean assembly proves the global comparison at precisely the original signature.
The tensor clause remains open rather than being replaced by an equivalent placeholder.

## New nodes

lem-pur-vector-local-trace-exponent states the ordinary trace transition on one frame,
with arbitrary normalized twist and projective data. It excludes global gluing and all
site comparison maps, so it is strictly a part of the original exponent argument.
Its source proof uses Kummer-boundary naturality, the two projective decomposition
components, the affine open counit, ordered tower induction, and naturality of the frame
prefix. The docstring and node record this argument. LeanFinder, Loogle, grep and
LeanSearch found no Mathlib match; the blueprint search found no duplicate.
No change records are needed: no existing module other than the assigned item changed.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
