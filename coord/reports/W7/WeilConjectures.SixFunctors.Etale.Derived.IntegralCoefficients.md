## What changed

Reduced `AlgebraicGeometry.Etale.boundedConstructibleIntegral_derivedHom` to the
single-level estimate `AlgebraicGeometry.Etale.integralFiniteHomEstimate`. The source
proof extracts uniform input intervals, chooses a finite dimension bound, applies the
estimate at each level, and combines these with the existing completeness and Hom
comparison declarations. Its final clause handles arbitrary supplied intervals separately.

The finite-level estimate assumes neither completeness nor uniform tower bounds, nor
Noetherianity or the domain condition. Its proof plan constructs finite quotient models,
uses residue-field Tor tests and finite Hom, descends and glues, then identifies the
result with the ambient Hom reduction. It is a genuine finite-level part of the argument.
The source signatures, public imports, attributes and non-theorem bodies are unchanged.
The existing categorical source proofs remain in their baseline form.

## Proved and sorry left

Two literal holes in `AlgebraicGeometry.Etale.boundedConstructibleIntegral_derivedHom`
are replaced by a complete assembly from the named finite-level estimate. This is a
decomposition, not an unconditional proof. One new hole remains in
`AlgebraicGeometry.Etale.integralFiniteHomEstimate`, node
`lem-coef-small-etale-integral-finite-hom-estimate`.

The current source's other two holes remain unchanged:
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_derivedHom` and
`AlgebraicGeometry.Etale.NormalizedTower.isDerivedBaseChange_of_isHomotopyLimit`.
These appeared when C4's delivery was rolled back during this session. Thus the current
baseline has four literal holes, of which two are closed, with one new hole split off.
The source now has two literal holes; the packet adds one named theorem hole.

## No longer needed

No existing declaration, node, module, or public import is withdrawn. No pruning claimed.
The pro-etale fixed-coefficient statements cannot directly discharge the general constant
coefficient statement here. They remain needed by their own consumers. The generalized
single-level estimate keeps the descent and coefficient-amplitude bridges explicit.

## Where the brief, the DAG or earlier work was wrong

The cited blueprint node currently attaches a distinct pro-etale declaration, so the
unchanged source statement receives its own specialization node. Complete Noetherian
domains with a principal regular element and finite quotient need not be DVRs. The
finite-level proof plan uses a regular two-term coefficient resolution and finite Artinian
residue tests, not a DVR or self-injectivity assertion. The degree minus-one coefficient
term is retained in the amplitude calculation. The arbitrary field in the source statement
also requires descent from an algebraic closure in the finite coefficient argument.

C4's restored proofs and helper modules compiled in isolation, but the source repeatedly
exceeded the compile limit. That optional restoration is not included here: the current
two source holes are preserved. Repair record 531b32854f590138 retains that earlier work.
The restored helper modules are excluded because the target proof does not import them.
Temporary diagnostic files and profiling settings are excluded from the final packet.

## New nodes

`lem-coef-small-etale-integral-finite-hom-estimate`: the single-level estimate, with
regular coefficient resolution, residue tests, finite Hom, descent, gluing, and comparison.
Its natural-language proof checks unit ideal, reversed intervals, empty scheme, and point
examples. This is the one new theorem hole.

`lem-coef-small-etale-integral-constructible-hom`: attaches the unchanged existing source
statement and records the complete assembly from the estimate, completeness, dimension
finiteness, and Hom comparison. The biduality unit has no realized steps bypassed here.

No additional helper node is delivered; the target proof does not import the C4 quotient-model module.

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
