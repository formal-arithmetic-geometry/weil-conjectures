## What changed

Proved `AlgebraicGeometry.Scheme.pbcPurityCompactScalar_integral_isIso` without
changing its signature. A private helper transports the existing
`completedIntegralFiniteFree` basis through `purCoefficientIso`, using the proved
`coefficientScalar_square`. The proper/open factorization then combines the
proper scalar comparison with the existing open scalar comparison.

Added `Sheaf.Paper.FiniteFreeProperScalarComparison` with the proved theorem
`WeilConjectures.PurCompactSupport.properComparison_isIso_of_finiteFree`.
It specializes `finiteFreeDirectImageCoherence` to the coefficient square and
identifies its specified comparison with `properComparison`. A proved private
categorical helper transports inverse mates between two left adjoints to the
same right adjoints, using conjugates of identity isomorphisms and Mathlib's
mate composition identities. Thus no equality of completed morphisms is inferred
from equality of their reductions.

The item adds private proof imports of the completed finite-free basis,
coefficient-presentation transport, and the new bridge. No existing public
imports, definitions, attributes, or statement signatures changed.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Scheme.pbcPurityCompactScalar_integral_isIso`
(`lem-pur-lifted-compact-scalar-invertible`). The item has zero remaining holes.

The new theorem
`WeilConjectures.PurCompactSupport.properComparison_isIso_of_finiteFree`
(`lem-pur-finite-free-proper-scalar-comparison`) and both private helpers are
proved. Added zero holes and split off zero unproved statements. The proof uses
existing declared dependencies, including dependencies that still contain
`sorry`; this delivery does not claim to close those dependencies.

## No longer needed

None. The original public coefficient-model import and both original declared
proof dependencies remain needed. No module, declaration, node, or unit step is
withdrawn. The added bridge replaces no existing public API.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The existing finite-free direct-image coherence
theorem supplies the underlying comparison result, but its scalar-model interface
differs from `properComparison`. The missing work is the proved normalization
bridge, together with transporting the completed finite-free basis to the lifted
coefficient presentation. The item's proof record now names those steps.

## New nodes

`lem-pur-finite-free-proper-scalar-comparison`, in
`dag/nodes/sec-smooth-purity/lem-pur-finite-free-proper-scalar-comparison.json`,
records the proved generic bridge. Its proof uses the existing
`lem-sp-finite-free-direct-image-coherence` and elementary Mathlib mate identities.
Finite product/coproduct comparison includes rank zero; the argument also applies
to empty schemes and zero complexes. The smooth-purity unit route is preserved.
The coherence node is used as a tool from the scalar-compatibility unit: the
smooth-purity unit has no separate normalization bridge for this mate. No
`tool_uses` approval was edited. No change record is required because no existing
interface or other module is changed.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
