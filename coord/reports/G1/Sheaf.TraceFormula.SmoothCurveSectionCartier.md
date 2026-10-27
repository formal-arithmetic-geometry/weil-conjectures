## What changed

Proved `AlgebraicGeometry.smoothCurveSection_cartier` in
`Sheaf.TraceFormula.SmoothCurveSectionCartier`, with its signature unchanged.
Separatedness makes the section a closed immersion. The canonical map from its
source to its scheme-theoretic image is then an isomorphism. Composing this map
with the image's map to the base gives the identity by the section equation, so
the image's map to the base is itself an isomorphism. Its finiteness, flatness,
and local finite presentation follow by instances, and the existing proved
Cartier criterion gives invertibility of the section's kernel ideal.

The proof follows all four steps of `lem-trf-smooth-curve-section-cartier` and
introduces no new dependency or change of route. The identity argument is valid
also for the empty base and non-Noetherian or nonreduced bases; no geometric
point or Noetherian hypothesis was added.

Removed the unused FiberDegree import and made RelativeEffectiveCartier a
proof-only import. The change record is
`coord/changes/smoothCurveSectionCartier-proof-imports.md`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.smoothCurveSection_cartier`
(node `lem-trf-smooth-curve-section-cartier`). Proved 1 of 1 sorries; added 0;
split off 0. No sorry remains in the item and no other theorem is changed.

The final proof and trimmed imports compiled cleanly in 5.7 seconds.
`#print axioms AlgebraicGeometry.smoothCurveSection_cartier` reports only
`propext`, `Classical.choice`, and `Quot.sound`. The sole existing direct consumer,
`Sheaf.TraceFormula.ValuationNodalPolarSection`, compiled unchanged against the
sandbox module in 20.4 seconds. Its temporary verification copy is not delivered.

## No longer needed

Removed the direct import
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`: the proof uses the
finite, flat, and locally finitely presented instances for an isomorphism
separately, rather than its bundled finite-locally-free predicate. This removes
no mathematical step or DAG dependency: `def-pc-finite-locally-free` still
explains exactly those three conditions.

Changed `WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier` from a
public import to a proof import. Its Cartier criterion remains necessary.
No node or module is withdrawn; no additional planned dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The stage-2 file exposed two proof dependencies as
public imports, which this delivery trims. The DAG already supplied the complete
proof route and the needed criterion was proved in the source library.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
