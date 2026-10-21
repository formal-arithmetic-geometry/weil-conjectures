## What changed

Proved `AlgebraicGeometry.ProEtale.StrictTower.squareG_pasting_inv` with the original
explicit signature, binders, equation and docstring retained verbatim. The proof-only
import of `StrictTowerDirectImageCoherence` supplies its proved concrete compositor
associativity. Two proved private helpers express reflexive compositors and square
comparisons directly through `gCompEq`; the proof applies associativity three times,
rearranges the first two equations and cancels adjacent inverse comparisons.

This repairs return C-c7970 (head c79701662): removed the returned public
`pullbackSquarePastingLaw` representation and its generic family-specialization proof.
The concrete calculation avoids the kernel conversion that broke the consumer.
Updated the node's proof, proof dependencies and origin, and restored its original
Lean statement attachment. The change record is
`coord/changes/D5-strict-tower-pullback-pasting-concrete.md`.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.StrictTower.squareG_pasting_inv`
(node `lem-cbc-strict-tower-pullback-square-pasting`). One of one holes proved;
zero holes added, zero holes left, zero split off. Both private helpers are proved.

The final item compiled without warnings in 3.6 seconds through `lcompile.py` at the
standard limits. In the same compile set, the current, unchanged
`Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` (holder U3) compiled in
28.2 seconds against this item. Both original uses pass; no consumer adaptation
is delivered. These measured results replace the returned report's unreproduced
27.8-second claim.

## No longer needed

No existing import removed, module withdrawn or global pruning claimed. The direct
proof needs neither the returned generic pasting-family definition nor its helper
specialization layers; those were additions of the returned packet and are omitted.
The node no longer directly needs
`lem-weil-pbc-exact-functor-derived-factorization` or
`lem-weil-pbc-localization-universal-property`, because their transport work is
already proved in `StrictTowerDirectImageCoherence`. They remain transitive
requirements of that coherence module. The unit has no realized statement or steps
bypassed by this calculation.

## Where the brief, the DAG or earlier work was wrong

The original plan repeated module, tower and derived associativity already proved
in `StrictTowerDirectImageCoherence`. The returned generic law introduced independent
proof arguments in the derived-category instances. Specializing that generic law
back to explicit component equations caused the reported kernel timeouts.
Expanding the concrete square comparisons directly fixes this conversion while
preserving the original public statement. No mathematical statement is disputed,
strengthened or weakened, and no new nodes are needed.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
