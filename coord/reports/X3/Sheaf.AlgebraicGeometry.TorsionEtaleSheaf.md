## What changed

Retire the zero-hole compatibility module Sheaf.AlgebraicGeometry.TorsionEtaleSheaf
in favor of WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf, as assigned in
coord/retire-items.tsv. Rewrite all 11 current direct imports preserving visibility.
In InvertibleOrdersColimit and TorsionFilteredUnion, replace PositiveNat by its
abbreviation body PNat.DvdOrder and positivity uses by PNat.DvdOrder.val_pos.
The torsion predicate and all mathematical constructions are unchanged.
Redirect def-weil-pbc-torsion-etale-sheaf's Lean attachment to the upstream twin.

Change record: coord/changes/retire-torsion-etale-sheaf.md.

Validation: lcompile.py --all compiled all 11 adapted consumers with no errors
or warnings; each file took 1.9–21.7 seconds. The full-library name scan finds
no other uses of the removed aliases. All 51 transitive consumers were audited
for compatibility-name uses; the only public type expansion is definitionally
equal. InvertibleOrdersColimit currently has no downstream importers.

## Proved and sorry left

Retirement, not a proof/decomposition: 0 of 0 item holes closed, 0 added,
0 split off. PositiveNat.pos was already proved by PNat.DvdOrder.val_pos.
No existing proof is replaced with sorry. Two unchanged holes in adapted files:
artin_tensor_etale_acyclic (lem-trf-artin-tensor-etale-acyclic), and
AlgebraicGeometry.Scheme.isZero_cohomology_projective_strictLocal_intersection
(lem-trf-projective-strict-local-intersection-acyclic). No other adapted file
contains a sorry.

## No longer needed

Sheaf.AlgebraicGeometry.TorsionEtaleSheaf and its compatibility declarations
AlgebraicGeometry.Scheme.PositiveNat and PositiveNat.pos are withdrawn.
All 11 consumer imports of the wrapper are replaced by its upstream twin.
The node def-weil-pbc-torsion-etale-sheaf remains needed and now points at the
upstream declaration. No unit statement or proof step is bypassed; no further
mathematical dependency or upstream declaration is pruned.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proof work, but the actual queue item is kind retire
with 0 holes. The queue's initial consumer list is stale: the current sources have
11 direct consumers. The DAG's Lean attachment still named a wrapper that did
not itself define IsTorsionAbelianSheaf; it is redirected to the original module.
The wrapper's only additional names were definitionally redundant, so removing
them requires no mathematical statement repair.

Searches: msearch loogle PNat.DvdOrder returned unknown identifier; leanfinder
found PNat.pos and related positive-natural-number results; grep was recorded.
Reading WeilConjectures.Data.PNat.DvdOrder identifies the precise existing
API PNat.DvdOrder and PNat.DvdOrder.val_pos used by this packet.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
