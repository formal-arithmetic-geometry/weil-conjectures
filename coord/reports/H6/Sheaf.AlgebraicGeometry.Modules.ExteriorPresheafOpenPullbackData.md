## What changed

Retired Sheaf.AlgebraicGeometry.Modules.ExteriorPresheafOpenPullbackData in favor
of its existing WeilConjectures twin, as requested by coord/retire-items.tsv and
the human-approved retirement hand-off. Updated its node's Lean attachment.
The sole direct consumer, Sheaf.AlgebraicGeometry.Modules.ExteriorPresheafOpenPullback,
now imports the upstream twin. A proved private comparison lemma identifies
exteriorSheafPresheaf with PresheafOfModules.exteriorPower: the objects coincide
and uniqueness on pure wedges identifies the restrictions. The original public
consumer signature is unchanged. Its proof node now describes this comparison.

Change record: coord/changes/retire-exterior-presheaf-open-pullback-data-h6.md.
The consumer compiled cleanly through lcompile.py. The comparison covers n = 0,
empty opens, empty schemes, and arbitrary modules without finiteness assumptions.

## Proved and sorry left

Original item: 0 sorries. Holes closed: none (0). Holes added: none (0).
No sorries remain in the delivery. The private theorem
exteriorSheafPresheaf_eq_exteriorPower is fully proved. The consumer theorem
AlgebraicGeometry.Scheme.Modules.exteriorPresheaf_open_pullback is fully proved
from the existing upstream component-data theorem. This is a retirement, not a
new closure of the already-proved exteriorPresheaf_open_pullback_data theorem.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.Modules.ExteriorPresheafOpenPullbackData.
Removed its proof import from Sheaf.AlgebraicGeometry.Modules.ExteriorPresheafOpenPullback
and replaced it with WeilConjectures.AlgebraicGeometry.Modules.ExteriorPresheafOpenPullbackData.
The duplicate local scalar-transport and adjunction helpers disappear with the retired
module; the upstream implementation supplies the same component data. No DAG node
is deleted: lem-sc-exterior-presheaf-open-pullback-data points to the upstream theorem.
The consumer retains its public ExteriorSheaf import because its statement uses it.
No other module or dependency is pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed module. This item is instead listed
as a zero-hole retirement. The upstream twin restates the component theorem in
its generalized exterior-power API, so a direct import swap alone needs the
proved comparison supplied here. No mathematical error was found, and the unit
route and target signatures are preserved. No upstream source file was modified.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
