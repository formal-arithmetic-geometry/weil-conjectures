## What changed

Retired the declaration-free module
Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom, as explicitly requested
by coord/queue.tsv and coord/retire-items.tsv, through deleted.txt.
Its canonical upstream twin already contains the complete theorem proof.
Updated only the DAG node's lean.note to record the retirement; its upstream
attachment, statement, proof dependencies and unit route stay intact.
Change record: coord/changes/N1-retire-raw-transition-to-hom-shim.md.

The historical consumer Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality
already re-exports its upstream twin, whose comparison proof imports and applies
the canonical upstream theorem directly. Current Lean import search and
tools/downstream.py both find zero consumers of the retiring shim.

## Proved and sorry left

The assigned item has zero declarations and zero sorry holes before retirement.
Holes closed: none (0 of 0). Holes added: none. Holes left in delivered modules: none.
No statements split off. The existing proved upstream declaration
AlgebraicGeometry.Etale.higherDirectImageRawTransition_toHom is retained verbatim;
its proof applies higherDirectImageRawTransition_toHom_core and evaluates the
resulting equality on z. No new theorem proof is claimed by this retirement.

Server validation: scratchpad/VerifyCanonicalComparison.lean compiled in 3.9 seconds.
It imports the canonical theorem and its actual upstream consumer, checks both
signatures, and prints the axioms of higherDirectImageRawTransition_toHom and
higherDirectImageRawOverPullback_comparison. Both use exactly propext,
Classical.choice and Quot.sound, with no sorryAx.

## No longer needed

The module Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom and its
public re-export of WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTransitionToHom
are redundant and retired. No current module imports this Sheaf path.
No mathematical node is pruned: sbc-lem-higher-image-raw-transition-to-hom is still
needed by sbc-lem-higher-image-raw-over-comparison, which uses its canonical upstream
declaration. All upstream modules and theorem dependencies remain in place.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a sorry-bearing item, but the current assigned
queue row is a retirement. D2's reviewed canonicalization already moved the attachment
to the proved upstream declaration and left a declaration-free Sheaf shim.
The inventory's one consumer is historical: it too is now a canonical upstream re-export.
No matching quarantine/rework entry or return exists for this item.
Checked the only live parent and the owning unit's realized entries; neither requires
the redundant Sheaf path. The explicit retirement request is consistent with current source.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
