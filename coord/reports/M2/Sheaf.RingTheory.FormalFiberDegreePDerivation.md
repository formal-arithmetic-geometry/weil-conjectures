## What changed

Completed the retirement item listed in `coord/retire-items.tsv`: withdrew
`Sheaf.RingTheory.FormalFiberDegreePDerivation` through `deleted.txt` and redirected
`new-lem-weil-pbc-degree-p-derivation-component` to the existing upstream theorem
`MvPowerSeries.exists_derivation_isUnit_tmul_formalFiber`.

The upstream theorem has the exact same signature as the retired theorem after
renaming. The official source consumer already imports and calls it, so no consumer
adaptation is needed. The source module and its proof are unchanged.

Change record: `coord/changes/retire-formal-fiber-degree-p-derivation.md`.
The original duplicate compiled in 17.8 seconds; the upstream theorem and official
consumer compiled individually in 17.6 and 13.3 seconds through `lcompile.py`.

## Proved and sorry left

Retirement of an already proved duplicate: 0 of 0 holes closed, 0 holes added, and
0 split off. No `sorry` remains in the retired item and no Lean declaration is added.
The upstream replacement theorem is already fully proved.

## No longer needed

Pruned module `Sheaf.RingTheory.FormalFiberDegreePDerivation` and its duplicate
`MvPowerSeries.FormalFiberDegreePDerivation`. Its direct imports disappear with the
withdrawn file; the upstream twin retains the imports required by the official proof.
No mathematical DAG node is pruned: the existing node is retained and now points to
the upstream declaration.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed module, but this queue entry is explicitly
kind `retire` and the module already has zero holes. The upstream twin provides the
same result under a different declaration name. Repository-wide searches show no
remaining Lean import or use of the retired module or old declaration outside the
module itself.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
