## What changed

Added the proof reduction for `CategoryTheory.ringFamilyGlobalExtension_module_monoidal`.
The target now obtains invertible normalized oplax data from a separately named auxiliary
statement and converts it to a strong monoidal structure with
`Functor.Monoidal.ofOplaxMonoidal`. Added the auxiliary module and its DAG node.

## Proved and sorry left

Closed the target theorem `ringFamilyGlobalExtension_module_monoidal`.
One strictly smaller auxiliary theorem remains as `sorry`:
`ringFamilyGlobalExtension_oplax_normalized`.

## No longer needed

None. The existing colimit proof and its imports remain used by the module.

## Where the brief, the DAG or earlier work was wrong

The original node's plan omitted the need to expose the invertible oplax data before
constructing `Functor.Monoidal`; this delivery records that missing categorical step.

## New nodes

`lem-weil-pbc-global-section-module-monoidal-oplax` records the auxiliary normalized oplax
statement used by the target.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
