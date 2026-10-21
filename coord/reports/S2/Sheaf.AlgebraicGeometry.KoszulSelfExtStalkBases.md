## What changed

Completed the listed retirement by withdrawing
`Sheaf.AlgebraicGeometry.KoszulSelfExtStalkBases`, an unused re-export stub with
no declarations. `deleted.txt` lists its Lean path; the delivery tool writes
the standard empty withdrawn module. The mathematical node keeps its existing
upstream Lean attachment, proof, dependencies, and statement. Its Lean note now
records the wrapper withdrawal.

The previous reviewed Q8 retirement already provides the replacement argument:
the official source theorem constructs both finite stalk bases, and both parent
proofs import it directly and transport the exterior basis along
`exteriorSheaf_eq_exteriorPower`. Those parents compile unchanged with
`lcompile.py`: `KoszulSelfExtExterior` in 5.3 seconds and
`KoszulSelfExtDualExteriorConormal` in 9.7 seconds. The pre-withdrawal wrapper
also compiled in 1.9 seconds.

Change record: `coord/changes/S2-withdraw-koszul-stalk-bases-reexport.md`.

## Proved and sorry left

The assigned module has zero holes and declares no theorem. Closed 0 holes,
added 0 holes, split off 0 statements; no `sorry` remains in the delivery.
The existing theorem
`AlgebraicGeometry.koszulRegularImmersion_self_ext_stalk_bases` is preserved
under its official upstream module and is not claimed as a newly closed hole.
This delivery completes a module retirement, not a new mathematical proof.

## No longer needed

The Sheaf re-export module and its public imports of
`WeilConjectures.AlgebraicGeometry.KoszulSelfExtStalkBases` and
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf` are no longer needed in that
wrapper. Both dependencies remain available through the parents' own imports.
No mathematical node, proof dependency or unit step is pruned. In particular,
`lem-sc-koszul-self-ext-stalk-bases` remains necessary and retains its upstream
attachment.

`tools/downstream.py` reports zero downstream modules. Searches of all current
Lean sources and quarantined sources find no imports of the withdrawn module.
The DAG has two parents of the retained mathematical node; both already use the
official theorem directly and compile unchanged. No parent dependency update or
consumer adaptation is needed, because the mathematical node is retained and
the wrapper has no attachment or declaration of its own.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a proof obligation, but this is a listed retirement
with zero holes. The Q8 landing already removed the duplicate theorem and
adapted both consumers. Submitting that source unchanged was correctly refused
by preflight as a no-op. The present packet completes the remaining withdrawal
of the unused wrapper, preserving the actual replacement argument and the
mathematical DAG route. No source-library file or target is changed.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
