## What changed

Added `Sheaf.Paper.CompletedAffineFreePresheafLocalDual`, splitting the finite-support
local dual construction before sheafification. The assigned theorem now has a complete
proof using the locally surjective sheafification unit and sheaf separatedness to descend
vanishing from the finite free presheaf representatives. The finite-support geometric
construction remains one named theorem with its own DAG node.

## Proved and sorry left

Closed the original `completedAffineFree_localDual_detect` hole. Added one strictly
smaller theorem, `completedAffineFree_presheaf_localDual`, with one `sorry`; it is the
finite free presheaf local dual separation substep and has node
`lem-sfb-completed-affine-free-local-dual-local-presheaf`.

## No longer needed

No planned imports were removed. The proof uses the coefficient-ring, pro-affine-etale,
sheafification, free-presheaf, and pushforward-continuous imports already present, plus
the new presheaf-local-dual module.

## Where the brief, the DAG or earlier work was wrong

The DAG's finite-support geometric step cannot be discharged by a Mathlib duality lemma:
the required natural slice functionals depend on clopen graph refinements of the
pro-affine-etale presentation. The reduction isolates exactly that geometric substep;
the parent combination is fully proved.

## New nodes

`lem-sfb-completed-affine-free-local-dual-local-presheaf` records the finite-support
presheaf separation theorem and its source, proof plan, and search results.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
