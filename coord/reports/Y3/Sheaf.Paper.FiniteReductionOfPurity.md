## What changed

Pruned the two unused auxiliary declarations
`finiteReductionOfCompositionSource` and `finiteReductionOfCompositionExceptional`
from `Sheaf.Paper.FiniteReductionOfPurity`. Preserved all six declarations implementing
the actual blueprint clauses, every retained signature, every definition and every
public import. Wrote the direct full-composition proof explicitly: apply the main
purity reduction square to f ≫ g, then rewrite both purity maps by the existing
purity composition formula. The resulting statement has precisely the original
source and exceptional composition isomorphisms.

Updated `thm-pur-finite-reduction-of-purity` in its allowed proof fields and Lean
attachment to remove the surplus identities. Change record:
`coord/changes/Y3-prune-unused-finite-composition-comparisons.md`.

## Proved and sorry left

Original holes: two, in
`WeilConjectures.PurityFiniteSetting.finiteReductionOfCompositionSource` and
`WeilConjectures.PurityFiniteSetting.finiteReductionOfCompositionExceptional`.
Both are pruned as unused auxiliary statements, not counted as newly proved.

The retained `finiteReductionOfCompositionCoherence` has a complete proof from
`finiteReductionOfPurity` and `smoothPurityCompositionCoherence`. The item's main
purity, coefficient trace, unit trace, base-change and affine-orientation proofs
remain complete. Item holes remaining: zero. Holes added: zero. No new nodes.
The delivered Lean proof compiled successfully through lcompile.py (46.5 seconds).

## No longer needed

Pruned declarations:

- `WeilConjectures.PurityFiniteSetting.finiteReductionOfCompositionSource`.
- `WeilConjectures.PurityFiniteSetting.finiteReductionOfCompositionExceptional`.

Both `tools/downstream.py --uses` scans list 45 downstream modules, and find the
names only at their own declarations. A source-wide and DAG-wide name search found
no caller. The quarantine tree was searched too: its two importers
`NormalizedOrientationPerfectDuality` and `LowerShriekFunctoriality` use neither name.
The owning node's direct parents were read from stmt_deps, proof_deps and
proof-step uses, including parents without a Lean attachment. They require the
retained purity/trace/orientation/full composition/base-change clauses, not these
two auxiliary equations. The unit statement and all its realized steps remain.

The owning proof no longer directly needs
`lem-pur-finite-adjoint-mate-compatibility`,
`lem-pur-finite-tensor-presentation-reduction`, or
`def-weil-exceptional-inverse-image` for a separate composition-comparison argument.
These nodes/modules may remain needed elsewhere, including below tensor-purity;
none is withdrawn. No import or whole module is removed.

## Where the brief, the DAG or earlier work was wrong

The earlier proof plan correctly observed that the full composition clause needs
neither separate compositor-reduction identity, but retained both unused sorry
statements as obligations. Those surplus obligations are now pruned. The exact
blueprint composition claim is retained with its original comparison arrows and a
complete direct proof. All current DAG-parent requirements and the unit route are
preserved. No target statement or definition changes, and no unproved replacement
statement is introduced.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
