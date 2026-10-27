## What changed

Proved `exists_strictlyPositiveIntegralGrading` in
`Sheaf.TraceFormula.SharpMonoidPositiveGrading`, preserving its signature and public imports.
The proof uses the existing `Weil.rationalConeDualFinite` declaration, with private
proof imports for finite monoid sums, rational coordinate spaces, positivity, and ring arithmetic.
A proved private helper clears denominators of finite rational families by finite-set induction.
The grading is the explicit integer coordinate sum, and its natural-valued restriction uses
`Int.toNat` with a proof of nonnegativity. Updated the node proof to describe this implementation.

The single-file server compile passes. Empty generator sets, empty form families, rank zero,
and the zero monoid are covered without nonemptiness assumptions or division by their sizes.

## Proved and sorry left

Closed the one original hole: `exists_strictlyPositiveIntegralGrading`
(node `lem-trf-sharp-monoid-positive-grading`).
The private `common_denominators` helper is also proved.
No `sorry` remains in the item, and no holes are added or split off.
The existing imported theorem `Weil.rationalConeDualFinite`
(node `lem-trf-rational-cone-dual-finite`) still has its pre-existing hole;
this delivery proves the assigned theorem from that declared dependency.

## No longer needed

None of the declared DAG dependencies is pruned: the sole proof dependency,
`lem-trf-rational-cone-dual-finite`, is used. No original import is removed.
No modules or nodes are withdrawn. The temporary broad `Mathlib.Tactic` import
was replaced by the specific positivity and ring tactic imports.

## Where the brief, the DAG or earlier work was wrong

No statement or source error was found. The planned pointedness argument can be applied
only at the lattice point where strict positivity is needed: if the sum of forms vanishes,
clear denominators for its negative and use sharpness on a positive multiple of that point.
This avoids introducing a separate cone structure or a separate global salience lemma.
The mathematical route and dependency are unchanged; the node now records this ordering.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
