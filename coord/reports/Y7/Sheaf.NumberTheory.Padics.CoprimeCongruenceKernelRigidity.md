## What changed

Proved `Padic.coprime_congruence_kernel_rigidity` in
`Sheaf.NumberTheory.Padics.CoprimeCongruenceKernelRigidity` without changing its
signature or the reduction definition. Added two proved private helpers: quotient
matrix equality is entrywise ideal membership; reduction of an element congruent
to one modulo `I^n` has pth power one modulo `I^(n+1)` if `p ∈ I` and `n ≥ 1`.
The latter proves the square-zero matrix identity by induction, so it requires
no commutativity of matrix multiplication.

The main proof extracts the local DVR structure and the chosen uniformizer's
ideal from the existing coefficient theorem. The spectral norm extension and
`Padic.norm_p_lt_one` put `l` in that ideal. Induction uses the coprime power
bijection on each image subgroup. Krull intersection then proves the integral
kernel equality entrywise. Added the proof-only import
`Mathlib.RingTheory.Filtration`; retained the existing public imports and
`Mathlib.GroupTheory.OrderOfElement`. Updated the theorem docstring and the
item node's proof and proof origin to describe this argument.

Validation: the complete module compiled cleanly through `lcompile.py`, with
no errors or warnings. The proof handles arbitrary groups, rank zero, level
one, residue characteristic two, and ramified coefficient extensions without
extra assumptions. Rank zero is handled by the same vacuous entrywise proof;
no positive-rank instance is used. No definition or statement was changed.

## Proved and sorry left

Closed the sole hole:
`Padic.coprime_congruence_kernel_rigidity`
(node `lem-sfb-coprime-congruence-kernel-rigidity`).

Original holes: 1. Closed: 1. Remaining in the item: 0. Added: 0. Split off: 0.
Both private helpers have complete proofs. Existing imported dependencies are
used as declared; this delivery introduces no new assumptions or axioms.

## No longer needed

No imports, nodes, or modules are pruned. The direct unit-times-uniformizer
factorization and the ensuing comparison of real powers in the original Step 4
are unnecessary: `Ideal.iInf_pow_eq_bot_of_isLocalRing` proves separatedness
from the same recorded local DVR structure. The DVR theorem remains needed,
so its node and tool-use approval are retained. All original proof dependencies
remain used. No upstream declaration or import is removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The original separatedness
argument is valid but longer than the available Mathlib intersection theorem.
The updated DAG records this shorter implementation. Three search modes were
run through `msearch.py`: LeanFinder returned congruence-subgroup facts rather
than this theorem; Loogle confirmed `Nat.Coprime.pow_left_bijective`; grep
located the existing Krull intersection results in `Mathlib.RingTheory.Filtration`.
The declared coefficient and coprime-power dependencies were read before writing
the proof. The unit route is preserved; the item is an algebraic supplement
below that route and the unit's realized statement and steps are untouched.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
