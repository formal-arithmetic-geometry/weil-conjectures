## What changed

Proved `AddCommGroup.divisible_unit_lattice_extension` in
`Sheaf.GroupTheory.DivisibleUnitLatticeExtension`, with its signature and public imports
unchanged. The proof uses the explicit subgroup `S = f⁻¹(nC)` of `L`, where `C = B/D`
and `f = p.comp φ`. Compatible Smith bases give `v_j = a_j e_j` and integers `t_j`
with `a_j t_j = n`. Divisibility inside `D` corrects lifts so that the basis map
extends `φ`. Multiplication by `n` gives the inclusion `L → S`; the quotient is killed
by `n`, so the proof supplies exponent one. Cancellation in the torsion-free quotient
proves surjectivity. This route does not need the original finite-cokernel hypothesis.

Added only proof imports for integer Euclidean-domain instances, torsion cancellation,
and finite bases. Updated the proof, proof dependencies and proof origin of both nodes
attached to the declaration. Added one node attaching an exact existing Mathlib theorem;
there is no duplicate Lean theorem or new Lean module.

Validation: the entire proof compiled without holes or warnings through `lcompile.py`
in 7.2 seconds after removing unused proof imports. The delivery tool runs the final
compilation and axiom checks. Edge cases checked in the argument: `n = 1`, rank zero,
`D = B`, `D = 0`, and noninjective `φ`; no choice of a nonzero basis vector is made
when the basis is empty. `G` is a subtype of `L` and thus has the required universe.

## Proved and sorry left

Closed: `AddCommGroup.divisible_unit_lattice_extension` (the single original hole;
attached nodes `lem-sfb-divisible-unit-lattice-extension` and
`lem-per-divisible-unit-lattice-extension`).

Holes closed: 1. Holes added: 0. Holes remaining: 0. Split off: none.
The new Smith-basis node is already proved in Mathlib.

## No longer needed

No original import or separately stated dependency is removed. The existing finite-free
subgroup Mathlib leaf remains useful for finite freeness of `S`. The cyclic-adjunction
construction, relation calculation and induction on the size of the finite cokernel
in the original plan are unnecessary; they were proof steps, not separate Lean modules.
Exploratory proof imports `Mathlib.GroupTheory.QuotientGroup.Basic` and
`Mathlib.RingTheory.PrincipalIdealDomain` were removed before delivery: quotient definitions
and the other imports already provide everything used.
No source-library declaration is removed. No module is withdrawn or claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The original plan is valid but substantially longer than necessary. Compatible bases
permit all roots to be adjoined at once and give exponent one, preserving the exact
statement and the unit route. The original declaration docstring records the older
cyclic-induction plan; the proof-body comment and both updated DAG proofs record the
implemented alternative. Its existing docstrings are preserved.

The live attachment is the sfb node; the module's historical blueprint tag also names
the dropped per copy. Both nodes attach the same declaration, so both proof records are
updated without making the live proof depend on the dropped copy. Existing ancestry
is incomplete: `blueprint_refs.py ancestor lem-sfb-divisible-unit-lattice-extension`
returns null; the new node retains null ancestry with an explicit inherited purpose.
No target statement, definition, signature or public import is changed.

## New nodes

`lem-sfb-full-rank-pid-smith-bases` attaches
`Submodule.exists_smith_normal_form_of_rank_eq` in
`Mathlib.LinearAlgebra.FreeModule.PID`, read with its PID, finite-basis and equal-rank
hypotheses. Its named basis/diagonal-coefficient API supplies the actual data in the
proof. LeanSearch, Loogle and grep all found this exact theorem; the complete blueprint
search found no corresponding statement. This is a Mathlib leaf, with no new proof hole
and no new Lean module. No change record is needed: the existing interface is unchanged.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
