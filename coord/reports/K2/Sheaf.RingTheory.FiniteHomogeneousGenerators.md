## What changed

Completed the retirement item listed in coord/retire-items.tsv. Withdrew
Sheaf.RingTheory.FiniteHomogeneousGenerators and replaced the sole remaining
consumer's private import in Sheaf.RingTheory.GradedKernelInternal by
WeilConjectures.RingTheory.FiniteHomogeneousGenerators. Updated the existing
DAG node lem-sc-p1-finite-homogeneous-generators to the proved upstream declaration.
The upstream signature differs only in an unused bound proof variable's name;
all mathematical hypotheses and conclusions agree, including empty generating families.
No upstream file, target statement, consumer signature, or consumer proof changes.

Repair of return C-fe0bd (head fe0bdad7fe): refreshed GradedKernelInternal from
the current sheaf-dag source after landing be63bcda32a. Preserved that landing's
upstream GradedKernelFinite import, its reduced theorem call, and the two local
uses of otherwise-unused hypotheses. Applied only the one-line import change
from Sheaf.RingTheory.FiniteHomogeneousGenerators to its upstream twin.
Compared with the returned packet, this avoids reverting the concurrent landing.

Validation: the refreshed sole remaining consumer compiled cleanly through
lcompile.py (exit 0, 2.8 seconds). A source-closure scan found no environment containing both
Sheaf and upstream twins. Exact comparison of the theorem text and proof, after
renaming the unused existential proof binder, succeeds. The upstream finite
spanning-set proof includes the zero module and empty generating-family cases.

Change record: coord/changes/K2-retire-finite-homogeneous-generators.md.

## Proved and sorry left

The assigned retirement starts with zero holes. Closed: none (0 of 0).
Added: none. Split off: none. Sorry left in delivered modules: none.
MvPolynomial.exists_finite_homogeneous_generators already has a complete proof
in the upstream twin. The consumer's graded_kernel_internal_finite and private
finite_homogeneous_spanning retain their complete proofs using that theorem.
This delivery is a duplicate-module retirement, not a new theorem proof.

## No longer needed

Pruned module: Sheaf.RingTheory.FiniteHomogeneousGenerators.
Removed import: import Sheaf.RingTheory.FiniteHomogeneousGenerators from
Sheaf.RingTheory.GradedKernelInternal; replaced by its upstream twin.
No DAG node or mathematical dependency is pruned: the existing node now points
at the upstream theorem, whose proof uses the same Mathlib lemmas.
The retired copy's three public Mathlib imports and private linear-combination
import are already present verbatim in the upstream twin.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes proof work, but this module is already proved
and the current queue explicitly marks it retire (zero sorry). The retirement
API-difference flag reflects only changing the unused existential binder hm to _.
The retirement table lists three consumers; current sources and downstream.py
find only Sheaf.RingTheory.GradedKernelInternal. The other two Sheaf consumers
have already been removed; their upstream twins use the correct upstream import.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
