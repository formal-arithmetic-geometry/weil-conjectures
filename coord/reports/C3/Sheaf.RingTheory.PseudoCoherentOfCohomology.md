## What changed

Proved `DerivedCategory.isPseudoCoherent_of_homology` in
`Sheaf.RingTheory.PseudoCoherentOfCohomology`, with its original signature unchanged.
Three proved private helpers transport pseudo-coherence and m-pseudo-coherence along
isomorphisms and shift a bounded-above finite-free representative by any integer.
The proof follows Stacks Tag 066B: represent K by C, identify the shifted cohomology
terms, induct over truncations from m - 1 using the second clause of distinguished
triangle closure, and transport across the final truncation quasi-isomorphism.
The all-m criterion then gives pseudo-coherence.
Updated the existing node's proof route and dependencies to match the direct shift
construction. No statement or definition changed, and no change record is needed.

## Proved and sorry left

Closed the one original hole:
`DerivedCategory.isPseudoCoherent_of_homology`
(node `lem-weil-pbc-pseudocoherent-cohomology-implies-pseudocoherent`).
Proved 1 of 1 original sorries; added 0 holes; split off 0 statements.
There are no remaining sorries in the delivered Lean module.
The private helpers `pseudoCoherent_of_iso`, `mPseudoCoherent_of_iso`, and
`pseudoCoherent_shift` are proved as well.

Validation: the module compiled through lcompile.py without errors or warnings.
The proof uses the existing dependency declarations; delivery preflight checks its
axioms independently. No lower cohomology bound or Noetherian hypothesis was added.
The base case covers b < m and the zero object, while integer induction covers gaps
and arbitrarily long lower cohomology tails.

## No longer needed

Removed proof imports:
- `Sheaf.CategoryTheory.TruncationTriangle`: retired re-export wrapper; use
  `WeilConjectures.CategoryTheory.TruncationTriangle` directly.
- `Sheaf.RingTheory.MPseudoCoherentShift`: the cohomology terms' finite-free models
  are shifted directly, avoiding repeated use of the one-step approximation lemma.
- `Sheaf.RingTheory.MPseudoCoherent`: its definition is already made available by
  the remaining proof dependencies; no separate direct import is needed.

Removed the direct dependency and obsolete top-level tool-use approval for
`lem-pc-ring-m-pseudo-coherent-shift`. Its module remains a transitive dependency of
the existing distinguished-triangle theorem, so this is not a claim of pruning it
from the whole target closure. The m-pseudo-coherence definition node is still used.
No other declared dependency was bypassed; there are no new nodes or withdrawals.

## Where the brief, the DAG or earlier work was wrong

The dependency statements fit the argument. The older truncation wrapper is retired,
and the direct shift construction shortens the node's planned shift iteration.
No mathematical statement error was found.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
