## What changed

Proved `Topology.exists_finite_good_stratification_refinement` in
`Sheaf.Topology.NoetherianGoodStratificationRefinement`, without changing its statement,
visibility, universes, or imports. Two proved private helpers implement the existing
six-step argument from Stacks Project, Topology, Tag 09Y5, with goodness as in Tag 09Y0.

`exists_open_piece` uses Mathlib's irreducible-component open-subset theorem and the
finite closed-cover characterization of irreducibility to find a nonempty open subset
of one original part. `exists_closed_refinement` uses well-founded induction on ambient
closed sets. Keeping all intermediate strata in the ambient space avoids separate
subspace-closure transport: their closures lie in the closed complement automatically.
The complement partition is indexed by the original index type times `Bool`, according
to membership in the closure of the chosen open piece. Empty input pieces are harmless;
the induction output always has nonempty strata. `Fin.cases` adjoins the chosen piece,
and the proof checks each frontier pair explicitly. The final closure-union clause
follows from covering and goodness.

The original DAG route and all four declared dependencies remain in use, through their
recorded Mathlib declarations. No new nodes, public declarations, or definitions are added.
No statement or definition repair, consumer adaptation, or change record is needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`Topology.exists_finite_good_stratification_refinement`
(node `lem-sfb-noetherian-good-stratification-refinement`).
Added 0 holes. Split off 0 obligations. No `sorry` remains in any delivered Lean file.
Both private helpers are fully proved.

Validation: the complete proof compiled with `lcompile.py`; the final delivery dry run
also checks compilation and declaration axioms. The construction includes the empty
space case (`Fin 0`), permits empty original parts, and places no separation assumption
on the Noetherian space. No nonempty assumption was added to the public theorem.

## No longer needed

None. No imports, nodes, modules, or declared dependencies were removed. The proof uses
the original locally closed and irreducible-component definitions, component covering,
and finite-component input. The component-open construction is supplied by Mathlib's
`TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent`.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The original proof plan is realized in Lean.
One remote compiler call returned no answer after its retry budget; rerunning the
prescribed compiler succeeded, so this did not block the work.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
