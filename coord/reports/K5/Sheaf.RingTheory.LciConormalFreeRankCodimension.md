## What changed

Retired Sheaf.RingTheory.LciConormalFreeRankCodimension in favour of the official
WeilConjectures.RingTheory.LciConormalFreeRankCodimension, as assigned in
coord/retire-items.tsv. The public theorem
Ideal.exists_basis_cotangent_localization_of_completeIntersection has exactly the
same signature in both modules. The apparent API difference is only the unused
private principal_ci_presentation_dimension helper; its proof is inline upstream.

Both current direct consumers, Sheaf.RingTheory.LocalCompleteIntersectionFieldChange
and Sheaf.TraceFormula.LciFieldChangeLocal, now import the official module. Each
consumer changes one private import line only. The existing conormal-rank node's
Lean attachment and proof metadata point at the official proof. No source-library
file or target changes. Change record:
coord/changes/K5-retire-lci-conormal-free-rank-codimension.md.

## Proved and sorry left

This is a zero-hole duplicate retirement, not a new proof: 0 of 0 item holes
closed, 0 holes added, 0 split off. The already proved official
Ideal.exists_basis_cotangent_localization_of_completeIntersection replaces the
copy. Both adapted consumers compile without errors or warnings through lcompile.py.
A separate signature check applies the official theorem to the exact old statement;
#print axioms reports only propext, Classical.choice and Quot.sound.

The two consumer holes are unchanged:
- Algebra.isLocalCompleteIntersection_fieldChange
  (lem-weil-pbc-lci-field-change).
- Algebra.isCompleteIntersectionLocal_fieldChange
  (lem-trf-lci-field-change-local).

## No longer needed

The duplicate module Sheaf.RingTheory.LciConormalFreeRankCodimension and its two
private helpers Ideal.basis_of_stably_free and
Ideal.principal_ci_presentation_dimension are withdrawn. The two direct imports
of the copy are replaced with imports of the official module. No mathematical
DAG dependency is pruned: the same conormal theorem, equidimensionality, stable
conormal comparison, and local finite-free rank argument remain in the official
proof. No unit statement or proof step is bypassed. Other upstream declarations
and their dependencies remain untouched.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief does not identify the retirement request: the module
already has zero sorries and is a depth-zero retirement item. The inventory's
DIFFERENT flag refers to a private helper, not an actual public API difference.
Its historical consumer list has four entries; the current source has only the
two field-change consumers, because the syntomic consumers already import the
official twin. The node is preserved with its unchanged mathematical statement,
and the official theorem keeps the same edge cases (zero variables or equations;
the prime excludes the zero-ring branch).

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
