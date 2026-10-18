## What changed

Repaired the returned delivery against the current shared files. The return said
that `FilteredHomologyTowerDifferential.lean` changed after the earlier base.
Started with its current F7-restored version, retained its public signature,
docstring and private helper, and supplied the complete representative differential
proof. The proof now applies the public, proved
`filteredHomology_tower_forward_representatives` rather than repeating its
calculation. The differential module's ordinary proof import of that module does
not expose private helpers. The canonical comparison lift is accessed from the
actual source module with `import all`.

Retained the completed normalized cycle lifts and quotient induction in
`Sheaf.CategoryTheory.FilteredHomologyTowerQuotients`. The induction constructs
cokernel comparison isomorphisms from its preceding epic map and kernel formula,
identifies the differential on simultaneous representative covers, and uses the
existing normalized homology comparison at the successor. All original theorem
signatures, including the private `tower_cycle_lifts`, stay unchanged.

Proved the previously split computation theorem
`filteredHomologyExactCouple_computations` against the explicit concrete
constructor now published by F8. Its first clause is reflexivity. Its second
unfolds the prescribed initial G and initial E identification and cancels equality
transports by substitution of integer indices. No definition is changed and no
unproved existence statement supplies arbitrary data.

Rebased the differential node on the current node, preserving the independent
review and landing records and changing only the proof fields. The other node
proof records describe the actual Lean argument. No held module of another group
is changed. The differential module is unclaimed in the current shared snapshot.

The three production modules compile together without errors or warnings.
After replacing the duplicated forward calculation with the public theorem,
the differential module compiled in 4.9 seconds. The delivery dry run performs
another complete compile with its declaration and axiom probes.

Change record: `coord/changes/filtered-homology-tower-differential-restoration.md`.

## Proved and sorry left

Original item holes closed:

- `tower_cycle_lifts` (private), node
  `lem-sp-filtered-homology-tower-quotients`.
- `CategoryTheory.filteredHomology_tower_quotients`, same node.

Additional current-base hole closed:

- `CategoryTheory.filteredHomology_tower_differential`, node
  `lem-sp-filtered-homology-tower-differential`.

The new helper `CategoryTheory.filteredHomologyExactCouple_computations`, node
`lem-sp-filtered-homology-couple-computations`, is also fully proved. It was the
single split-off hole in the returned sandbox and is no longer admitted.

Actual local hole counts: item 0; differential module 0; computation module 0.
Two of two original item holes are closed; no holes are added or split off.
These statements still use the project's existing imported theorem dependencies;
this is not a claim that their entire transitive axiom closures are sorry-free.

The computation is valid for zero complexes and arbitrary integer bidegrees,
including negative filtration indices. The quotient proof uses epic representative
covers and cancellation, without assuming projective objects. Monic normalization
fixes both lift families uniquely, and cokernel normalization fixes the comparison
isomorphisms.

## No longer needed

Removed imports from the item relative to the current base:

- `Sheaf.Algebra.Homology.FilteredComplexRepresentativeEpis`: the simultaneous
  differential representative cover supplies the required epic cover in both
  the cycle-lift and differential-transport calculations.
- `Sheaf.Algebra.Homology.FilteredComplexSubquotients` and
  `Sheaf.CategoryTheory.FilteredHomologyCoupleData`: already publicly available
  through the concrete exact-couple interface.
- `Sheaf.CategoryTheory.FilteredComplexPageDifferential`: publicly exported by
  the normalized homology interface; its theorem remains a proof dependency.
- `WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits`: no extension lemma
  from this module is used by the direct factorization argument.
- `WeilConjectures.CategoryTheory.ExactCouple` and
  `WeilConjectures.CategoryTheory.ExactCoupleConvergence`: already publicly
  re-exported by the corresponding statement interfaces.

The item node no longer directly needs
`lem-sp-filtered-complex-representative-epis`; its proof dependency is removed.
The differential uses the source
`WeilConjectures.CategoryTheory.FiniteCycleDerivedComparison` directly to access
its private comparison lift; no import of the retired Sheaf comparison proxy is
needed. The previous inline forward calculation and its private-helper import
are replaced by the public forward theorem. No other planned mathematical
ingredient or unit step is bypassed. These are local dependency removals, not a
claim that all other target consumers of these modules disappear.

## Where the brief, the DAG or earlier work was wrong

The previous delivery's base predated the F7 restoration of the differential
statement and F8's explicit constructor. Its report therefore described an
inactive differential statement and hollow constructor data. Those descriptions
are obsolete: the current differential statement is active with one admitted
proof, the concrete constructor and initial E isomorphism are explicit, and the
forward representative theorem and its private helper proofs are complete.
This repair preserves those independently landed changes and proves the
remaining differential and computation formulas against them.

The original return is repaired by starting from the current differential file,
not by resubmitting its old version. The only changes there are proof imports
and the theorem proof. Its existing signature, helper and docstring are retained.
The dependent quotient-pages module already uses the same signature, so no
consumer adaptation or target statement change is required.

The computation node retains its recorded blueprint ancestry and its actual
Mathlib search results from the original session; `searches.jsonl` is retained.
The historical unit attachment is unchanged; this delivery changes no unit route.

## New nodes

`lem-sp-filtered-homology-couple-computations` records the concrete D-object and
normalized initial-G computations in one fully proved API theorem. It mentions no
derived pages, cycle lifts, finiteness, epimorphy or quotient comparison induction.
The existing concrete construction and initialG definition are its only proof
dependencies. No remaining obligation is assigned to a new worker.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
