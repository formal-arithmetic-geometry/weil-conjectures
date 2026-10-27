## What changed

Filled the three proofs in `Sheaf.CategoryTheory.ResolvedTotalComparisonDescent` along
its existing seven-step DAG plan. The proof imports
`Sheaf.CategoryTheory.InjectiveFiniteTotalDerivedComparison` privately and uses its
summand-normalized natural chain comparison, total quasi-isomorphisms, and total and
column K-injectivity. Private proved helpers package the ordinary derived unit as a
natural transformation, transport it through extension and totalization, and invert
its naturality square.

The common-resolution proof constructs the five augmented replacements and checks
the four strict augmentation squares. The descent proof constructs the total and
column comparisons from the inverse units. Each localized augmented leg is the
source comparison inverse followed by the target comparison; induction proves the
zigzag formula, and cancellation proves common-resolution independence and the
identity, composition, and strict-square choice compatibility clauses.

## Proved and sorry left

Closed these three original holes:
- `CategoryTheory.ResolvedTotal.mapped_leg_quasiIso`;
- `CategoryTheory.ResolvedTotal.common_resolution_legs`;
- `CategoryTheory.ResolvedTotal.resolved_total_comparison_descent`.

No holes added or split off. No `sorry` remains in the delivered module. This is a
proof from the existing declared dependency
`CategoryTheory.injective_finite_total_derived_comparison`, whose own proof remains
an independent stage-3 item.

Validation: the full module compiled via `lcompile.py` in 13.9 seconds; the final
delivery reruns compilation and the project preflight with its axiom probes.

## No longer needed

None. No imports or DAG dependencies were removed. The existing route is used;
there are no withdrawn modules or nodes. The Mathlib object-resolution naturality
search hits do not state naturality of cosimplicial finite totals, so the proof uses
the declared finite-total comparison and proves its descent here.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. All existing public signatures,
definition bodies, and public imports are preserved. The arbitrary-quasi-isomorphism
comparison dependency is used only for its finite-total and K-injectivity clauses;
the actual ordinary right-derived unit is inverted directly using the upstream
`rightDerivedFunctorObjQIso`, as the item's normalization requires.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
