## What changed

Completed `AlgebraicGeometry.Etale.etale_filtered_step_cohomology_compatibility`
in `Sheaf.AlgebraicGeometry.EtaleFilteredStepCohomology`, with its existing
signature and the canonical isomorphism definition unchanged. Two proved private
helpers establish naturality of the K-injective derived-unit comparison and of
`resolutionEtaleCohomologyIso`. The public proof constructs the augmentation
homotopy from `T.over_K`, applies that naturality, uses the sections-lift equation,
and cancels the homology isomorphism of the lift.

Added two modules with one named intermediate theorem each:
`Sheaf.AlgebraicGeometry.EtaleRestrictedAugmentationInclusion` supplies the
explicit sheaf-total inclusion and its augmentation equation;
`Sheaf.AlgebraicGeometry.EtaleRestrictedSectionsComparisonMap` supplies the
chain-level equation after global sections. Both are strictly earlier parts of
the argument, with no homology degree, derived cohomology map, or filtered-step
cohomology isomorphism in their conclusions. They construct no data by choice
from an unproved existence statement. The inclusion is an explicit totalized map.

The added import is proof-only. No existing signature, public import, definition,
target, or other module is adapted. The compatibility node now follows the Lean
proof. The unit `sk-prop-h2` has no realized nodes here; its route is unchanged.

## Proved and sorry left

Closed the item's sole hole:
`AlgebraicGeometry.Etale.etale_filtered_step_cohomology_compatibility`
(node `lem-weil-pbc-etale-filtered-step-cohomology-compatibility`). The item now
contains zero sorries. Its already completed isomorphism-existence theorem and
final existential theorem remain completed with their original signatures.

Added two holes, each with whole proof `:= by sorry`:

- `AlgebraicGeometry.Etale.etaleRestrictedAugmentation_inclusion`, node
  `lem-weil-pbc-etale-restricted-augmentation-inclusion`.
- `AlgebraicGeometry.Etale.etaleRestrictedSections_comparison_map`, node
  `lem-weil-pbc-etale-restricted-sections-comparison-map`.

This is a decomposition: one upper hole closed, two strictly earlier holes
added, not a claim of a fully sorry-free proof. Each new theorem has its source
and a complete proof in words in its docstring and node. The existing imported
sections-factorization and sections-lift-isomorphism holes are unchanged.
All three delivered modules compile locally without warnings. The delivery
checker supplies the axiom probe; only standard axioms and existing/new named
sorry dependencies are expected.

## No longer needed

Removed the direct proof import
`Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple`. The compatibility proof
no longer uses `lem-sp-kinjective-comparison-principle`: the chain comparison is
explicit, and naturality plus the given augmentation homotopy suffices. This is
pruning of this proof dependency, not a claim that the module is unreachable
from every other target branch. All remaining public imports serve the existing
statements or exposed canonical-isomorphism definition; none is removed.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped at the homotopy comparison. The augmentation
comparison and the finite-diagonal sections calculation can be stated as genuine
chain-level intermediate equations. Once those two steps are isolated, the
homotopy and all derived-unit, homology, and isomorphism-cancellation glue are
proved in Lean. No additional K-injective comparison-existence theorem is needed.

An attempt to prove the augmentation equation by unfolding the mapped total
and extension functors led to the 60-second compiler limit. That unfinished
proof was removed: the delivery keeps this step as the named public theorem
with exactly `:= by sorry`, rather than retaining a partial proof, changing a
definition or increasing the time limit.

Edge cases checked mathematically before stating the intermediate theorems:
for n < q the truncated source is zero; retained degrees cancel truncation
projection/inclusion; negative resolution degrees and empty diagonals are zero;
zero complexes and arbitrary negative q use the same formulas. Neither theorem
adds a positivity assumption or selects an arbitrary cohomology isomorphism.

## New nodes

`lem-weil-pbc-etale-restricted-augmentation-inclusion` records the explicit
totalized column inclusion and its equation with the restricted augmentation.
Its module is `Sheaf.AlgebraicGeometry.EtaleRestrictedAugmentationInclusion`.

`lem-weil-pbc-etale-restricted-sections-comparison-map` records equality between
sections of the sheaf-resolution comparison and the prescribed sections inclusion
followed by `T.w`. Its module is
`Sheaf.AlgebraicGeometry.EtaleRestrictedSectionsComparisonMap`.

Both inherit chapter `sec-curve-estimates` and unit `sk-prop-h2`, cite Stacks
Tags 015J and 0133, record LeanFinder/Loogle/grep searches and the unavailable
LeanSearch service, and record the unsuccessful whole-blueprint duplicate search.
No change record is needed: every existing public interface is unchanged.

## Second reading by C2

1. Compared the delivered module with the repository version. The existing theorem signatures and canonical isomorphism definition are unchanged; only the proof import, proof body, and the two new modules differ. Verdict: pass.

2. Compiled all three delivered modules with `lcompile.py`. The target theorem has no `sorry`; the only remaining sorries are the two named split-off public theorems, with no hollow definitions or forbidden declarations. Verdict: pass.

3. Checked the two split-off equations against the explicit total and sections constructions, edge cases, and their docstrings and DAG nodes. They are genuine earlier chain-level statements and strictly weaker than the target. Verdict: pass.

4. Reviewed the proof route and imports. The proof uses the explicit augmentation and sections equations, derived-unit naturality, and homology cancellation; the removed K-injective comparison import is unused. Verdict: pass.

5. Checked the compatibility node proof, proof dependencies, proof origin, and unit route against the Lean proof. The unit `sk-prop-h2` route remains represented. Verdict: pass.

Changed nothing in the proof during second reading; appended this review only.
