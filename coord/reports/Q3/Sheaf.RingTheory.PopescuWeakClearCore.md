## What changed

Proved `Algebra.exists_cleared_submersive_presentation_core` in
`Sheaf.RingTheory.PopescuWeakClearCore` without changing its signature, public imports,
or docstrings. Added the proof-only import `Mathlib.RingTheory.MvPolynomial.Localization`.
The proof clears each relation by `IsLocalization.surj`, proves equality of the localized
relation ideal with the evaluation kernel, and computes the determinant after column
scaling by units. It then lifts the inverse determinant through the presentation and
clears its denominator. The localization ideal-membership criterion supplies the final
scalar annihilating the residual error; a ring calculation produces the required
certificate. Updated the item's DAG proof, proof dependencies, and proof origin to match.

The source read was Stacks Project, Smoothing Ring Maps, Tag 07F9,
`lemma-delocalize-weak`, the denominator-clearing paragraphs (lines 2179–2188), in the
local literature mirror. Mathlib search used LeanFinder, Loogle, and grep through
`msearch.py`, plus source searches in both library roots and Mathlib.

## Proved and sorry left

Closed the sole original hole:
`Algebra.exists_cleared_submersive_presentation_core`
(node `lem-weil-pbc-popescu-weak-clear-core`). No holes remain and no holes were added.
This is a complete proof, not a decomposition. No new declarations, modules, or nodes.
The proof works uniformly with zero relations (empty determinant and product are 1),
without injectivity of R into its localization, and also for the zero D algebra.
The unit's statement and realized steps are untouched.

Validation: the completed file compiles cleanly with `lcompile.py`; the final delivery
check performs the declaration axiom probe and preflight. The second reader runs both the dry run and the authorized delivery.

## No longer needed

No original import was removed: both public imports provide the statement's interface.
A temporary direct import of `Mathlib.RingTheory.Localization.Ideal` was removed because
`Mathlib.RingTheory.Localization.AtPrime.Basic` already publicly imports it.

The proof no longer needs separate invocations of the planned dependency nodes
`lem-weil-pbc-polynomial-scalar-extension`, `lem-weil-pbc-localization-base-change`, or
`def-weil-pbc-module-localization`; these have been removed from this node's proof
dependencies. Polynomial localization is used directly through Mathlib's
`MvPolynomial.isLocalization`, and localization of a module is not constructed in this
proof. The Mathlib polynomial localization implementation internally uses tensor and
localized-module results, so this is pruning of the explicit DAG route, not a claim that
those Mathlib source modules disappear from the transitive import closure. No Sheaf or
WeilConjectures module is newly pruned from that closure.

## Where the brief, the DAG or earlier work was wrong

The DAG treated denominator clearing and the determinant calculation as elementary
steps; their Lean realization needs explicit polynomial localization instances, unit
ideal-membership cancellation, evaluation compatibility, and determinant scaling.
All are available in Mathlib and the existing presentation interface. No statement or
source error was found. The final finite-linear-combination clearing argument can be
replaced directly by `IsLocalization.algebraMap_mem_map_algebraMap_iff`; this also
handles localization maps with nonzero kernel.


## Second reading by Q3

1. **Interface preservation — pass.** Compared the sole delivered module with the
   repository by `diff` and checked the existing theorem signature byte for byte.
   The only Lean differences are its proof and one plain, proof-only Mathlib import.
   No definition, statement, docstring, public import, or visibility changes.
2. **Proof and trust — pass.** Read the complete proof: polynomial localization
   clears each equation; cancellation by a unit proves kernel equality; derivative
   compatibility and column scaling prove the determinant is invertible; a lifted
   inverse and localization ideal membership give the certificate. Compilation is
   clean on retry (32.5 seconds); the initial attempt hit the 60-second limit during
   concurrent machine load. No forbidden declarations, hollow definitions, or sorry
   occur. The independent scratch `#print axioms` compiled in 3.4 seconds and shows
   exactly propext, Classical.choice, and Quot.sound; the delivery also runs its probe.
3. **Split statements — pass, none.** No new declarations, modules, nodes, or holes
   were introduced. The choices in this proof use proved localization surjectivity,
   presentation surjectivity, and invertibility, all within a theorem proof; no data
   definition chooses an arbitrary witness from an unproved existence theorem.
   For c = 0 the determinant and denominator product are 1, so the same argument
   applies. No injectivity or nonzero hypothesis on D is used: the localization
   ideal criterion absorbs kernel errors even for rings with zero divisors.
4. **Shortest route and pruning — pass.** Checked the source's denominator-clearing
   paragraphs in the local Stacks mirror and Mathlib's polynomial localization and
   ideal-membership implementations. Searched presentation coefficient descent,
   Jacobian certificates, and the project's Popescu modules: no shorter theorem
   supplies this certificate over the fixed, possibly noninjectively localized R.
   The three removed old proof dependencies are all listed under No longer needed.
   The two public imports supply statement types; the added plain import supplies
   the polynomial-localization instance. No imported Sheaf module is removed.
   Read sk-thm-p1's realized statement and steps: this internal algebra lemma changes
   none of them and preserves its enclosing denominator-clearing route.
5. **DAG agreement — pass.** Verified that only proof, proof_deps, and proof_origin
   differ in the node, and proof_deps is precisely the union of the step uses.
   The five steps follow the Lean proof and retain its Stacks source. No new-node
   or statement-change records are required.

Second-reading changes: corrected the report's obsolete dry-run-only instruction
and appended this review. The Lean proof and node needed no repair.
