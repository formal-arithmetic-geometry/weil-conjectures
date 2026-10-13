## What changed

Proved `AlgebraicGeometry.affine_algebra_upper_truncation_edge` without changing its
signature or the existing public imports. Added proof imports for the natural acyclic
quasi-coherent pushforward comparison, the lower-truncation cycle formula, affine
higher-image vanishing, exact scalar restriction/derived composition, and the homology
property of truncation. Updated the existing node's proof route and dependencies.

The affine calculation makes the canonical lower-truncation projection invertible,
first over O_Y and then over f_*O_X by exact conservative scalar restriction. The
existing lower-truncation cycle formula supplies the bottom isomorphism with its
canonical cycle identity. A private abstract lemma composes it with the upper and lower
truncation maps and verifies the displayed identity using naturality, inverse
cancellation, and the mapped left-homology-data kernel/cokernel identities. Keeping this
calculation abstract avoids repeatedly unfolding scheme and ringed-space data.

Read the Stacks Project pages for Tags 0AVW and 08D4. The local literature files named by
the node were absent. The unit record has no realized statement/step nodes to bypass;
its route and target declarations are unchanged.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.affine_algebra_upper_truncation_edge`
(node `lem-sc-affine-algebra-upper-truncation-edge`). No new holes were added, and no
`sorry` remains in the delivered module. All private helpers have complete proofs.

This is a proof from existing library statements. The lower-truncation cycle formula
uses the previously stated `AlgebraicGeometry.derived_lower_truncation_unit_bridge`,
which remains another worker's item; no copy or replacement of that statement is added.

## No longer needed

No original import was removed: the four public imports support the unchanged
statement and definitions. No new nodes or modules are introduced. Removed the trial proof imports
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`: both are
publicly supplied by the used affine higher-direct-image module.

The following former proof dependencies are no longer separately invoked here:
`lem-pc-affine-vanishing` (`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`),
`lem-sc-module-cohomology-source-comparison`
(`Sheaf.AlgebraicGeometry.ModuleCohomologySourceComparison`),
`lem-pc-unbounded-derived-functor-cohomological-bound`
(`Sheaf.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound`), and
`new-qcoh-sections-left-exact-bottom` (`Sheaf.Paper.DerivedSectionsLeftExactBottom`).
Their roles are already supplied by the existing acyclic-pushforward comparison and
lower-truncation cycle formula. These modules can remain transitively reachable through
those dependencies; this delivery does not claim their global elimination.

## Where the brief, the DAG or earlier work was wrong

The prescribed affine-tail argument was already packaged in the natural acyclic
quasi-coherent derived-pushforward theorem, and the cycle normalization was already
packaged in the lower-truncation cycle formula. Reusing those declarations avoids new
intermediate statements. The original statement is valid; no hypotheses are added,
including no boundedness or K-injectivity assumption.

Initially the published build lacked the existing upper-truncation comparison and
lower-truncation cycle-formula modules. They became available during the session.

## Second reading by K3

1. Compared the delivered Lean module with the repository version. The target and all existing declaration signatures are byte-for-byte unchanged; only proof imports, private helpers, and the target proof body changed. Verdict: pass.

2. Compiled the module directly and with `--all`; both completed without errors or warnings. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof uses only existing declarations and its private helpers are fully proved. Verdict: pass.

3. Checked the DAG node against the Lean route and searched the repository for duplicate declarations. The target statement is unchanged, the revised proof dependencies match the imports used, and no new split-off statement or node was introduced. Verdict: pass.

4. Reviewed pruning and imports. The two trial proof imports were removed as documented; all remaining imports are used by the proof or public interface. The former dependency nodes listed above are no longer directly invoked. Verdict: pass.

5. Checked the unit record and route. No realized unit statement or step is bypassed; the affine acyclic pushforward comparison and lower-truncation cycle formula are used as the route records. Verdict: pass.

Changed during second reading: no Lean or DAG changes; appended this review section only.

Final validation: the delivery dry run printed OK, at commit `987df2bc95`, with
review class CODEX (changes a node file). A separate scratch copy with `#print axioms
AlgebraicGeometry.affine_algebra_upper_truncation_edge` compiled and reported exactly
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The last comes from the
existing open library dependencies described above; no new hole was introduced here.
The delivery's automated probe and preflight passed. The empty-scheme, zero-complex,
and negative-degree cases require no extra assumptions in any private helper.
