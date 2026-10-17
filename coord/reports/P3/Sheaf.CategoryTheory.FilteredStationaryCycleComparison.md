## What changed

Repaired the returned delivery against the current shared repository version of
`lean/Sheaf/CategoryTheory/FilteredStationaryCycleComparison.lean`. The current
version already proves every declaration. Preserved that proof, including its
short Mathlib `CategoryTheory.Limits.pullback_equalizer` calculation in the private
`quotient_kernel` helper, instead of restoring the longer retained sandbox proof.
Removed the unused proof-only import of
`Sheaf.CategoryTheory.DerivedCoupleKernelIdentities`. The second reading also
removed the redundant proof-only import `Mathlib.CategoryTheory.Abelian.Exact`.
These remove unnecessary direct dependencies. Updated the current node's
proof metadata and removed its obsolete derived-couple proof dependency.

All existing signatures, visibility, definitions and target statements are
unchanged. No consumer adaptation or interface change record is needed. The
unit `sk-prop-h2` and its realized route are unchanged.

Validation: the edited single file compiles cleanly with `lcompile.py`.
Explicit `#print axioms` probes on all eight declarations show only `propext`,
`Classical.choice`, and `Quot.sound`. The required dry run also checks every
declaration with its axiom probe.

## Proved and sorry left

The current baseline contains 0 holes; this repair closes 0 of 0 and adds 0.
No sorry remains in the delivered module. In particular, the private
`CategoryTheory.stationary_projection_kernel` and public
`CategoryTheory.filteredStationary_cycle_comparison` were already completely
proved in the current shared repository and retain those proofs. The earlier
report's claim of closing one hole applies to its superseded base, not this repair.
No theorem is split off and no module is added.

## No longer needed

Removed the proof-only import
`Sheaf.CategoryTheory.DerivedCoupleKernelIdentities` and the node dependency
`lem-sp-derived-couple-kernel-identities`. Neither that module nor its upstream
replacement `WeilConjectures.CategoryTheory.DerivedCoupleKernelIdentities` is
needed by this proof. Other library users may still need them. Mathlib's
`pullback_equalizer` already supplies the general kernel pullback identity.
The remaining normalized-presentation import supplies its proved subobject
helpers; its object-only comparison theorem is not applied. No other route or
module is pruned. Also removed the redundant proof-only import
`Mathlib.CategoryTheory.Abelian.Exact`; its declarations remain available through
the retained imports, and compiling without it succeeds.

## Where the brief, the DAG or earlier work was wrong

The return identified an overlapping landing after the previous delivery base.
The current file already contains the complete stationary kernel proof and a
shorter quotient-kernel calculation than the retained sandbox version. Reapplied
only the still-needed dependency pruning to that current file. This is a
substantive import and proof-dependency removal, not an unchanged re-push.

The current node incorrectly described a call to the private derived-couple
pullback-kernel helper. Its proof metadata now records the Mathlib lemma actually
used. Loogle confirms `CategoryTheory.Limits.pullback_equalizer` in
`Mathlib.CategoryTheory.Subobject.Limits`; local source inspection confirms its
specialization to kernels. No mathematical statement or definition is changed.

## Second reading by P3

1. **Signatures and statements.** Compared the delivered module with the shared
   repository version. Every existing declaration, visibility, definition, and
   target statement is byte-for-byte unchanged. The Lean edits remove two
   unused or redundant proof-only imports. The node statement and all target
   hypotheses and conclusions are unchanged.

2. **Proof and axioms.** Compiled the delivered module with `lcompile.py`; it
   succeeds without errors or warnings. The file has no `sorry`, `axiom`,
   `unsafe`, `opaque`, `extern`, or `implemented_by`. Explicit `#print axioms`
   probes for all eight declarations show exactly `propext`,
   `Classical.choice`, and `Quot.sound`.

3. **Split-off statements.** No statements were split off and no new nodes were
   added. The existing private helpers are genuine intermediate subobject
   calculations, not restatements of the target. The existing quotient-kernel
   calculation uses Mathlib's `pullback_equalizer`, which is already available
   and needs no node. Zero complexes, zero graded pieces, and r=1 introduce no
   excluded case or extra hypothesis.

4. **Pruning and route.** The removed derived-couple import is unused by the
   current proof; the quotient-kernel calculation directly uses
   `CategoryTheory.Limits.pullback_equalizer`. The corresponding old DAG
   dependency was removed. The normalized-presentation, cohomology-image,
   differential-cover, page-differential, and filtered-complex dependencies remain
   because the proof uses them. Individual removal experiments for the three
   retained proof-only Sheaf imports fail with missing declarations. The public
   homological-complex import is required by the target
   signature (removal fails at `homology`, `homologyMap`, and `cycles`). Removed
   the redundant direct Mathlib exactness import after a successful compile
   without it. The unit `sk-prop-h2` is unchanged; its `realized` statement and
   step lists are empty, and this dependency pruning introduces no unit bypass.
   Read `homology.tex`, especially `equation-graded-cohomology` and the proof of
   `lemma-compute-cohomology-filtered-complex`: the denominator is precisely
   `(A intersect B) + (A' intersect Z)`. In the Lean proof the upper bound kills
   the target representative differential in `actual_cycles_cover`; the lower
   bound identifies page boundaries in `stationary_projection_kernel`; `ha` and
   `hepi` identify the transported image filtration. The two epic projections
   then have equal kernels, and `Abelian.epiDesc` constructs inverse maps.

5. **DAG agreement.** The node's `proof`, `proof_deps`, and `proof_origin` now
   describe the proof as written, including the Mathlib pullback calculation and
   the absence of the derived-couple helper. No change record or forced
   adaptation is needed. The delivery dry run passes as a CODEX node-metadata
   change.

The second reader additionally removed `Mathlib.CategoryTheory.Abelian.Exact`
and updated this report. The first worker's derived-couple pruning and node
metadata repair are retained; no proof body was rewritten.
