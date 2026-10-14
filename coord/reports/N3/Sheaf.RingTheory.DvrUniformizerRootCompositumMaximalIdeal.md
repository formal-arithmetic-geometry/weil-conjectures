## What changed

Proved `RingTheory.dvr_uniformizer_root_compositum_formallyUnramifiedData` with
all signatures, visibility and docstrings preserved. The maximal-ideal theorem's
proof now applies Mathlib's criterion directly. The construction follows the companion
`DvrUniformizerRootCompositumResidue` proof: construct the standard root DVR,
identify its root with the image of a U-uniformizer times a unit, obtain the
unramified intermediate model, and apply arbitrary DVR compositum base change.

Added proof-only imports for the local unramified criterion, multiplicity API, `DvrUniformizerRootAlgebra`,
`DvrStandardRootUnramifiedModel`, and `DvrUnramifiedCompositumBaseChange`.
Updated the formally-unramified-data node's proof and dependencies to match.

## Proved and sorry left

Closed 1 of 1 existing holes:
`RingTheory.dvr_uniformizer_root_compositum_formallyUnramifiedData`
(node `lem-sbc-dvr-uniformizer-root-compositum-formally-unramified-data`).
No holes remain in the module; no new holes or statements were added.
`RingTheory.dvr_uniformizer_root_compositum_map_maximalIdeal` remains proved by
its existing application of this now-proved theorem and the local criterion.
The local compile and delivery axiom probe validate the proof.

## No longer needed

Removed proof import `Sheaf.RingTheory.DvrMapMaximalIdealOfFormallyUnramified`;
its wrapper is replaced by Mathlib's `Algebra.FormallyUnramified.map_maximalIdeal`
directly. The module is no longer needed by this proof. All original public
imports are preserved; every added proof import supplies a used ingredient. The original data node had no proof dependencies to prune. The residue
companion theorem itself is not imported, only its underlying model and base-change
results. No new normalization or ramification-index lemmas are required.

## Where the brief, the DAG or earlier work was wrong

The initial repository snapshot had a single maximal-ideal hole. The first dry run
refreshed the base to a version factoring this through the formally-unramified-data
theorem. This delivery preserves that newer interface and closes its remaining hole.
The data node's original proof had no dependencies recorded; its now-proved
standard-root model and arbitrary DVR base-change dependencies are made explicit.
The unit route is preserved. The unit hypothesis excludes e=0; e=1 uses the same
proof. No finiteness assumption on A/B is added.

## Second reading by N3

1. Compared the complete delivered module with the repository version using `diff`.
   Both existing declaration signatures, visibility and docstrings are byte for byte
   unchanged. Only proof bodies and proof-only imports differ; no definition,
   statement or change record is added. Verdict: pass.
2. Compiled the delivered file locally with `lcompile.py`, with no errors or
   warnings. Compiled a scratch copy with `#print axioms` for both
   `RingTheory.dvr_uniformizer_root_compositum_formallyUnramifiedData` and
   `RingTheory.dvr_uniformizer_root_compositum_map_maximalIdeal`: each uses only
   `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. There are no
   remaining holes, forbidden declarations, or hollow definitions. Verdict: pass.
3. No new statements or split-off holes exist. Checked the signatures and actual
   constructions of the standard-root algebra, standard-root unramified model,
   and compositum base-change theorems. The associated-power calculation gives
   exactly the unit relation required by the model; its fraction-field factorization
   supplies exactly the generation hypothesis required by base change. The model
   is explicitly constructed in its existing proof, not an arbitrary unproved
   witness. The unit assumption excludes e=0 in the nontrivial DVR B; e=1 uses
   the same argument. Verdict: pass.
4. Searched the DVR modules by compositum, root, unramified and maximal-ideal
   concepts; checked the companion residue proof and the existing Mathlib wrapper.
   Repeated Loogle search confirms the exact type of
   `Algebra.FormallyUnramified.map_maximalIdeal`. The direct criterion is the
   shorter final step, and no existing theorem bypasses the root-model construction
   for the data statement. All added imports are proof-only and used; original
   public imports provide signature types. The removed wrapper and the absence
   of old data-node dependencies are recorded under No longer needed. Read
   `dag/units/sk-prop-input-spreading.json`: its route and realized fields are
   unchanged (the realized arrays are already empty in the repository, and this
   delivery does not claim to repair them). Verdict: pass.
5. Compared the node diff and checked all three named dependency nodes against
   their Lean declarations. The four proof steps describe the root construction,
   associated-power/locality calculation, unramified model, and base change as
   written; proof_deps is precisely their non-elementary node union. The unchanged
   maximal-ideal node still cites the data theorem followed by the local criterion.
   No new node fields or statement changes need checking. Verdict: pass.

Second reading changed only this report: added the independent checks and explicit
axiom results. No Lean or DAG repair was needed.
