## What changed

Proved `AlgebraicGeometry.openStalk_representative_coherence` in
`Sheaf.AlgebraicGeometry.OpenStalkRepresentativeCoherence`, with the existing signature
and docstring unchanged. Added a private proof import of
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` and six proved
private helpers for composition factors, homology comparisons, and their generic combination.
The abstract exact-functor calculation avoids repeated unfolding of the scheme stalk
construction. No definitions, public statements, instances or other modules were changed.
Updated the existing node's proof and proof origin to describe the implemented calculation.

## Proved and sorry left

Closed the single hole `AlgebraicGeometry.openStalk_representative_coherence`
(node `lem-pc-open-stalk-representative-coherence`). Holes closed: 1. Holes added: 0.
No `sorry` remains in the delivered module and no intermediate statements were split off.
All six private helpers have complete proofs. Single-file compilation passed without warnings.
The final delivery dry run checks every declaration's axioms and the unchanged public signature.

## No longer needed

None. No existing imports, nodes or modules can be pruned: the open restriction,
representative stalk comparisons, and additive derived stalk isomorphism remain necessary.
The proof does not use any tensor-stalk or auxiliary chain-square hypotheses or modules.
The lemma `comparisonStalkHomologyIso_naturality` is not called explicitly: its underlying
localization-factor naturality is used directly after expanding the comparison. Its module
remains necessary for the comparison definitions and exactness instances.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The node's suggested constituent equations suffice.
The calculation applies to arbitrary exact functors, so zero complexes and zero homology
are included. The empty-open case has no point z, and the top-open case needs no separate
assumption. Doing the cancellation directly with concrete scheme stalk functors caused
expensive definitional unfolding; proving the same exact-functor calculation abstractly
and specializing it makes the unchanged statement compile within the existing 60-second limit.

## Second reading by T2

1. Compared the delivered module with the repository version. The public theorem signature and its
   docstring are unchanged byte for byte; the only module changes are the proof and one private import.
   The node changes only record the implemented proof route and origin. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. Searched for `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, `extern`, and `debug.skipKernelTC`; none occur. The helpers are
   private proved theorems, with no hollow definitions or split-off holes. Verdict: pass.
3. Reviewed the proof against the imported exact-functor and stalk comparison declarations. The
   cancellation and naturality steps establish the unchanged target for arbitrary complexes, including
   zero and empty/top-open edge cases. No new public statement was added, and no existing statement was
   weakened. Verdict: pass.
4. Checked pruning and imports. The public open-stalk module remains required by the target; the exact
   functor import is proof-only and is plain `import`. Every stated proof dependency is used by the
   specialization, and no old proof dependency can be removed. Verdict: pass.
5. Checked the DAG node and unit route. Its `proof`, `proof_deps`, and `proof_origin` match the proof,
   the target node and unit are unchanged, and no new node or change record is required. Verdict: pass.

Changed after second reading: added this review section; no Lean or DAG corrections were necessary.
