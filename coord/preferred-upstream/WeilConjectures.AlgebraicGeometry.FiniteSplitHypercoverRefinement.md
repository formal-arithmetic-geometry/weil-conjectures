## Our proof of this upstream file that an upstream sync dropped (recovered from git history, 2026-10-23)

`coord/preferred-upstream/WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverRefinement.lean` is our version at commit `438e3d04508` (`git show 438e3d04508:lean/WeilConjectures/AlgebraicGeometry/FiniteSplitHypercoverRefinement.lean`), where `AlgebraicGeometry.exists_refinement_solving_local_requirements` was proved (statement unchanged since then); in the current file it is `sorry`. The other two proofs of this file (exists_and_cofiltered, exists_truncated_refinement) were restored on 2026-10-23 (landing 20261023T143847-L-3599783).

How it was lost: `f90ec681010` (upstream sync 5f7b33eac) gave the file the tip's text. The old proof uses FiniteSplitReplacementStage, StageSolves and exists_local_replacement_stage_zero, which are not in the current library under these names, so it could not be put back mechanically.

Re-apply on the current text: keep upstream's statements and text, put the proof back (with what it needs, adapted to the current context), and deliver as usual. Do not restore the old file wholesale. If a proof needs an `import Sheaf.*` or a helper declaration in this upstream file, say so in the delivery: the maintainer then adds a row to coord/upstream-statement-exceptions.tsv, without which the next upstream sync drops the proof again.
