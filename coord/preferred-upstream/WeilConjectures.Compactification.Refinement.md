## Our proofs of this upstream file that an upstream sync dropped (recovered from git history, 2026-10-23)

`coord/preferred-upstream/WeilConjectures.Compactification.Refinement.lean` is our version at commit `74684efbe30` (`git show 74684efbe30:lean/WeilConjectures/Compactification/Refinement.lean`), where these declarations were proved; in the current file they are `sorry`:

- `AlgebraicGeometry.Compactification.exists_overRefinement`: statement unchanged since then

How they were lost: `29fa402a64e` (upstream sync (scheduled): slopmaster2 5f7b33eac..a762b776d, 17 commits; 37 Lean files (deleted-here 1, source-proof 1, take 12)). The verbatim step of that sync replaced the file by the tip's text without our proof.

Re-apply on the current text: keep upstream's statements and text, put these proofs back (with the private helpers and imports they need from the old file, adapted to the current context), and deliver as usual. Do not restore the old file wholesale. If a proof needs an `import Sheaf.*` or a helper declaration in this upstream file, say so in the delivery: the maintainer then adds a row to coord/upstream-statement-exceptions.tsv, without which the next upstream sync drops the proof again.
