## Our proofs of this upstream file that an upstream sync dropped (recovered from git history, 2026-10-23)

`coord/preferred-upstream/WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange.lean` is our version at commit `438e3d04508` (`git show 438e3d04508:lean/WeilConjectures/SixFunctors/ProEtale/BaseChange/SmoothBaseChange.lean`), where these declarations were proved; in the current file they are `sorry`:

- `AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap`: statement unchanged since then

How they were lost: `f90ec681010` (upstream sync (scheduled): slopmaster2 e9ba49ac4..5f7b33eac, 168 commits; 5330 Lean files (conflict 1, imports 2, merged 1, source-proof 1, take 279; conflicts ). The 10-20 sync gave the file the tip's text; the old proof uses a helper (comparison_mate_transport) and section variables of the old file, so it could not be put back mechanically (tried 2026-10-23).

Re-apply on the current text: keep upstream's statements and text, put these proofs back (with the private helpers and imports they need from the old file, adapted to the current context), and deliver as usual. Do not restore the old file wholesale. If a proof needs an `import Sheaf.*` or a helper declaration in this upstream file, say so in the delivery: the maintainer then adds a row to coord/upstream-statement-exceptions.tsv, without which the next upstream sync drops the proof again.
