## Our proofs of this upstream file that an upstream sync dropped (recovered from git history, 2026-10-23)

`coord/preferred-upstream/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit.lean` is our version at commit `81303983ee8` (`git show 81303983ee8:lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean`), where these declarations were proved; in the current file they are `sorry`:

- `AlgebraicGeometry.ProEtale.constructibleCocone_essSurjObj`: statement unchanged since then
- `AlgebraicGeometry.ProEtale.constructibleCocone_homSurj`: statement unchanged since then

How they were lost: `27449cab40c` (upstream sync (scheduled): slopmaster2 ee65497e6..58206abfd, 17 commits; 36 Lean files (source-proof 1, take 10)). The verbatim step of that sync replaced the file by the tip's text without our proofs.

Re-apply on the current text: keep upstream's statements and text, put these proofs back (with the private helpers and imports they need from the old file, adapted to the current context), and deliver as usual. Do not restore the old file wholesale. If a proof needs an `import Sheaf.*` or a helper declaration in this upstream file, say so in the delivery: the maintainer then adds a row to coord/upstream-statement-exceptions.tsv, without which the next upstream sync drops the proof again.
