## Our proofs of this upstream file that an upstream sync dropped (recovered from git history, 2026-10-23)

`coord/preferred-upstream/WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity.lean` is our version at commit `f90ec681010` (`git show f90ec681010:lean/WeilConjectures/AlgebraicGeometry/Sites/CohomologyContinuity.lean`), where these declarations were proved; in the current file they are `sorry`:

- `AlgebraicGeometry.Etale.isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit`: statement unchanged since then

How they were lost: `57ddce9742d` (upstream sync 5f7b33eac: prefer upstream, round 1: 9 upstream file(s) take the tip's version (our changes broke WeilConjectures.AlgebraicGeometry.ConstantGroupS). After the merge our version of some upstream file no longer compiled in the new upstream context, so the file took the tip's text ("prefer upstream"); the proof needs adapting.

Re-apply on the current text: keep upstream's statements and text, put these proofs back (with the private helpers and imports they need from the old file, adapted to the current context), and deliver as usual. Do not restore the old file wholesale. If a proof needs an `import Sheaf.*` or a helper declaration in this upstream file, say so in the delivery: the maintainer then adds a row to coord/upstream-statement-exceptions.tsv, without which the next upstream sync drops the proof again.
