## Our proofs of this upstream file that an upstream sync dropped (recovered from git history, 2026-10-23)

`coord/preferred-upstream/WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory.lean` is our version at commit `94f45b099b4` (`git show 94f45b099b4:lean/WeilConjectures/ConstructibleSheaf/ProEtaleModule/DerivedCategory.lean`), where these declarations were proved; in the current file they are `sorry`:

- `AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible`: statement **changed upstream since then**: the old proof is a starting point only

How they were lost: `bcf29a20283` (upstream-sync: merge slopmaster2 e47efb5a5 directly into sheaf-dag, with the Poincare duality PR #1474 files). Upstream restated the declaration in that sync.

Re-apply on the current text: keep upstream's statements and text, put these proofs back (with the private helpers and imports they need from the old file, adapted to the current context), and deliver as usual. Do not restore the old file wholesale. If a proof needs an `import Sheaf.*` or a helper declaration in this upstream file, say so in the delivery: the maintainer then adds a row to coord/upstream-statement-exceptions.tsv, without which the next upstream sync drops the proof again.
What changed: the old statement took closure of constructible modules under kernels, cokernels and extensions as instance hypotheses on `R`; the current one is for the finiteness coefficients `condensedRingObj Λ X` on a noetherian scheme and must prove that closure (Bhatt–Scholze, Section 6.8; the module docstring shows it is false for a general `R`). The old proof covers only the step from the closure properties to the triangulated subcategory.
