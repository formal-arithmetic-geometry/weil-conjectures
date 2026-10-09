# HUMAN

Questions that need the human. The maintainer and the launcher write them under "Open"; the launcher brings each to the human at once and moves it under "Answered" with the answer. The agent that asked acts on the answer, writes one line in `coord/ledger.md`, and then deletes the question and its answer from this file; what the human decided for the rest of the run is in `SETUP.md`. The file holds only what is still open or not yet acted on.

## Open

<!-- - 2026-01-01, from <session>: <question>, what waits on it, and the options with a recommendation -->
- 2026-10-09, from L (maintainer/lead): documents wanted for stage-1 proofs, listed in the Wanted table of `literature/LIST.md`. New today: Lang, *Algebra*, Ch. V §5 Thm 5.1 (for `lem-weil-unique-subfield-of-closure`); Serre, *Local Fields*, Ch. II §2 Prop. 3 (for `def-weil-l-adic-coefficient-extension`). Nothing blocks on them: until a document arrives the worker splitting the node writes the proof itself and marks it as an agent's; when it arrives the proof is rewritten from it. Recommendation: provide scans or page ranges of the Wanted rows that are standard textbooks (Lang, Serre, Hartshorne, Weibel, Mumford) first, since many nodes will cite them.
- 2026-10-09 (evening), from L (maintainer/lead): the Lean sorry `AlgebraicGeometry.Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity` (slopmaster2, BaseChangeProperty.lean 321) is now the node `lem-weil-pbc-injective-acyclicity-bounded-below`, stated from its Lean statement: for any commutative ring Λ, acyclicity of the pullbacks of *injective torsion Λ-sheaves* implies the base-change isomorphism for every bounded below complex with torsion cohomology. The worker of the target doubts it is provable as stated for general Λ (Stacks 0A4B uses injective ℤ/ℓ-sheaves; an injective ℤ/ℓ-sheaf need not be Λ-injective, and a torsion Λ-sheaf need not have a torsion injective resolution), while for proper f its conclusion is the target itself, so a worker splitting it must not prove it from the target (cycle). Nothing waits on it: the node is an item and its worker will report what the literature gives. Options: (a) confirm the Lean statement is intended (then its split must find a proof, perhaps through restriction of scalars to ℤ as the docstring of `isIso_baseChange_of_isProper` suggests); (b) restrict the Lean to Λ = ℤ or to torsion rings, which the route of the units supports. Recommendation: (b), unless the Lean authors have an argument for (a).

## Answered

<!-- - 2026-01-01, from <session>: <question> — answer (2026-01-02): <ruling> -->
