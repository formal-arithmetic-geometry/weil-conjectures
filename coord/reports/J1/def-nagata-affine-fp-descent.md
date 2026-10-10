Files written:

- `def-nagata-affine-fp-descent.json` — definition, no new nodes, Mathlib searches found no exact match.
- `citations.json` — empty because the item is a definition with no proof steps.

Attachments: none. No `WeilConjectures/` declaration carries the blueprint tag or states this finite-stage definition exactly; the nearby formalized route uses `AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated` and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation` instead.

WANTED: none.

The imported node was marked `bypassed` and had no proof. I retained its statement and existing dependencies. The dependency `def-nagata-directed-finite-upper-bound` supplies the selected common upper bound, and `lemma-nagata-filtered-colimit-finite-data` supplies simultaneous finite-stage lifts and relations; neither dependency is duplicated here. The blueprint note says this stage-by-stage construction is bypassed by the formalized approximation route.

## Review by J1

I read the item node and its unit `sk-prop-nagata-sketch-approximation`, including the unit's affine finite-presentation descent step. I checked both cited dependency statements directly: the selected-upper-bound definition introduces a finite-set upper-bound function, while the finite-data lemma states that finitely many elements and equalities lift to one stage and persist under transition. Those are exactly the two nontrivial notions used by the item; the polynomial presentation, coefficient lifts, quotient, and induced comparison are the definition's own introduced data. There are no proof steps, so `citations.json` is empty and no hypotheses are hidden in a proof. I searched the source checkout for the item tag and its key terms and found no exact declaration. I ran LeanFinder, Loogle, Mathlib grep, and LeanSearch searches for the item; the recorded results contain only general finite-presentation declarations, no exact descent definition, and LeanSearch was unavailable.

## Second reading by J1

- Item statement: checked against blueprint node `def-nagata-affine-fp-descent` (order 351) and the statements of `def-nagata-directed-finite-upper-bound` and `lemma-nagata-filtered-colimit-finite-data`; after repair it explicitly introduces the directed ring system, its colimit, the structure map, and all finite-presentation data. Verdict: agrees hypothesis by hypothesis.
- New nodes: none; the item is the sole definition node and has no proof steps.
- Dependencies: the selected-upper-bound and finite-data notions are cited inline and remain the two existing statement dependencies; no proof fact is uncited.
- Small cases: the zero ring, a field, and presentations with $n=0$ or $m=0$ are well-typed; the empty affine scheme is allowed when the colimit ring is zero.
- Mathlib and source search: checked the recorded LeanFinder, Loogle, grep, and LeanSearch searches; no exact Mathlib declaration or source-repository declaration was found (LeanSearch unavailable).

Changes made: repaired the statement's missing directed-system/colimit context and added inline citations for both dependency notions, plus the induced structure map used in $\\beta_B$. No nodes or proof steps were added.
