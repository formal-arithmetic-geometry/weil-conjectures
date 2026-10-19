## Worker report

Files written: `dag/nodes/sec-deligne-laumon-a1/lem-per-uniformization-complete-local-descent.json` and the repaired child `lem-per-alteration-cover-closed-fibre-shrink`, whose statement was replaced by the corrected inductive gluing statement. The item has seven proof steps and remains a statement-only stage-1 split. No Lean was written and no compiler or build tool was run.

## New nodes

- `lem-per-henselian-normal-completion-preparation`, statement-only, Mathlib no match.
- `lem-per-marked-finite-diagram-approximation`, statement-only, Mathlib no match.
- `lem-per-alteration-cover-approximation`, statement-only, Mathlib no match.
- `lem-per-henselian-regular-pair-spreading`, statement-only, Mathlib no match.
- `lem-per-alteration-cover-closed-fibre-shrink`, statement-only, Mathlib no match; its returned false shrinking statement was replaced by the corrected gluing statement.

Attachments: none. The source search for the exact item tag, uniformization, alteration, and each child notion found no finished declaration under `WeilConjectures/`.

WANTED: none. ILO and the cited Stacks texts are available locally.

## Return repair

The returned child `lem-per-alteration-cover-closed-fibre-shrink` asserted that an arbitrary open neighborhood of every closed fibre preserves an `\ell'`-alteration cover. The supplied Nisnevich and complete-regular counterexamples show that assertion is false. I replaced that node statement with the corrected gluing statement and removed the false assertion from the item's proof and citations. The correction follows the requested induction: at each non-closed point use the lower-dimensional induction hypothesis, spread the resulting regular marked family to a residue-field-preserving pointed etale neighborhood, extract finitely many neighborhoods by complete decomposition, and combine those families with the regular neighborhoods of the closed fibre. Step 4 of the item now gives this argument explicitly and cites the corrected child, the spreading theorem, finite completely decomposed extraction, and alteration cover calculus.

## Review by Q142

I reread ILO Exposé III Proposition 6.2 (printed pp. 43--45), including the completion/approximation discussion on p. 44, Exposé III sections 2, 3.1, 5.1 and 5.4, Exposé II Corollary 2.2.4 and Proposition 4.1.1, and IX 1.3 (p. 132). I also reread every statement cited by each item step. Steps 1--3 still use the preparation, complete-local excellence, marked finite-diagram approximation, alteration-cover approximation, finite-presentation, and henselian-pair statements exactly as those nodes state them. Step 4 no longer takes the false implication from an arbitrary closed-fibre shrink. It uses the lower-dimensional induction hypothesis, then the statement of `lem-per-henselian-regular-pair-spreading` (regular marked families spread to pointed etale neighborhoods), `lem-per-completely-decomposed-etale-finite-subcover` (pointwise residue-field-equal lifts have a finite subfamily), `lem-per-alteration-cover-closed-fibre-shrink` (the precise conditional gluing conclusion), and `def-per-prime-to-ell-alteration-topology`. Steps 5--7 retain the earlier verified normalization, spreading, cover-calculus, and dimension arguments.

For the five retained children I checked their hypotheses against the cited ILO and Stacks places: preparation is for reduced quasi-excellent local rings; marked approximation includes all components and intersections; cover approximation has no regularity hypothesis; regular-pair spreading preserves the specified family and boundary diagram; and the new gluing node assumes a finite closed-fibre family plus pointwise lower-dimensional families and concludes only the finite glued cover. The new node was searched before creation with LeanFinder, Loogle and Mathlib grep; all gave no matching theorem. Existing DAG and blueprint searches found no duplicate. The corrected node is the only node cited in Step 4 and in `citations.json`; no false shrinking assertion remains.

I tested the new gluing statement on the supplied counterexamples: it does not assert that either `\{W_1,W_2\}` or an arbitrary singleton shrink covers; the hypotheses require the additional pointwise lower-dimensional families. I also checked dimension zero, a henselian DVR, an empty boundary, and the empty scheme. The bounded induction uses only lower-dimensional local rings, so no global finite-dimension bound is introduced; the unbounded assertion is obtained by the same strong induction separately at each finite local dimension.

## Source error

ILO II 4.1.1 is an assertion for the ordinary alteration topology with Zariski generators. The prime-to-`\ell` parenthetical in ILO III 6.2 does not justify arbitrary closed-fibre shrinking, and the omitted locus need not be closed. The old child therefore had a false statement. The repaired route is the dimension induction described above; no claim that arbitrary `U_i` preserve a prime-to-`\ell` cover remains.

## Not duplicates

`lem-per-alteration-cover-closed-fibre-shrink` vs `lem-per-alteration-cover-calculus`: the returned version claimed every open neighborhood of each closed fibre remains covering; the repaired statement assumes additional regular pointwise families on finitely many pointed etale neighborhoods and concludes a glued family. It is strictly conditional and does not imply arbitrary shrinking.

`lem-per-henselian-normal-completion-preparation` vs `lem-sc-strict-henselization-dimension`: the existing node concerns strict henselization dimension only; the new preparation statement also gives componentwise normalization, normal completions, faithful flatness, and nowhere-density preservation.

`lem-per-marked-finite-diagram-approximation` vs existing approximation nodes: those nodes concern formal algebraization or module data; this statement simultaneously descends regular schemes, all boundary components and all scheme-theoretic intersections near the closed fibre.


## Unfinished work

The item is repaired and fully split. The five original statement-only children remain unsplit, as required for stage 1; the corrected gluing child is also statement-only. Independent maintainer review remains external to this worker report.

lem-per-henselian-normal-completion-preparation vs lem-sc-filtered-colimit-prime-chain-contraction: the existing node contracts prime chains in arbitrary filtered colimits; the repaired node concerns ordinary henselization, componentwise normalization, normal completions, and nowhere-density.

lem-per-henselian-normal-completion-preparation vs lem-sc-filtered-colimit-prime-chain-dimension-bound: the existing node gives only a dimension bound for filtered-colimit prime chains; the repaired node gives henselian normalization and completion properties for quasi-excellent local rings.

lem-per-henselian-normal-completion-preparation vs lem-sc-filtered-colimit-prime-chain-dimension: the existing node computes dimension through filtered-colimit chains; the repaired node asserts reduced excellent henselization, finite normal factors, normal completion, and nowhere-density preservation.

lem-per-henselian-normal-completion-preparation vs lem-sc-smooth-strict-local-field-model: the existing node treats smooth strict-local rings over a field; the repaired node treats ordinary henselization and finite normalization of arbitrary reduced quasi-excellent local rings.

lem-per-henselian-normal-completion-preparation vs lem-trf-smooth-geometric-stalk-algebra: the existing node is a smooth geometric-stalk algebra criterion; the repaired node is a local algebra preparation theorem with normal completions and finite normalization factors.

lem-per-henselian-normal-completion-preparation vs lem-per-excellent-normal-surface-local-data: the existing node is restricted to normal excellent surfaces and their singular loci; the repaired node is arbitrary-dimensional reduced local preparation and completion.

lem-per-henselian-normal-completion-preparation vs lem-per-normal-punctured-hypersurface-connected: the existing node proves connectedness of a punctured hypersurface in dimension at least three; the repaired node proves henselian normalization, completion normality and nowhere-density preservation, with no connectedness conclusion.
