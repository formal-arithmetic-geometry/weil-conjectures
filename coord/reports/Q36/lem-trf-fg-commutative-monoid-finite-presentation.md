# Stage-1 report: lem-trf-fg-commutative-monoid-finite-presentation

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fg-commutative-monoid-finite-presentation.json` — split statement; proof supplied; no Mathlib match for the full theorem.
- `dag/nodes/sec-trace-formula/lem-trf-congruence-polynomial-kernel.json` — statement-only supporting node; no exact Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-mvpolynomial-noetherian.json` — Mathlib leaf, `MvPolynomial.isNoetherianRing_fin`, `Mathlib/RingTheory/Polynomial/Basic.lean:925-927`.
- `citations.json` — verbatim citations for every non-elementary dependency used by an item step.

## Attachments

None. I found no sorry-free declaration in the slopmaster2 source stating this item or either new node.

## WANTED

WANTED: none. The Noetherian polynomial input is available in pinned Mathlib; the binomial-kernel statement is recorded as a statement-only node because no exact Mathlib theorem was found.

## Corrections and checks

The imported item described an ordinary commutative monoid but cited `sk-def-sfb-ring-object`, whose statement concerns ring objects of sheaves and does not define the required set-level monoid. I removed that parenthetical and its statement dependency. The mathematical conclusion is unchanged. The source string for Tag 00FN only supplies the Noetherian polynomial input; it does not state the monoid consequence, so the proof origin records the remaining binomial-kernel argument as agent-written. I tested the edge cases $n=0$ (the free monoid is trivial and the selected relation list may be empty), a free monoid (empty kernel relation), repeated generators, the idempotent relation $2p=p$, and a finite cyclic monoid; the construction allows $m=0$ and imposes no cancellation, integrality, or saturation assumption.

## Review by Q36

I read the current item node, its parent `lem-trf-fine-log-stalk-chart-spreading`, the unit record `sk-i-curve-zero`, the chapter record, and the blueprint proof for `lem-trf-local-term-locality`. The parent uses exactly the finite-presentation property in its second step, so the revised statement supplies that input without changing the parent's hypotheses. I read the statement of `lem-trf-congruence-polynomial-kernel`; it gives precisely the kernel-as-binomial-ideal fact used in steps 1–3, including its finite-generator specialization. I read the Mathlib source at `Mathlib/RingTheory/Polynomial/Basic.lean:925-927`; `MvPolynomial.isNoetherianRing_fin` gives Noetherianity for every finite variable count over a Noetherian coefficient ring, and instantiating the coefficient ring with $\mathbf Z$ supplies step 2. The proof's step 1 constructs $M=\mathbf N^n$, the kernel congruence, and the monoid-algebra map. Step 2 checks the only finiteness hypothesis: Noetherianity yields finitely many ideal generators, and each generator has a finite ideal-span witness, so only finitely many binomials are retained. Step 3 compares the selected-pair congruence with the kernel by passing to the quotient monoid algebra; the cited kernel statement is used in both directions, and distinct quotient classes remain distinct basis vectors. Step 4 verifies the equivalent universal property from surjectivity of $\pi$ and constancy on fibres; this is elementary once the congruence equality is established. I checked that every hypothesis is present where used, that no cancellation or saturation is smuggled in, and that every cited quote in `citations.json` is verbatim. Searches over the whole DAG and blueprint found no duplicate kernel or finite-presentation node; the Mathlib searches were run with `msearch.py` and their actual outputs are recorded in both new node files.

## Not duplicates

`lem-trf-congruence-polynomial-kernel` vs existing congruence and monoid-algebra nodes: those existing nodes define general monoid objects or quotient congruences, while this node states the kernel ideal formula for the induced monoid-algebra map and its finite relation specialization.
`lem-trf-mvpolynomial-noetherian` vs `lem-sf-noetherian-polynomial-dimension`: the existing node states a Krull-dimension formula, whereas this leaf states Noetherianity and cites a different Mathlib declaration.
