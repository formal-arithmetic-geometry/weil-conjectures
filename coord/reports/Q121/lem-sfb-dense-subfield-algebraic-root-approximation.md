# Q121 stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dense-subfield-algebraic-root-approximation.json`: statement split in five steps; no match for the whole statement in Mathlib. Statement and its statement dependencies are unchanged.
- `citations.json`: six verbatim citation records, one for each cited node at each proof step.
- `report.md`: this report. `searches.jsonl` was produced by the required search command.

New nodes: 0. New Mathlib leaves: 0. Reused Mathlib leaves: `lem-sfb-monic-dense-approximation`, `lem-sfb-roots-coefficient-proximity`, and `lem-weil-alg-closed-linear-factorization`, together with the existing polynomial and algebraicity definitions.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for dense-subfield/root-approximation language. `PadicAlgCl.exists_isAlgebraic_mem_adjoin_simple` in `NumberTheory/Padics/Extension.lean:82` is a specialized p-adic overfield conclusion, not this general statement with all its coefficient and degree clauses. Its proof at lines 110–126 supplies the route being expanded here.

## WANTED

None. The quantitative proof is available in the checked Mathlib source and project source. No additional literature is needed for this split.

## Issues found

No statement dispute and no change of hypotheses or conclusion. The imported item had no proof. Stanford L19, Proposition 1.1.9, first bullet on p. 3 explains the countability input, but does not contain the quantitative lemma. I therefore mark the expansion as agent-written, explicitly identifying Extension.lean:110–126 and the Mathlib approximation lemmas. I did not present L19 as proving its explicit tolerance formula.

The blueprint route is unchanged: this is the arithmetic coefficient-topology input under paragraph (3) of the current direct-images proof. `blueprint_refs.py ancestor` returns null; I retained the inherited null ancestor and via chain and the already specific `from.place`. The whole-blueprint searches `root approximation`, `monic`, `dense subfield`, and `linear factorization` found no equivalent blueprint statement; the `monic` hits concern different assertions. No unit realization is due: this item is not the unit's key theorem.

## Not duplicates

No new nodes. Whole-DAG searches by theorem names and the phrases monic approximation, nearby roots, coefficient approximation and algebraically closed factorization found the three existing leaves used here. In particular I did not create new copies of the two approximation inputs or a new splitting lemma. The separably closed factorization node in the trace-formula chapter requires separability and is not needed; the algebraically closed factorization leaf applies directly without that extra hypothesis.

## Review by Q121

I read the worker brief, stage-1 contract, the three levels in SETUP, GOAL, the item's chapter and unit records, the current direct-images blueprint proof and delivery-errors B–E in full. I read Stanford L19 p. 3 and project Extension.lean:82–127 for the item, and Mathlib Analysis/Normed/Field/Approximation.lean:114–124 and 132–138 for the exact quantitative inputs. There are no new nodes whose sources require separate review. For the existing factorization leaf I also read Mathlib Algebra/Polynomial/Splits.lean:299–309 and FieldTheory/IsAlgClosed/Basic.lean:62–63. For the final definition I checked Stacks Tag 09GC, fields-definition-algebraic, in fields.tex:608–616.

For step 1 I checked positivity separately: M is at least 1, so r/M is strictly positive, and n+1 and n are nonzero. The displayed nth-root identity is the positive-real identity, so no zero-base or fractional-power ambiguity is hidden. This is elementary arithmetic; it is not a separate lemma.

For step 2 I opened `lem-sfb-monic-dense-approximation` and checked its complete statement. It permits an unnormed field D, requires precisely density of D in the normed field K, and gives monicity, exact degree and strict bounds for every coefficient, including those above the degree. These are exactly the facts taken from it. The Mathlib declaration has only Field D, NormedField K, Algebra D K and DenseRange, so no completeness, nontrivial norm or characteristic assumption was introduced.

For step 3 I opened `def-weil-polynomial-ring` and `lem-weil-alg-closed-linear-factorization`. The definition supplies the coefficient description of degree and leading coefficient. Applying the leaf to q over L is legitimate because q is nonzero: its coefficient at n is 1. Its leading coefficient is also 1. The leaf's statement really gives the nonzero leading constant and finite linear factorization; it does not assert the number of factors equals n. I supplied that remaining elementary coefficient argument explicitly: a product of m monic linear factors has top coefficient 1 at m and no coefficients above m. Thus m=n. I did not use the proof of the leaf or infer splitting merely from the definition of algebraic closedness.

For step 4 I opened `lem-sfb-roots-coefficient-proximity`. Its statement supplies both h(b)=0 and exactly the bound used. I checked its norm restriction hypothesis against the item and its monicity, equal positive degree, all coefficient inequalities and splitting hypotheses against steps 2–3. Only K and L need norms here; no norm on D is silently used. The input f(x)=0 is the item's given root condition. Step 1 turns its bound into precisely r, retaining the strict inequality.

For step 5 I opened `def-weil-polynomial-root` and `def-weil-algebraic-element`. The former states evaluation as the finite coefficient sum along the given homomorphism. Writing both inclusions in the displayed sum proves agreement of h(b) and g(b) with the composite D-to-L inclusion, rather than assuming a scalar-tower compatibility. The latter defines algebraicity by a nonzero annihilating polynomial. The witness is the already constructed g, whose leading coefficient is 1, so the last inference is just the definition. I generated citations.json from these actual statements; every quote is verbatim.

I checked delivery-errors B point by point: there are no unsplit new nodes or missing new notions; the unchanged statement is self-contained and the norms and density are inline; the existing source declarations and line numbers above were read; TeX has single mathematical backslashes after JSON decoding. Every appended search record is copied from this run's actual searches.jsonl, while the imported earlier records are retained. Both semantic phrasings were read. Loogle finds coefficient approximation alone; the other hits about root existence, coefficient bounds and number fields do not imply the full item. IsAlgClosed.of_denseRange has extra completeness/characteristic/nonarchimedean hypotheses and a different conclusion, so it was not misclassified as a match.

For C I checked all six citations against their statements as described above; every non-elementary inference is one of the three cited Mathlib leaves. No citation depends back on the item: all proof dependencies are Mathlib leaves or definition leaves. The factorization tool is in another unit but is already Mathlib, so the route exemption applies without replacing a unit step. For D the five steps carry the actual tolerance, coefficient transfer, splitting application, root selection and evaluation argument, instead of restating the item through a new node. For E I tested the small cases: n=1 gives the exact radius identity with epsilon=r/(2M); x=0 makes M=1 and still gives positive tolerance; D=K allows g=f and b=x; a trivial norm forces sufficiently close coefficients to coincide and causes no problem; positive characteristic and repeated roots require no separability. Degree zero and r=0 are excluded by the statement and are not used. No completeness or characteristic-zero assertion is needed.

Every step is under 600 characters, and the whole proof is 1944 characters. No long step hides an auxiliary lemma. No repository or launcher file was edited, no git command was run in the read clone, and no Lean compiler, Lake or build tool was used.

## Unfinished work

None in the one-level split. The server dry run and delivery are the remaining mechanical checks at the time this report is written.
