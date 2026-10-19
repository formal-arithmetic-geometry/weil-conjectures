# Worker report: lem-per-noetherian-local-domain-open-infinite

Group Q15; direct stage-1 delivery, 2026-10-19.

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-noetherian-local-domain-open-infinite.json`: existing statement, unchanged; split into seven steps following Stacks 02IG. No exact Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-partial-parameters-quotient-dimension.json`: one new statement-only node, Stacks 02IE. `unsplit`, not a Mathlib leaf. A partial system of parameters need not be a regular sequence.
- `report.md`, `citations.json`, and the actual `msearch.py` search log `searches.jsonl` are sandbox supporting files. No Lean or unit/chapter file was written.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item id, infinite-open terminology and Noetherian local domains. The project hits concern DVRs, regular local rings and unrelated topology. None states 02IG. Also searched the project for systems of parameters and 02IE before introducing the helper; no matching declaration appeared. No sorry declaration was treated as finished evidence.

## WANTED

None. All mathematical sources used are present in `literature/stacks-project/algebra.tex`, and tag/label pairs were checked in `literature/stacks-project/tags/tags`.

## Corrections and scope

The item had an empty proof and no proof dependencies. Its statement is correct and was retained byte for byte. The source is Tag 02IG, `lemma-Noetherian-local-domain-dim-2-infinite-opens`, lines 14738–14765. I filled the argument rather than relocating the infinitude assertion into a child. The new node is the independent general quotient-dimension theorem 02IE, `lemma-elements-generate-ideal-definition`, lines 14712–14723; it does not mention domains or opens and is not a clause of the item.

The source's last sentence suppresses two short arguments. The split now explains why the first lifted parameter is nonzero and why the two unequal quotient dimensions force a prime containing that parameter but avoiding x. It explicitly uses the inverse maps between quotient primes and primes containing the ideal, so it does not assume a closed subset is proper merely because one ideal is properly contained in another. It also explains the local Noetherian quotient hypotheses and the lifting of the ideal of definition using the power bound actually present in the cited node.

Read the chapter `sec-deligne-laumon-a1` and unit `sk-p-dl-a1-perverse`, their fixed route requirements in SETUP, and the main-20261015 unit and ancestor proof. The existing item's `blueprint.from` locates this commutative algebra tool within the normal-local dualizing input to the ancestor's Step 1. No chapter or unit route is changed. The item is not a key realization node, so no unit record needs editing. The helper has the same ancestor `lem-per-artin-gabber-affine-curve`, with this item added at the front of the inherited via chain and the exact 02IG use of 02IE specified in its place.

## Searches and reuse

Before creating the helper I searched the whole DAG by tags 02IG, 02IE, 00KW and 00KQ, their labels, systems of parameters, partial parameters, and dimension-drop terminology. Opened the existing spectrum, dimension and parameter nodes used by the proof. `tools/blueprint_refs.py search` was run for `Noetherian local domain`, `parameters`, `02IE`, `quotient dimension`, and `02IG`; none states the item or the helper. `ancestor` confirms the inherited ancestor. The only broad parameters blueprint hits concern unrelated gluing, Fourier or categorical assertions; a principal-ideal DVR node is not the requested dimension theorem.

All Mathlib searches went through the prescribed msearch.py, with successful service responses recorded as actually returned. For the item I used two semantic phrasings (infinitude of opens and non-openness of the generic point), Loogle, LeanSearch and a RingTheory grep. The insertion-of-primes lemmas and local dimension finiteness are ingredients, not the conclusion. Jacobson singleton results have an additional hypothesis.

For the helper I used two semantic phrasings (initial parameters and arbitrary selected generators of an m-primary ideal), Loogle `ringKrullDim, Ideal.radical`, LeanSearch, and greps in RingTheory/KrullDimension and RingTheory. Read `Mathlib/RingTheory/KrullDimension/Regular.lean:137–227`. The nearest equality is `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`, line 210 (the exact name/line was checked by a further logged grep). It assumes regularity, absent here. The inequalities do not specialize to equality in one line; the nonzerodivisor result supplies only the separate existing dimension-drop node. No match was promoted on the basis of a name alone. The existing item's earlier Q29 searches remain intact, and Q15's additional searches are appended.

## Not duplicates

lem-per-partial-parameters-quotient-dimension vs lem-weil-pbc-noetherian-local-system-of-parameters: both cite 07DU only to define an ideal of definition. The existing 00KQ node gives existence of a parameter ideal and a power containment. The new 02IE node gives the dimensions of quotients by initial parts of any prescribed parameter sequence, and cannot be obtained by specializing that existence statement.

No existing DAG node had source tag 02IE when checked. The helper is not the existing `lem-weil-pbc-noetherian-local-system-of-parameters`: that node proves existence, finiteness and a maximal-ideal power bound, not dimension after taking an initial subset of arbitrary prescribed parameters. Nor is it `lem-weil-pbc-dimension-quotient-nonzerodivisor`: parameters in an arbitrary local Noetherian ring may be zero divisors. The helper is strictly smaller than the item and serves the two numerical equalities in Step 6.

## Review by Q15

I read delivery-errors B–E in full with the source and node statements open. For the item I read all of 02IG, the exact same local-domain, Noetherian and dimension-at-least-two hypotheses as the item. For the only new node I read all of 02IE and the definition of an ideal of definition in 07DU (`definition-ideal-definition`). Its statement introduces A, its unique maximal ideal, d, every parameter, the radical and the range 1 <= i <= d; it has no proof or proof dependencies. It does not assume regularity, reducedness, excellence or equicharacteristic. The statement-only boundary is intentional.

Step 1 uses `lem-weil-pbc-spec-irreducible-closed-subsets-primes` clause (1), which explicitly gives the closure V(p) for EVERY prime p, not merely a generic-point definition. R nonzero and a domain make (0) a prime. Its closure is X; subtracting the finitely many other closures really leaves exactly (0) and is open. This step explains both the generic point and its openness under the finite assumption.

Step 2 uses the statement of `def-weil-pbc-krull-dimension-ring`, which explicitly includes equality with the topological dimension, and the finite-dimension clause of `lem-weil-pbc-noetherian-local-system-of-parameters`. The latter is applied to the given Noetherian local R. Hence d is a finite integer at least two; no finiteness of dimension is taken for granted and infinite subtraction never occurs.

Step 3 uses only the basis clause (i) of `lem-weil-pbc-spec-localization-away-basic-open`; it does not use the localization construction inside that node's proof. The point (0) lies in the open singleton from Step 1. Thus x is nonzero, and it is a nonunit because otherwise its D(x) would be the entire, non-singleton spectrum. Membership of a nonunit in the unique maximal ideal is the elementary local-ring property used here. This checks the maximal-ideal hypothesis required in Step 4 without assuming x lies there arbitrarily.

Step 4 uses the full statement of `lem-weil-pbc-dimension-quotient-nonzerodivisor`, read along with 00KW (`lemma-one-equation`). R is Noetherian local, x is in its maximal ideal by Step 3, and the domain cancellation law with x nonzero proves that x is a nonzerodivisor. The explicit quotient-ideal correspondence gives the local Noetherian hypotheses and nonzeroness of R/xR needed by Step 5. No completeness hypothesis is used.

Step 5 applies `lem-weil-pbc-noetherian-local-system-of-parameters` to this quotient of dimension d-1. I read the node's entire statement, including the power containment; the quoted citation includes it. Read its source 00KQ (`proposition-dimension`) and 07DU. The lifts are in n since the chosen quotient elements are in n/xR. The inverse image of the generated ideal is precisely (x,y_2,...,y_d). The power bound then proves the radical equality explicitly, without adding a nilradical/intersection theorem not in the cited statement.

Step 6 uses exactly the new 02IE statement twice, after permuting the same d generators to start with y_2,x. Reordering changes no generated ideal. Its hypotheses are Step 2's d=dim R, Step 5's radical equality, membership of every generator in n, and d>=2 for the two indices. The quotient is not assumed Cohen–Macaulay or regular. This is where the non-elementary content absent from the old DAG is cited, rather than hidden as an elementary step.

Step 7 uses only the chain-supremum definition in `def-weil-pbc-krull-dimension-ring` and the preceding equalities. The correspondence of quotient primes with primes containing the kernel is written with the inverse maps and the domain criterion for primality. If all primes containing y_2 contained x, the two sets of chains would coincide. Their unequal finite dimensions therefore produce the required prime. y_2 is nonzero because otherwise its quotient dimension would still be d. The resulting prime in D(x) cannot be zero. These are elementary steps from definitions and the already cited equalities, not an additional existence theorem. I checked that no citation uses another node's proof rather than its statement. `citations.json` contains an actual verbatim statement excerpt for every step/node pair (eight pairs).

For small cases, the d=0 helper statement is vacuous, d=1 gives a zero-dimensional parameter quotient (e.g. k[[t]]/(t)), and d=2 gives dimensions 1 then 0 for the parameters s,t of k[[s,t]]. The helper also permits nonregular parameters: in k[[u,v,w]]/(u^2,uv), the dimension is two, v is a zero divisor, and the parameters v,w still give quotient dimensions one and zero. Thus regular-sequence hits cannot be substituted. The item's dimension threshold is necessary: for a DVR the generic singleton is a finite nonempty open, and for a field its whole spectrum is a singleton. In dimension two, e.g. k[[s,t]], the proof's dimension difference is 1 versus 0, so the final strictness remains valid at the boundary. The empty O is excluded at the first step; the zero ring is excluded by the statement. Non-domain rings are not silently included.

B1–B10: the helper is statement-only, self-contained, has actual sources by tag and label, has exactly the notion dependencies it uses, uses single TeX escapes, records real searches, and has precise ancestry. C1–C8: the two spectrum lemmas and two dimension/parameter lemmas are existing Mathlib tools with the quoted statements; the one new lemma supplies all remaining non-elementary numerical content. The local quotient and final prime correspondences are written out. D1–D5: neither the item nor its sole conclusion is repeated in a child, and no assertion is derived by invoking its own proof; the argument follows 02IG's actual steps. E1–E7: hypotheses checked above; no source error or disputed statement was found. All seven step texts are below 2000 characters, and none hides a long lemma. I corrected an initially mistyped Mathlib candidate line number in the search verdict to the logged line 210 before the dry run. No source statement was changed.

## Unfinished work

The helper 02IE is deliberately unsplit under the one-level contract. No part of the item's natural-language proof is left open. The first dry run requested the explicit same-tag pair line for 07DU; I added the line above after reopening the existing statement. The next server dry run and direct push are run after this repair; their final result is reported by the delivery command.
