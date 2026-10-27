# Stage-1 report: lem-trf-analytic-ramification-tower

## Files written

- dag/nodes/sec-trace-formula/lem-trf-analytic-ramification-tower.json — statement, split; no Mathlib match. Four steps, 2287 characters in total, using three existing nodes.
- citations.json — a verbatim statement excerpt for each of the four step/node pairs.
- report.md — this report.

No new nodes and no Mathlib leaves. The sandbox initially contained dispatcher briefs only, with no node, report, or earlier search log to resume. The current repository item was copied without dropping its inherited metadata or earlier searches. Fresh searches and their actual log records were appended.

## Attachments

None. Searches in lean/WeilConjectures for the exact blueprint id and for immediate extensions, divisible value groups, wild inertia, and defectlessness found no declaration giving the item. The broad ramification/henselian search found ordinary scheme and local-ring results, not this complete valued-field assertion.

## Sources wanted

WANTED: literature/temkin-stable-modification-arXiv-0707.3953v3.pdf, §2.1 pp. 7–9 and proof of Theorem 6.3.1 pp. 49–50, for lem-trf-analytic-ramification-tower. The named local PDF does not exist. I read the primary author's PDF through the web reader at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf (arXiv:0707.3953v3). No document was downloaded into the repository. The assembly is marked proof_origin.by = agent, since the local source required by the brief is missing.

## Corrections and observations

The imported statement is mathematically sound. I normalized its doubled TeX backslashes; no hypothesis, conclusion, or mathematical definition changed. The equalities of residue fields are understood through the canonical embedding, as explained in step 1. This does not assert literal equality of two quotient types.

The proof was empty. I supplied the finite-index/divisibility argument, the finite-dimensional/algebraically-closed residue argument, the defect calculation, and the collapse of the auxiliary tame extension. In particular, p-power degree alone would not justify a tower: step 4 invokes the existing tame-base-change theorem and step 3 proves that its auxiliary extension is trivial.

The latest blueprint ancestor lem-trf-local-term-locality now presents the contracting-correspondence argument directly and no longer spells out the historical semistable-alteration branch named in this item's inherited blueprint.from.place. I read its current statement and proof as well as the chapter and unit records. The existing item and its three inputs remain in the same unit sk-i-curve-zero; this delivery neither edits a unit nor substitutes a different proof route. The split_report identifies the inherited Temkin subargument it resolves rather than pretending that the present blueprint explicitly contains it.

## Unfinished work

None for this one-level split. The three existing cited statements remain independent DAG work; I did not split or edit them. No Lean source was written and no compiler, Lake, or build command was run.

## Not duplicates

No new ids were created. I searched the full DAG and blueprint for ramification, tame extensions, divisible values, immediate extensions, and defect, and reused lem-trf-valued-extension-degree-bound, lem-trf-valued-finite-ramification-calculus, and lem-trf-valued-tame-prime-tower. The finite-index and finite-dimensional algebra arguments are steps, not new nodes. This avoids making new nodes out of the item's own clauses.

## Review by NO

I read delivery-errors B–E in full and checked the actual four steps against the statements of all three cited nodes. For the item I read Temkin §2.1, including the fundamental inequality and Lemma 2.1.5, and the proof of Theorem 6.3.1 on printed pages 49–50. The latter explains the ramification reduction; the immediate-field specialization is assembled explicitly in our proof. There are no new nodes requiring separate source review. I also opened def-weil-field and def-trf-valuation-ring to check the unchanged statement dependencies.

Step 1 uses only the conclusion of lem-trf-valued-extension-degree-bound: embeddings, finite residue dimension, and finitely many value-group cosets. Its hypotheses require compatible real nonarchimedean absolute values and finite field dimension, all present here; it requires neither discreteness nor a finiteness assertion about valuation rings. I checked the residue calculation by the dependence of 1,a,...,a^f and splitting the resulting polynomial; a nonzero constant cannot vanish. The value calculation uses repetition among e+1 powers and the unique positive real root, so it does not assume a divisible quotient has finite order. The same argument is deliberately proved for every finite M/K so its later application to the auxiliary extension is justified without citing the item itself.

Step 2 uses the explicit defect definition and the characteristic-dependent defect conclusion of lem-trf-valued-finite-ramification-calculus. The ground field is complete and its absolute value nontrivial, so this is the complete-field, unique-prolongation setting of the cited statement. With e=f=1 the degree equals the defect. In residue characteristic zero the resulting degree-one extension equals the base. In positive residue characteristic the degree is p^a. I do not assume the ground field itself has characteristic p, or that L/K is separable or defectless.

Step 3 uses the definition of tame in that same calculus node, specifically d=1, with the already proved e=f=1. It is elementary substitution into the degree formula, not a new ramification theorem: every finite tame extension over K has degree one. It does not claim an arbitrary immediate extension is trivial.

Step 4 uses exactly clause (1) of lem-trf-valued-tame-prime-tower. That clause accepts a finite p-power extension of a complete field and supplies a finite tame base change plus a prime-degree tower, including the inseparable case. I checked the positive residue characteristic, completeness, nontrivial norm, and degree hypotheses against steps 1–2. The finite tame field it returns equals K by step 3, so the endpoint compositum is literally L in the common algebraic closure. Removing identity steps gives the requested degrees. This is more than applying a new copy of the desired conclusion: the cited existing theorem works for arbitrary p-power extensions and permits a generally nontrivial tame base change; our argument proves why that extra base change disappears here.

Small cases checked: L=K gives e=f=d=1 and a tower of length zero; positive residue characteristic permits defect p^a and purely inseparable steps; mixed characteristic uses the residue prime; characteristic-zero residue forces degree one. Divisibility without the positive-real ambient group would not suffice for the root-uniqueness step, and the item supplies that ambient group. None of the steps exceeds 2000 characters, and their combined length is below 3000. Each non-elementary input is a cited node statement; the elementary residue and value arguments are written out. citations.json was built from the actual cited statement strings, retaining their exact spelling. No Stacks tag or forbidden SGA route is used.

I read the fresh Mathlib hits and the representative ideal-ramification source declarations. The latter describe multiplicativity of ramification indices for ideals (including Dedekind and flat-localized hypotheses), not the defect or tower assertion for potentially nondiscrete analytic fields. Other hits describe residue algebra maps, finite residue fields of local fields, and henselian ring definitions. The second semantic phrasing again found ideal-ramification facts; neither it nor Loogle or LeanSearch supplies an attachment or a one-line Mathlib specialization of this item. searches.jsonl contains the exact queries and actual results; inherited searches are retained, not invented or silently replaced.
