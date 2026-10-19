# Stage-1 delivery: lem-per-j2-finite-algebra-criterion

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-j2-finite-algebra-criterion.json`: existing statement, now split in six steps. Mathlib verdict: no match; no new nodes or Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each of the seven step/node citations.
- `report.md`: worker report and direct-delivery review.
- `searches.jsonl`: actual search-command log; `write_split.py`: sandbox-only preparation script, not a project edit.

## Attachments

None. Searched the slopmaster2 project's `WeilConjectures/` for the exact item tag and the J-2, regular-locus and finite-algebra notions; no declaration states the item. Master is reference material only. The item has no recorded Lean audit/declaration to reconcile; none was inferred from a sorry-free-looking partial declaration.

## WANTED

None. Read the available Stacks source `literature/stacks-project/more-algebra.tex`, Tag 07PC (`lemma-J-2`) in full, including (3) implies (4) and (4) implies (1), and Tag 07P7 (`definition-J`). Verified these labels against `literature/stacks-project/tags/tags`.

## What was wrong and what changed

The imported item was a correct statement with no proof. Its statement, statement dependencies, provenance and inherited search records remain intact. The six new proof steps fill its missing argument. The source's terse assertion (3) implies (4) is expanded by constructing finite models explicitly, rather than asserting a finite-model existence theorem or creating a node restating this item. The genuinely non-elementary remaining implication (4) implies (1) is already the statement of `lem-exc-j2-residue-field-criterion`, so it is cited as an existing generic tool.

Read chapter `sec-deligne-laumon-a1`, unit `sk-p-dl-a1-perverse`, and the current main-20261015 ancestor proof `lem-per-artin-gabber-affine-curve.proof.md`. This item is a commutative-algebra input several levels below that ancestor, via the complete-local-excellence support of the duality construction. It is not the unit's key node; no unit realization or route is changed. Preserved the inherited blueprint ancestry and concrete place. `split_report.tool_uses` declares the off-unit residue-field criterion, which is a tool implementing the item's own cited Stacks route. No SGA source is used.

## Not duplicates

No new nodes. Whole-DAG searches for 07PC, J-2 and J-1 found and reused `lem-exc-j2-residue-field-criterion`; its hypothesis is the existence of finite domain models with nonempty regular opens, whereas this item's hypothesis is openness for all module-finite algebras. These statements are different; steps 1–5 prove the bridge. Blueprint searches for J-2, regular locus, finite algebra, module-finite and residue-field were read; no blueprint node states this item exactly. The finite-algebra spreading node is about coherent algebras on a projective generic fibre and is unrelated here.

## Unfinished work

None in this one-level split. The cited existing residue-field criterion remains responsible for its own proof and dependencies; no new frontier is introduced. No Lean was written, compiled or built, and no repository or launcher file was edited.

## Review by N0

I read the statement of the item against Stacks 07PC (3) implies (1), with J-1 and J-2 expanded by 07P7: the base is Noetherian, finite means module-finite, and the conclusion covers every finite type algebra. There is no added domain or reducedness hypothesis on the base or on the algebras quantified in the conclusion. I opened the actual statements of every cited node, rather than taking any property from its proof.

Step 1 uses precisely the fraction and residue-field construction in `def-weil-pbc-localization-at-prime`. The displayed equality condition proves that the residue field is the fractions of R/p; cancellation uses primality and denominators outside p. It does not identify the fibre with R/p. This is elementary fraction arithmetic.

Step 2 uses exactly the power characterization, characteristic-zero clause and finite-dimensionality in `def-weil-pbc-finite-purely-inseparable-extension`. A finite basis exists by finite-dimensionality. Each denominator lies in the domain A=R/p, and is nonzero; the formula beta_i^(n_i)=c_i d_i^(n_i-1) has no negative exponent because n_i>=1. The argument is an explicit substitution in a pure-power equation, not an appeal to an uncited denominator-clearing lemma.

Step 3 uses the spanning definition in `def-weil-finitely-generated-module`. Reducing each exponent modulo n_i proves finite spanning directly. Coefficients lift through the surjection R to A. Every basis vector equals beta_i/d_i in the fractions of B; hence those fractions contain every element of L, and the reverse containment follows because B is a subring of the field L. No normality, primitive-element theorem, finiteness of normalization, or descent theorem is used. These are elementary polynomial and linear-combination computations, so no separate finite-model node is warranted.

Step 4 applies the exact statement of `lem-weil-pbc-finite-algebra-noetherian`: R is Noetherian by the item, and B is module-finite by step 3 (or B=A with generator 1 in characteristic zero). Its conclusion makes B Noetherian. Openness of U is then the item's own hypothesis applied to B, not a property borrowed from a definition node.

Step 5 uses `def-weil-regular-scheme` only for its actual definition of a regular local ring. The zero prime is available because B is a nonzero subring of L. Its localization is L by step 3; fields have zero-dimensional spectrum and zero maximal ideal generated by zero elements. The field's two ideals also prove Noetherianity directly, so no theorem about localizing Noetherian rings is silently required. Thus the regular open just obtained contains the generic point and is nonempty, even though R itself can be nonreduced.

Step 6 uses the whole hypothesis and conclusion of `lem-exc-j2-residue-field-criterion`: the map R to L is the residue-field map followed by the fixed extension, B is actually embedded in L, it is finite over R, all its fractions exhaust L, and its regular open is nonempty. All these hypotheses have been established in steps 1–5. That cited statement, not just its proof, gives the entire finite-type conclusion. `def-exc-excellent-ring` defines J-2 as exactly that conclusion; no G-ring or catenarity condition is inferred. The residue-field criterion is strictly a different input from this item's finite-algebra criterion, and does not depend on this item.

I tested the construction when R is the zero ring (there are no primes, so the criterion's hypothesis is vacuous); when R is a field; when L=k; in characteristic zero (use B=A); when n_i=1 or alpha_i=0; over a nonreduced base (the construction uses its prime quotient); and for an inseparable example A=F_p[t], L=F_p(t^(1/p)) (take beta=t^(1/p), relation beta^p=t). In general nonmonic denominators are handled by the displayed scaling identity. None requires excellence or perfection in advance.

Against delivery-errors B–E: no new statement-only nodes require metadata or searches, all existing notions have their original definition dependencies, TeX and sources are explicit, there is no attachment supported merely by a tag, and no service failure is called a negative result. All seven citations are exact substrings of their node statements (full statements in citations.json). Every non-elementary input is a cited statement; elementary steps spell out the formulas. The criterion cited is not a restatement of this item, and there is no circular induction or route change. All proof steps are below 2000 characters (340–665), and none hides a standard comparison lemma. No source or statement dispute was found; no statement correction was needed.

I ran the required logged Mathlib searches: two semantic phrasings, Loogle with IsRegularLocalRing and IsOpen, two source regex searches, and LeanSearch. Read every hit: openness of smooth, etale, unramified or free loci, and Noetherianity theorems, do not give the regular-locus criterion. Read `Mathlib/RingTheory/Smooth/Locus.lean` at its openness declaration (line 124) to confirm that distinction. Kept inherited search records as inherited evidence, and appended the exact queries and result records actually logged for this delivery. There are no fabricated searches or new Mathlib matches.
