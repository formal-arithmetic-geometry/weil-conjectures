# Stage-1 report: lem-sfb-quasifinite-normal-local-birational-algebra

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-quasifinite-normal-local-birational-algebra.json: statement, split in five steps; no exact Mathlib match.
- citations.json: seven step/node citations, each quoting the cited statement verbatim.
- searches.jsonl: actual msearch results, preserved.
- report.md: this report.

No new nodes; no new Mathlib leaves. The item statement, statement dependencies, source, creation record, and inherited blueprint provenance are unchanged.

## Attachments

None for this item. Project-source searches for the blueprint tag returned no declaration. Searches for birationality, equal fraction fields, quasi-finiteness and normality found only related results. In particular Algebra.exists_finite_subalgebra_away_of_isQuasiFiniteAtPrime in lean/WeilConjectures/RingTheory/QuasiFiniteAtFiniteSubalgebraAway.lean:50 proves the existing node lem-weil-pbc-quasi-finite-at-finite-subalgebra-away, not this item. Its complete source proof was read and it contains no sorry. FiniteNormalCoverFamily.lean:20 instead concerns an integral intermediate algebra on a normal principal open; it does not state the item.

## WANTED

None. All proof sources used here are available in literature/stacks-project/.

## Corrections and observations

The mathematical statement is correct and has been retained. The live item was unsplit and the sandbox held no earlier node or report. There is no released repair note for this item.

The local algebra paragraph in Stacks 0BFP(4) passes through a finite algebra whose localization is the source local ring. I used the existing pointwise finite-subalgebra form of algebraic Zariski main (00Q9, with the finite-generator extraction in 00QA/00QB) and expanded the needed fraction calculations. This avoids creating either a duplicate finite-model lemma or a new node merely repeating the item. In particular the proof does not assume that localization of a finite module is finite over the original base.

blueprint_refs.py ancestor returns None for this inherited item. Its existing blueprint.from.node is null, with a detailed from.place and via chain; I preserved these fields. The current latest blueprint's direct-image proof (3) now presents the compactification assembly; the inherited local algebra input remains a generic tool in the existing alteration prerequisites. Neither the unit statement nor its route is changed, and this item is not the unit's key node. Whole-blueprint searches for quasi-finite, birational and 00Q9 found no blueprint node stating this local normal-birational algebra conclusion. No same_as entry was warranted.

The only non-leaf off-unit tool used is lem-weil-pbc-quasi-finite-at-finite-subalgebra-away. It is a generic ring-theoretic finite-neighbourhood result, not a six-functor conclusion or an alternative alteration route. Its use is declared in split_report.tool_uses.

## Unfinished work

None for this one-level split. Existing dependencies keep their own states. No Lean was written, compiled or built, and no repository or launcher file was modified.

## Review by Q80

I read Stacks varieties.tex, Tag 0BFP (lemma-modification-normal-iso-over-codimension-1), especially the whole proof of clause (4), against the item's statement. The paragraph assumes a common function field and a normal base local domain and uses algebraic Zariski main, finite implies integral, and locality to finish. I also read algebra.tex at theorem-main-theorem (00Q9), lemma-quasi-finite-open (00QA), lemma-quasi-finite-open-integral-closure (00QB), lemma-essentially-finite-type-fibre-dim-zero (the result 0BFP invokes), lemma-finite-is-integral (00GK), and definition-domain-normal (0309). There are no new-node sources to review.

For Step 1 I opened def-weil-pbc-localization-at-prime: it states the fraction relation and localization at the prime complement. These give the embeddings into K by domain cancellation, and a not in p implies a not in q by contraction. Thus the map is the stated induced map, not an unrelated abstract isomorphism.

For Step 2 I read the complete statement of lem-weil-pbc-quasi-finite-at-finite-subalgebra-away. It gives exactly a finite A-subalgebra B inside C, g outside q, and the canonical isomorphism B_g to C_g. The hypotheses are finite type and quasi-finiteness at the given prime, both present. The lemma does not require A Noetherian or the map quasi-finite everywhere; neither was added.

For Step 3 I read lem-weil-pbc-finite-algebra-is-integral and def-weil-pbc-normal-ring. The first gives monic equations for every b of the finite algebra B, not merely existence of a finite presentation. The same equations over R=A_p show integrality there, and the second puts b in R because b is in K=Frac(R). I wrote why this is the same fraction field. This step does not need a separate theorem about preservation of integrality by base change.

For Step 4 I reread the prime-localization statement and def-weil-ring-localization-away. Since g is already in R, write g=a/s with s outside p. Equality in K is equality in C after multiplying by s. If a were in p, primeness would contradict g outside q. Hence g is a unit of R. The cited away-localization node explicitly describes fractions b/g^n, so B_g embeds in R; the canonical isomorphism from Step 2 then embeds C in R. No general identification lemma is hidden here.

For Step 5 the same prime-localization statement supplies all fractions d/c of C_q. For every c outside q, the expression c=a/s in R and the equality sc=a imply a outside p, again by primeness. Thus 1/c lies in R. This proves the opposite inclusion and explicitly identifies the inverse with the quotient in R. The three elementary steps are each direct fraction calculations; neither Zariski main nor finite implies integral is marked elementary.

I tested the identity C=A, a field base, and p=(0): the last case has R=K and the argument forces C_q=K. A principal open C=A[1/f] at a prime in D(f) also gives the expected equality and confirms that the statement must not assert C itself equals A_p. Dropping normality fails for the cusp normalization k[t^2,t^3] subset k[t] at the cusp (finite, hence quasi-finite, with common fraction field). Dropping quasi-finiteness fails for the blowup chart A=k[x,y] subset C=k[x,t], y=xt, at q=(x,t), p=(x,y): the base is normal but t=y/x is not in A_p and the fibre has positive dimension. These checks also confirm the denominator arguments use the right contraction and no extra Noetherian hypothesis.

All cited node statements were open while the steps were checked; citations.json quotes those statements verbatim, with one entry for every step/node pair. The proof has 2211 characters in total and no step longer than 526 characters. The complete B–E delivery checklist was read: no new statement-only-node, duplicate, missing-definition, Mathlib-leaf, route-lock or SGA issue arises; the only substantial results used are explicitly cited. Logged leanfinder, loogle, leansearch and grep results were read, including the second semantic phrasing. Mathlib's Zariski main and quasi-finiteness permanence declarations require the additional normality and denominator argument and do not attach this item in one line.
