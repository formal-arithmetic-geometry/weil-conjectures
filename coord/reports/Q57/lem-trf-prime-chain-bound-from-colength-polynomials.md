## Files written

- dag/nodes/sec-trace-formula/lem-trf-prime-chain-bound-from-colength-polynomials.json: statement item, now split into eight explicit steps; no Mathlib match for the whole conditional theorem.
- citations.json: one verbatim statement quote for each step/node citation.
- searches.jsonl: actual msearch.py queries and service outcomes. The existing item's earlier searches were retained. write_split.py is sandbox-only preparation code, not part of the delivery.

New nodes: 0. New Mathlib leaves: 0. All auxiliary arguments are elementary steps using already existing nodes. No unit record is changed: the item is an extracted algebra input, not the unit's key proposition.

## Attachments

None. Searches of lean/WeilConjectures for the item's blueprint tag, Hilbert--Samuel, and colength found no declaration stating this theorem. The local-ring unit criterion used in Step 1 is the existing Mathlib leaf, not an attachment for the item.

## Wanted literature

None. WANTED: none.

## Audit of the original item and blueprint

The statement is unchanged and true under its stated hypotheses. The original unsplit item had no proof and did not name the polynomial-definition node among its statement dependencies; that dependency is now explicit. The imported source is Stacks algebra.tex, Tag 00KQ, proposition-dimension, especially the last prime-chain paragraph. This conditional extraction assumes the shifted difference inequality instead of reproving it, and must not call its parent Hilbert--Samuel dimension theorem (which would be circular). I read the parent's proof to check precisely that it needs all three conclusions, not merely the dimension bound. I preserve the recorded historical blueprint ancestry under lem-trf-local-term-locality; its main-20261015 update concerns contracting local terms and supplies no alternative proof of the algebra assertion. The split changes neither that unit nor its route.

The proof uses elementary coefficient estimates instead of introducing a separate asymptotic comparison theorem. Searches for that possible input also ran with msearch.py: LeanFinder found Polynomial.div_tendsto_atTop_of_degree_gt and related analytic limits, while LeanSearch found degree/limit theorems. Reading Analysis/Polynomial/Basic.lean showed that these are real-variable limits, not the requested integer eventual-comparison statement in one specialization. Since the needed argument is just bounding the sum of lower coefficients and subtracting polynomials, I wrote it in Step 3 and created no node. The whole-item searches found dimension formulas for polynomial rings, generator bounds for local rings, and chain bounds by Krull dimension; none identifies the conditional colength polynomial theorem. I read KrullDimension/Polynomial.lean:32 onward to distinguish polynomial-ring dimension from the degree of a polynomial representing lengths. There is no unsupported Mathlib leaf claim.

## Not duplicates

No new nodes are proposed. Searches of the whole DAG by colength, polynomial-degree, eventual positivity, quotient length, and the Stacks places, and blueprint_refs.py searches for polynomial, colength, prime chain, polynomial growth and eventually positive found no node to replace this conditional theorem. Existing definitions of module length, polynomial degree, and Krull dimension and the local-ring unit criterion are reused.

## Review by Q57

I read Stacks algebra.tex at proposition-dimension (Tag 00KQ), definition-length (02LY), lemma-length-independent (00IX), and lemma-spec-closed (00E5), and checked the tag mapping in tags/tags. I also opened every existing node actually cited: lem-weil-pbc-local-ring-unit-criterion, def-weil-pbc-module-length, def-weil-polynomial-ring, and def-weil-pbc-krull-dimension-ring. Their statements give exactly the units criterion, chain supremum, degree/leading coefficient, and prime-chain supremum used below. No step uses a cited node's proof or a hidden stronger assertion.

Step 1 uses the unit criterion to show a proper ideal is contained in the maximal ideal, hence that J is proper. Its only other input is the definition of length, applied to the explicit nonzero-module chain. This checks that H_J is defined and at least 1, which is essential in the degree-zero case. The criterion is an existing Mathlib leaf, so it is an allowed generic tool across units without a route replacement.

Step 2 uses the length definition itself: the scalar rings have exactly the same submodules by lifting scalars, and inverse images under a surjection lift strict chains. This explicitly proves both the quotient-length identification and the inequality, rather than claiming either from a definition node without an argument. The source 00IX has precisely the same scalar-lifting proof. There is no extra flatness, exactness, or residue-field hypothesis.

Step 3 uses the polynomial definition only. For n at least 1 each lower power is bounded by n^(d-1), so the triangle inequality bounds all lower terms by B n^(d-1). Taking n large compared with 2B/a gives positivity; degree zero is a separate constant calculation. Applying that calculation to P-Q proves the comparison. This is a few-line elementary polynomial argument, not an appeal to an uncited analytic limit theorem.

Step 4 applies Steps 2 and 3 after taking the maximum of just two thresholds. Step 5 takes n large enough that n-c also exceeds its threshold, excludes d=0 using H_J at least 1, and computes the coefficient dc times the leading coefficient by binomial expansion. I checked d=1 separately: lower constant terms cancel, so no negative-degree assertion is needed. Step 6 then applies the already proved comparison to two nonzero polynomials with strictly positive leading coefficients. There is no use of Noetherian dimension theory here; Noetherianity is an allowed but unnecessary hypothesis for this conditional implication.

Step 7 chooses x from an actual set difference between two strict primes. The first step places it in the maximal ideal. J lies in the second prime, so both quotient-degree monotonicity and the principal degree-drop hypothesis apply. The lift of a quotient prime chain is proved directly using the definition of prime and surjectivity, including properness and strictness. Thus it does not cite a spectrum definition for a missing correspondence theorem. Step 8 explicitly iterates integer inequalities with its base case and successor inequality, then uses the cited Krull-dimension definition only to take the supremum. The argument bounds arbitrary chains, without assuming they are maximal, saturated, or end at the maximal ideal.

Small cases checked: a field has only the zero proper ideal, H=1 and degree zero, no x in the required set difference and no positive-length chain; a nonzero Artinian local ring has eventual constant colength and again no positive-length prime chain; a degree-zero P with x as hypothesized gives D=0 against H_J at least 1; for P=aT+b, D=ac is positive constant, so the drop is exactly one; for chain length zero the sum bound is immediate; I=I' permits equality of degrees. Nonzero quotient rings are ensured by properness, c is positive, all polynomial comparisons are over Q and all degrees of Q_I are natural integers. I corrected the preliminary reference to the quotient-spectrum tag to 00E5 after checking the local tag map. No statement dispute or source error was found. Every proof step is below 2000 characters and none hides a non-elementary lemma. There are no new statement-only nodes to check.

## Unfinished work

None in this stage-1 split. No Lean was written and no compiler, Lake command, or local DAG/preflight checker was run.
