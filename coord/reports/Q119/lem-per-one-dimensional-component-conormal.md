# Stage-1 delivery: lem-per-one-dimensional-component-conormal

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-one-dimensional-component-conormal.json: statement node, now split into four steps; unchanged statement; no Mathlib match for the whole item.
- citations.json: 13 literal statement quotations, one per step/node citation.
- searches.jsonl: actual msearch.py records for five fresh searches. The item's six inherited search records are retained unchanged.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. The proof reuses existing Mathlib leaves for localization, radical powers, minimal-prime localization and module support, and the existing completion theorem.

## Attachments

None. I searched WeilConjectures/ in the read-only slopmaster2 checkout for the exact blueprint tag and the one-dimensional-component/conormal concepts, then read the relevant RingTheory and AlgebraicGeometry hits. The hits concern deformation-to-the-normal-cone terminology, generic components, divisor components or unrelated minimal primes; none states the item. No Lean or compiler was run. The upstream master checkout does not have the attempted WeilConjectures/RingTheory directory; it was not treated as evidence of any proof.

## WANTED

None. The Stacks source and the current blueprint are available locally.

## Findings and changes

The item was an unsplit statement with search evidence but no proof. Its statement is correct as written and remains unchanged. The argument follows the d=1 paragraph of Stacks Tag 0AW3 (more-algebra.tex, lemma-not-formally-catenary). I expanded its two compressed implications: a minimal-prime localization has nilpotent maximal ideal, and the conormal module has support contained in the closed point and is therefore killed by a maximal-ideal power.

I used the existing minimal-prime localization radical lemma plus the existing finite-generation/radical-power lemma to express the first implication directly. This is the elementary nilpotence content of the source's Artinian-local observation and does not require a new Artinian lemma. I used support rather than nonempty associated-prime language for the second implication: when J=0, the conormal module is zero and its associated-prime set is empty. Nothing in the proof asserts that the closed point must occur in the support.

The item's chapter, unit, source, imported searches, creation data and blueprint ancestry are preserved. I read the chapter and unit, and the main-20261015 ancestor proof, especially Step 3. This item's existing ancestry passes through arbitrary-field duality, completion dimensions and Ratliff's criterion; the split supplies precisely its conormal ingredient and does not change the perverse unit or its realization fields. The only off-unit nonleaf tool is lem-weil-pbc-adic-completion-noetherian, declared in split_report.tool_uses; the other cited theorems outside the unit are existing Mathlib leaves.

## Not duplicates

No new nodes were created. Whole-DAG keyword/tag searches and blueprint_refs.py searches for conormal, minimal prime and annihilator led to reuse of the existing minimal-prime-localization-radical, localization-noetherian, fg-ideal-radical-power, finite-module-support-annihilator and zero-locus-eq-iff-radical-eq nodes. The conormal blueprint hits define normal bundles or differentials, rather than the present local-ring assertion. Thus there are no new/existing same-tag pairs to distinguish.

## Mathlib searches read

The five fresh searches were run through msearch.py and their actual results read. LeanFinder was queried both for a maximal-ideal power annihilating the conormal and for a finite-length thickening of a one-dimensional component. The first returned Krull intersection, adic Hausdorffness and cotangent-space rank facts; the second returned principal nonzerodivisor quotients of finite length and dimension inequalities. Neither gives the item, since the ambient ring here may have other components of higher dimension and the quotient is J/J^2. Loogle's query for Ideal.Cotangent and pow had no hits. The RingTheory grep returned conormal terminology in Extension/Cotangent/Basic.lean, whose header and definitions I read; it concerns presentations and the cotangent complex, not this support argument. LeanSearch returned zero-dimensional localizations, an Artinian quotient criterion, Krull intersection, finite quotients and minimal-prime localization facts. I read the pertinent KrullDimension/Zero and KrullsHeightTheorem source: these are tools for parts of the argument, not a one-line specialization proving both clauses. No unavailable service was recorded as a negative result. No new node was declared absent from Mathlib.

## Review by Q119

I read Stacks more-algebra.tex Tag 0AW3, including its entire d=1 paragraph and its location in the Ratliff induction. For the generic tools I read the actual DAG statements and their relevant Stacks text: algebra.tex Tags 0316 (completion is Noetherian), 05GI/05GG (local completion and maximal ideal), 00FN (Noetherian localization), 00IM (a finitely generated ideal contained in a radical has a power in the ideal), 00L2 (support equals the zero locus of the annihilator), 00E0(7) (radical equals the intersection of containing primes), and smoothing.tex Tag 07FJ's minimal-prime step. There are no new-node sources to audit.

Step 1 uses lem-weil-pbc-adic-completion-noetherian exactly for Noetherianity of the maximal-ideal completion, lem-weil-pbc-local-completion-local-ring exactly for locality and maximal ideal mB, and def-weil-pbc-noetherian-ring for finite generation of ideals. Their hypotheses are satisfied by the item's Noetherian local A and specified completion; no excellence or catenarity is assumed.

Step 2 uses lem-weil-pbc-localization-noetherian for B_q, lem-weil-pbc-minimal-prime-localization-radical with I=0 and the given minimal q, and lem-weil-pbc-fg-ideal-radical-power with the finitely generated ideal qB_q inside the radical of zero. The quoted statements explicitly supply these conclusions under these hypotheses. The finite generation is justified by the cited definition of Noetherianity. I wrote out the images-of-products argument giving q^n B_q=0, instead of hiding an identification of extended ideal powers. The exponent is positive because the power-containment node states t>=1.

Step 3 is elementary from these conclusions and the cited definitions. The images of finite ideal generators generate J/J^2, and multiplication by J kills it. For p not containing q, the specified element x^n is both an annihilator and a unit after localization. At p=q I used the fraction-zero criterion from def-weil-pbc-localization-at-prime, so no unstated exactness-of-localization theorem is needed. For a prime strictly between q and mB, its quotient gives a length-two prime chain in B/q, directly contradicting the dimension-one hypothesis as defined by def-weil-pbc-krull-dimension-ring. The support convention used here is explicitly contained in the statement of lem-weil-pbc-finite-module-support-annihilator; that theorem's finite-generation hypothesis has already been verified. These elementary subarguments are steps of the proof, not new nodes or clauses relabelled as lemmas.

Step 4 uses lem-weil-pbc-finite-module-support-annihilator with the just-proved finite module M, then lem-weil-pbc-zero-locus-eq-iff-radical-eq for the precise intersection-of-primes formula. Every prime in that intersection must be mB; the empty intersection is also allowed. This establishes mB contained in the annihilator radical without assuming M is nonzero. Finally lem-weil-pbc-fg-ideal-radical-power applies to the finite ideal mB and the annihilator, giving positive c and exactly the asserted module annihilation. Its statement, and not any argument hidden in another node's proof, supplies the containment.

I checked delivery-errors B through E against the written file and these sources. The statements and dependencies introduce the needed objects; no new node is elementary, duplicated, unsourced or a clause of the item. Every non-elementary step uses a node whose actual statement supplies the fact taken from it, with verbatim citations recorded. The two explicit fraction arguments avoid invoking unrecorded exactness or associated-prime results. All steps are below 2000 characters. No SGA source is used.

Small cases: for a DVR A, q=0 and J=0, so n=c=1 works. For any reduced one-dimensional local ring, the minimal-prime localization has qB_q=0 and the same support computation works; this tests multiple components without needing B to be a domain. For the nonreduced test B=k[[t,e]]/(e^2), q=(e), n=2 gives J=0, while n=1 would generally have non-torsion conormal; thus choosing a sufficiently large power is essential. In the complete node B=k[[x,y]]/(xy), q=(x) gives B/q=k[[y]] and q/q^2 is killed by both x and y, illustrating the nonzero closed-point conormal case. These auxiliary B examples test the commutative-algebra argument; they are not asserted to be completions of local domains. A zero-dimensional completion cannot satisfy dim(B/q)=1, and q is proper throughout. The source's extra non-equidimensionality and universal-catenarity context are unnecessary for this particular lemma and are not introduced as hypotheses.

## Unfinished work

None in the mathematical split. Delivery validation is recorded below after the required tool finishes.

## Validation

The required deliver.py --no-push run completed successfully with exit code 0: server preflight passed at dry-run commit 2c80f7a49e. The subsequent final dry run includes this report addition. No Lean files were written and no compiler, Lake or build command was run.
