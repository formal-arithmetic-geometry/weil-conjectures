Files written:

- `dag/nodes/sec-picard-framework/lem-sc-affine-pseudo-coherent-lift.json` (statement, split; no Mathlib match)
- `dag/nodes/sec-picard-framework/lem-sc-pseudo-coherent-qcoh.json` (statement-only, no Mathlib match)
- `dag/nodes/sec-picard-framework/lem-sc-qc-open-derived-lift.json` (statement-only, no Mathlib match)

Attachments: none.

WANTED: none.

I found no declaration tagged `(blueprint: lem-sc-affine-pseudo-coherent-lift)` and no sorry-free declaration stating the item in either Lean source checkout. I searched the DAG and blueprint for pseudo-coherent lifting, affine finite-free models, and the Tag 08EE route; the existing affine criterion and affine derived-equivalence nodes are cited rather than duplicated. The two preliminary reductions used by Tag 08EE were not already nodes, so they are recorded as statement-only children.

## Review by E1

I read the complete Stacks proof of Tag 08EE (Lemma 36.13.6) in `/home/ubuntu/c1-stacks-review/perfect.tex`, including the preceding `lemma-lift-quasi-coherent` and affine comparison calls. Step 1 uses exactly the statements of the two new children: pseudo-coherence gives quasi-coherent cohomology, and a quasi-coherent derived object on the quasi-compact open lifts to the affine scheme. Step 2 uses the existing affine derived equivalence and affine pseudo-coherence criterion, with X introduced as Spec(A) and U covered by finitely many principal opens. Steps 3 and 4 spell out the source's descending cone induction and its hypotheses: localized cone cohomology vanishes in degrees at least n, finite localized H^(n-1) supplies generators, and denominator clearing makes one finite free A-module work on every principal open. Step 5 checks that sheafifying the resulting bounded-above finite-free complex gives the required restriction. I checked the zero-complex case (take the zero complex as the initial model) and the one-open case (the induction is the usual affine finite-free replacement). Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such in the search log.

The source's phrase “Some details omitted; hint: clear denominators” is expanded in step 4 rather than hidden. No statement was changed.

## Second reading by E1

Step 1 checked against Stacks Tag 08EE and labels `lemma-pseudo-coherent` and `lemma-lift-quasi-coherent`; verdict: correct, and both cited child statements supply exactly the reductions used.
Step 2 checked against Tag 08EE and the affine comparison and pseudo-coherence criterion nodes; verdict: correct affine setup and finite principal cover.
Step 3 checked against the full Tag 08EE induction and More on Algebra Tags 064R and 064S; verdict: the cone and finite-generation claims were non-elementary and are now cited by new supporting nodes.
Step 4 checked against the denominator-clearing paragraph of Tag 08EE; verdict: replaced the vague clearing-denominators phrase with representatives, common powers, and the zero-composite argument.
Step 5 checked against the final sentence of Tag 08EE and the affine equivalence; verdict: correct sheafification and restriction conclusion.
Node `lem-sc-affine-pseudo-coherent-lift` checked against Tag 08EE, including zero-complex and one-open cases; verdict: exact statement.
Nodes `lem-sc-pseudo-coherent-qcoh` and `lem-sc-qc-open-derived-lift` checked against the two preliminary lemmas invoked in Tag 08EE; verdict: distinct and correctly scoped.
Node `lem-sc-cone-pseudo-coherent` checked against More on Algebra Tag 064R; verdict: necessary nontrivial triangle lemma, statement specialized to the used direction.
Node `lem-sc-finite-cohomology` checked against More on Algebra Tag 064S; verdict: necessary finite-generation lemma, statement specialized to the used clause.

Changes: added the two missing supporting nodes and citations for step 3; made step 3 non-elementary; expanded step 4's denominator-clearing argument to remove the unsupported shorthand.

## Not duplicates

lem-sc-pseudo-coherent-qcoh vs lem-sc-affine-pseudo-coherent-lift: the child only states that pseudo-coherent objects have quasi-coherent cohomology, while the item additionally constructs a bounded-above finite-free lift on the affine scheme.
lem-sc-qc-open-derived-lift vs lem-sc-affine-pseudo-coherent-lift: the child only lifts an arbitrary quasi-coherent derived object to X, while the item adds pseudo-coherence and constructs a finite-free complex.
