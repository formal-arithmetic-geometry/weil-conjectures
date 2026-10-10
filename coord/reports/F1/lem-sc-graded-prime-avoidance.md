Files written:
- `lem-sc-graded-prime-avoidance.json` — statement, split proof, no new nodes; no Mathlib leaf.
- `citations.json` — no proof-step node citations; all steps are elementary algebra from the stated hypotheses.

Attachments:
- None.

WANTED:
- None.

What was wrong or changed:
- The imported item was statement-only despite its source containing a complete proof. I expanded it into the induction proof of Stacks Algebra Lemma 00JS. The proof explicitly handles removal of inclusions, the base case, the product-ideal noncontainment argument, homogeneous choice, and the final sum of powers. No statement was changed and no auxiliary node was required.

What could not be finished:
- Nothing.

## Review by F1
I read the item statement and its source citation against the exact Stacks text in `/home/ubuntu/c1-stacks-review/algebra.tex`, lines 15542--15579, labelled Algebra Lemma 00JS (`lemma-graded-silly`). The statement's hypotheses match: a graded ring, homogeneous prime ideals, a graded ideal inside the positive-degree ideal, and noncontainment in each prime. I also read the cited statement of `def-pc-proj`; it supplies the nonnegative graded commutative ring and positive-degree homogeneous notation used by the item. No new node was created, so there are no additional source statements or Mathlib searches to review.

Step 1 is the source's reduction to a list with no inclusions; avoiding a larger prime implies avoiding a contained smaller prime. Step 2 checks the `r=1` case by taking a homogeneous component outside a homogeneous prime, with positive degree forced by `I subset S_+`. Step 3 is the induction hypothesis and its immediate termination case. Step 4 spells out the source's product-ideal argument: pairwise noncontainment supplies factors outside the final prime, and primality forces a contradiction if the product ideal were contained. Step 5 verifies the product ideal is graded, chooses homogeneous `y`, checks equal positive degrees of the two powers, membership in `I`, and nonmembership in each prime using primality. These are all direct one-line consequences of the definitions and the preceding choices, so each step is marked elementary and `citations.json` is correctly empty.

I tested the edge cases in the source argument conceptually: `r=1` is the base case; for `r=2`, the final element is `x^(deg y) + y^(deg x)` with `y in I p_1`, and the two prime-membership checks specialize exactly as stated. The positive-degree condition excludes degree-zero cancellation concerns. The DAG statement and its `def-pc-proj` dependency were left unchanged.
