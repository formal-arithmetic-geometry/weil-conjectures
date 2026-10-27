## Files written

- dag/nodes/sec-trace-formula/lem-trf-nonarchimedean-prime-power-root-estimates.json: existing statement split into five steps; no new nodes and no new Mathlib leaves. Statement and statement dependencies retained exactly.
- citations.json: the full verbatim statement of each of the two cited nodes, both used in step 2.
- searches.jsonl: searches actually run with msearch.py. Prior searches in the live item are preserved.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag, item id, nonarchimedean, prime-power root, sum-power and root-estimate terminology. The PadicAlgCl logarithm/exponential estimates concern powers near 1 in a specific complete p-adic algebraic closure, and do not state this item for arbitrary valued fields and arbitrary roots. No project attachment covers the three clauses.

## Literature

WANTED: literature/temkin-stable-modification-arXiv-0707.3953v3.pdf, Lemma 6.2.10(i)--(ii), printed p.46, for lem-trf-nonarchimedean-prime-power-root-estimates. This PDF is absent from the read clone. I did read the published arXiv v3 text through the browser at https://arxiv.org/pdf/0707.3953v3, printed p.46 (PDF page 46, zero-based page 45): the two estimates and its instruction to estimate the power of the root difference agree with the item. No file was downloaded or written outside the sandbox. The proof is marked agent-written because it supplies the omitted binomial calculation and the difference/sign argument, with the available Stacks arithmetic source identified precisely.

Read literature/stacks-project/algebra.tex, Tag 0545, label lemma-help-with-powers, especially its interior binomial coefficient divisibility argument. This is the source of the existing coefficient node; the statement used is its explicit divisibility assertion, not the stronger subring conclusion of Tag 0545. Read Mathlib/RingTheory/WittVector/Frobenius.lean:116--119 (map_frobeniusPoly.key₁) and Mathlib/Data/Nat/Choose/Sum.lean:76--78 (add_pow), confirming both existing Mathlib leaves against their statements.

## What was wrong or incomplete

The item had no proof. The statement itself is correct, including n=0, all choices of roots and characteristic p. No statement correction or STATEMENT-DISPUTED marking is needed. The difference clause needs explicit treatment of p=2: applying the sum estimate to u,-v alone leaves the endpoint term 2v^q when q is even. That term has exactly the required |p| factor. Step 4 supplies it.

The latest blueprint's lem-trf-local-term-locality proof now uses contracting correspondences directly, rather than the historical nearby-cycle semistable-alteration branch recorded in this created node's ancestry. I read that latest proof and unit, and retained the assigned lower arithmetic item's inherited provenance; I did not change the ancestor, unit, chapter, or route. This split serves the existing parent lem-trf-analytic-special-coset-leading-bound and does not assert the obsolete branch is required by the current blueprint.

## Mathlib and duplicate searches

Ran LeanFinder with two different phrasings, LeanSearch, Loogle and grep through the mandated msearch command; read their returned names and signatures. IsNonarchimedean.add_pow_le and RingSeminorm.exists_index_pow_le only bound a power of a sum, without its Frobenius defect. sum_pow_char_pow is an equal-characteristic identity. PreTilt.valAux_add is an inequality on a tilt, not arbitrary roots in E. Read all these candidates' source (including Mathlib/RingTheory/Perfection.lean:764ff and Algebra/CharP/Lemmas.lean:350ff). None makes the whole item a one-line specialization.

Whole-DAG concept searches and blueprint_refs search for binomial, binomial expansion, prime-power, nonarchimedean and absolute value found the two needed existing Mathlib leaves. The binomial-divisibility leaf supplies more than the needed divisibility by p. No new statement was created for a clause of the item or for any elementary induction, norm bound, or root comparison.

## Not duplicates

No new nodes. Reused lem-pur-prime-power-binomial-divisibility and lem-pur-commutative-ring-binomial-expansion rather than duplicating them. Both have status mathlib, so their use as generic arithmetic tools across units is permitted without a new tool-use authorization.

## Review by NN

I checked delivery-errors B through E against the actual item and the two dependency statements. The original item is retained, and all proof work is in its steps: there is no statement-only node taking over a clause. Both citations in step 2 are supported by their entire verbatim statements in citations.json, which I read before selecting them.

Step 1 uses only the defining ultrametric and multiplicative axioms: integer norm <=1 follows by repeated addition, divisibility then bounds an integer by |p|. I wrote why the residue quotient is a field and why positive characteristic is prime, rather than imposing primality as an extra hypothesis. The inverse argument uses norm exactly 1 outside the open unit ball. I separated n=0 before any use of an interior coefficient or parity.

In step 2 the coefficient node applies with prime p, a=n and 0<j<q, which ensures v_p(j)<n and thus a positive divisor exponent. Its statement really gives divisibility of the binomial coefficient, not merely a Frobenius identity in characteristic p. The binomial expansion node applies to the commutative field E; removing endpoints gives the exact error displayed. Every mixed monomial has total degree q, so its norm is bounded by |p| M^q. Finite ultrametric addition is a direct induction from the stated axiom. These are precisely the two non-elementary inputs, with citations and sources.

Step 3 states the finite-sum induction claim, its j=1 base, and the error decomposition for j+1. The uniform maximum M also bounds every partial sum by ultrametric addition. It invokes the two-variable bound proved in step 2, not a nonexistent external sum lemma. Step 4 handles odd p and p=2 separately; in the latter case I checked the sign by expanding the exact displayed identity, including when E has characteristic 2.

Step 5 applies the proved sum bound to the chosen roots themselves, giving |B^q-y^q|<=|p|R^q. It first proves |y|,|B|<=R, so the proved difference bound is applicable with the same maximum. Adding the two explicitly identified errors gives the q-th power of the root difference. Nonnegative real q-th roots preserve this inequality since q>=1; multiplicativity identifies R with the maximum of the input root norms. This argument makes no assumption of completeness, algebraic closedness, existence of roots beyond the stipulated ones, or uniqueness of the root choices.

I tested n=0, t=1, all zero inputs, mixed characteristic with p=2 and q even, and equal characteristic |p|=0. In the last case the proof forces all errors to vanish, as expected for injective Frobenius in a field. In t=1 it still controls possibly different q-th roots of the same input. All five steps are under 2000 characters; none hides a further comparison theorem or source lemma. There are no unintroduced notions, new tags, off-route non-Mathlib tools, or cycles introduced.

## Unfinished work

None in the assigned split. The two arithmetic leaves already exist in Mathlib. The missing local Temkin archive is recorded above; its relevant published text was independently read online. No Lean was written or compiled, no git command was run in the repository, and all authored files are in the assigned sandbox.
