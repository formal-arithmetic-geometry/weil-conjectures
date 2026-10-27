# Stage-1 report: lem-sfb-finite-domain-polynomial-extension-data

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-domain-polynomial-extension-data.json: statement split, unchanged statement and statement dependencies; no full Mathlib match. Five proof steps reuse four existing Mathlib leaves.
- citations.json: the exact current statements of every cited node, once for each citing step.
- report.md and searches.jsonl: author review and actual search-command log.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id and polynomial/normal-domain and module-generator terminology, including RingTheory and AlgebraicGeometry. No declaration gives the complete item. The appearances in PolynomialRingN2, finite-extension and Nagata arguments are not a theorem with all these hypotheses and conclusions. The source library is read-only and no compiler was run.

## WANTED

None for this item. All algebra sources required here are present in literature/stacks-project/. The inherited ancestor's remark about a wanted de Jong PDF does not affect these elementary algebra prerequisites.

## What needed repair

The imported item was statement-only, not a completed split. Its statement is correct and is preserved exactly. The old searches and inherited provenance remain. The item is not one Mathlib leaf: in particular the fixed family of module generators requires a coefficient calculation. I used existing generic leaves rather than creating copies of each conclusion.

Read the latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, together with the chapter and unit records. This is a subordinate algebra prerequisite on the inherited alteration/universal-openness route; it changes no unit or chapter route. The ancestor command returns None, as does the inherited blueprint.from.node, so that value is retained rather than inventing a blueprint id. The inherited precise place and via chain remain. Blueprint searches for polynomial and normal domain found no blueprint theorem stating this package.

## Not duplicates

No new nodes were created. Existing lem-weil-pbc-polynomial-ring-normal-domain (030A), lem-weil-pbc-finite-type-algebra-noetherian (00FN), lem-weil-pbc-finite-type-noetherian-finite-presentation (00FP), and lem-weil-pbc-finite-algebra-is-integral (00GK) are reused. The item additionally keeps the given coefficient map and the prescribed spanning family, so it is not a duplicate of any one of these statements.

## Review by Q34

I read Stacks algebra.tex at lemma-polynomial-domain-normal (030A), lemma-Noetherian-permanence (00FN), lemma-Noetherian-finite-type-is-finite-presentation (00FP, especially (3)), and lemma-finite-is-integral (00GK), including their proofs. I verified the labels against tags/tags. I also read more-morphisms.tex lemma-quasi-finite-Noetherian-universally-open (0F32): it motivates adjoining affine-space coordinates but does not itself state the coefficient calculation. That calculation is supplied here, with proof_origin.by = agent. No SGA source is used.

Step 1 uses the statement of def-weil-pbc-mv-polynomial-ring: the finite monomial expansion and multiplication law give the coefficient map and equality coefficient by coefficient. Injectivity is exactly the hypothesis on phi, without assuming that C is normal. There is no hidden assertion that an injective coefficient map is an isomorphism. The Mathlib source MvPolynomial/Eval.lean:385-405 independently confirms this calculation.

Step 2 uses that same polynomial definition to give the regrouping isomorphism and its inverse. The leading-coefficient argument proves the domain clause for C one variable at a time. The statement of lem-weil-pbc-polynomial-ring-normal-domain explicitly gives both domain and normality for a one-variable extension of any normal domain, so induction starts at A and applies it at every stage. No Noetherian hypothesis is needed for that lemma, and no normality is incorrectly assumed for C. This uses the statement, not a construction buried in its proof. I read its recorded Mathlib instance in Polynomial/IsIntegral.lean:179-181.

Step 3 uses the polynomial definition to exhibit a finite-type A-algebra and uses the statement of lem-weil-pbc-finite-type-algebra-noetherian, which requires only a Noetherian base and finite type. Both hypotheses hold for A -> A_n. I read Algebra.FiniteType.isNoetherianRing in RingTheory/FiniteType.lean:187. It is already a Mathlib leaf, so its other unit is not a route replacement.

Step 4 uses only the stated finite-monomial polynomial definition and the original spanning hypothesis. For each coefficient of a polynomial, choose its given finite linear expression and write down p_j explicitly; distributing two finite sums proves f = sum phi_n(p_j)c_j. Any subalgebra containing the c_j contains these linear combinations, which proves the same family's algebra generation and the surjectivity of the evaluation map. No tensor-product comparison, flatness, or independent base-change theorem is used. This short elementary calculation remains a step instead of a new node.

Step 5 uses exactly the statements of lem-weil-pbc-finite-type-noetherian-finite-presentation and lem-weil-pbc-finite-algebra-is-integral. Their inputs are the Noetherian A_n from step 3 and the finite-type/finite-module C_n from step 4; their conclusions are algebra finite presentation and monic relations, respectively. In particular, module finite presentation is not substituted for algebra finite presentation. I read RingTheory/FinitePresentation.lean:69 and IntegralClosure/Algebra/Basic.lean:64-73 to check the existing leaves.

For the citation audit I opened every cited node and copied its current statement verbatim into citations.json. None is a definition being used for a non-elementary theorem. There are no new statement-only nodes needing their own sources or missing notions. The five steps are all under 2000 characters; the leading-coefficient and regrouping arguments are routine and explicit, while each substantive normality/Noetherianity/finite-presentation/integrality theorem is a cited node.

I checked n=0 (one monomial, unchanged coefficient map and original spanning expression), n=1, identity extensions, finite field extensions, zero/repeated generators, and r=0. Empty generators would force C to be the zero ring, contradicting the domain hypothesis, so there is no missing nonemptiness assumption. Domains are nonzero throughout. No statement dispute was needed.

The five added search records are actual command runs, with two different semantic phrasings, Loogle, grep and LeanSearch. Returned polynomial finite-presentation instances are over the coefficient base, and Noether normalization chooses a new map over a field; neither is a one-line theorem for this whole fixed-map, fixed-family package. The successful grep for map_injective covers only step 1, which is proved explicitly. Searches inherited from the live node are retained rather than claimed as fresh runs.

## Unfinished work

None in the stage-1 split. This delivery contains no Lean implementation and requests no changes to other workers' nodes.
