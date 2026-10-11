Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-kinjective-characterize-K-injective.json`: statement node split into four proof steps; Mathlib search found no exact bounded-size criterion.
- `dag/nodes/sec-smooth-purity/lem-pur-kinjective-homotopy-exact-injective-target.json`: statement-only child; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-kinjective-homotopy-limit-vanishing.json`: statement-only child; no Mathlib match.
- `citations.json`: verbatim citations for every step.

Attachments: none.

WANTED: none.

## Not duplicates

`lem-pur-kinjective-homotopy-exact-injective-target` vs existing K-injective nodes: the existing nodes state K-injectivity or bounded-below injective criteria, whereas this child states exactness of the three Hom groups induced by an arbitrary short exact sequence of complexes with a termwise injective target.

`lem-pur-kinjective-homotopy-limit-vanishing` vs `lem-weil-pbc-mittag-leffler-complex-limit-homology`: the existing node treats countable inverse systems of abelian-group complexes and an essentially constant cohomology system; this child treats a continuous transfinite union of subcomplexes and vanishing of homotopy-category Hom into an injective-term complex.

## Review by K1

I read `/home/ubuntu/c1-stacks-review/injectives.tex`, Lemma `lemma-characterize-K-injective`, including its full proof from the transfinite filtration through the successor and limit cases. The returned review exposed that the previous split incorrectly used the existential-cardinal child for the item's fixed `kappa`; I therefore checked the item's own clause (a), which supplies the needed small subcomplex for every quotient. The imported item statement agrees with the Stacks hypotheses, including the Grothendieck category, the cardinal size convention, injective terms, and null-homotopy hypothesis for bounded-above small acyclic complexes.

Step 1 follows the source's ordinal construction: at a proper successor the item's own clause (a) supplies a nonzero bounded-above acyclic subcomplex of the nonzero quotient; its inverse image is acyclic as an extension, limit colimits remain exact by the Grothendieck hypothesis, and the cardinal bound on subobjects forces termination. Step 2 uses the exactness child for the displayed sequence after shifting the target to `I[n]`; the shift remains termwise injective, and hypothesis (2) applies to every shift of the bounded-above small acyclic quotient, so the induction proves vanishing for every `n`. Step 3 uses the repaired limit child for the source's Hom-complex inverse-limit/Mittag–Leffler argument, simultaneously for every shift; the transition maps are surjective because every term of every shifted target is injective. Step 4 specializes the all-shifts conclusion to `n = 0` and uses the existing K-injective definition to obtain null-homotopy.

I checked the new child statements against the exact sentences used in the source and tested the edge cases `M^bullet = 0` (the filtration starts at zero and the conclusion is immediate), a complex already equal to the initial subcomplex at a successor (the chain is kept unchanged), and shifts `n` and `-n` (the hypotheses and conclusions quantify over all integers). Both new children were searched in the DAG and blueprint before creation, and all required Mathlib searches were run; LeanSearch was unavailable and is recorded as unavailable rather than as a no-match.

What was wrong in the returned item was threefold: the limit child was false without all-shifts vanishing; the induction only proved degree zero; and Step 1 cited a child with an unrelated existential cardinal. I repaired these by strengthening the child to all shifts, making the successor and limit inductions simultaneous in every shift, specializing to zero only in the conclusion, and using the item's own clause (a) with the filtration argument written out as an elementary Grothendieck-category construction.

What could not be finished: no Lean declaration in either source checkout states this exact criterion, so the item remains a stage-1 split rather than an attachment.

## Second reading by K1

- Item statement: checked hypothesis by hypothesis against Stacks `lemma-characterize-K-injective`, including the Grothendieck category, size bound, both bounded-size clauses, injective terms, and null-homotopy conclusion; verdict: agrees.
- Step 1: checked against the transfinite construction in `injectives.tex`; the item's clause (a) applies to each nonzero acyclic quotient, and exact filtered colimits plus the subobject-cardinality argument justify the limit and termination claims; verdict: repaired and sound.
- Step 2: checked against the displayed successor exact sequence after replacing `I` by every shift `I[n]`; hypothesis (2) applies to each shifted bounded-above acyclic quotient; verdict: repaired and sound.
- Step 3: checked against `homology-lemma-ML-over-ordinals` and the source's inverse-limit Hom-complex argument; the all-shifts hypothesis is now explicit and injectivity gives surjective transitions for each shift; verdict: repaired and source route matches.
- Step 4: checked against the definition of K-injective; the all-shifts induction is specialized to `n=0`, and vanishing in the homotopy category is equivalent to null-homotopy; verdict: sound.
- Child `lem-pur-kinjective-homotopy-exact-injective-target`: checked its arbitrary abelian-category hypotheses and exact Hom sequence against the successor paragraph; verdict: correct. Repaired the cochain-complex dependency to the generic complex definition.
- Child `lem-pur-kinjective-homotopy-limit-vanishing`: checked the limit-system hypotheses and the ordinal Mittag-Leffler source lemma; verdict: corrected to require a Grothendieck abelian category (the AB5 context used by the item) and the generic complex definition.
- Edge cases checked: zero acyclic complex, filtration already equal to the ambient complex, and a one-term complex over a field; all are consistent.

Changes made: strengthened the limit child to require and conclude `Hom_K(-, I[n]) = 0` for every integer shift; removed the unrelated bounded-size child from Step 1 and proof dependencies; made Steps 2 and 3 simultaneous over all shifts; and updated the citations and Mathlib-search log. The child statements retain the generic complex citation and Grothendieck hypothesis checked in the prior review.

### Correction to the second reading

- Step 2: rechecked against the source successor exact sequence and the item's actual hypothesis (2); the induction is now on `Hom_K(K_alpha[n], I)`, and hypothesis (2) is applied to the shifted source `N_{beta+1}[n]`, which remains bounded above, acyclic, and termwise bounded by `kappa`.
- Step 3: rechecked against the source Hom-complex inverse-limit argument and `homology-lemma-ML-over-ordinals`; the limit child now assumes vanishing of `Hom_K(K_beta[n], I)` for every earlier beta and every integer n, the acyclicity condition needed by the Mittag--Leffler argument.
- Step 4: rechecked against the K-injective definition; the induction conclusion is specialized only at `n=0`.
- Child `lem-pur-kinjective-homotopy-limit-vanishing`: the former H^0-only hypothesis was false; the statement was repaired to all shifted sources after checking the Ab counterexample recorded in `coord/returns/K1.md`.

Additional changes: updated Step 2 and Step 3 wording, replaced the child citation quote in `citations.json`, and corrected the report's description of the item's hypothesis (2). The earlier second-reading endorsement of the weaker limit child is superseded by this correction.
