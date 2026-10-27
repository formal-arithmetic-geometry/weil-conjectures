## Files written

- dag/nodes/sec-trace-formula/lem-trf-compact-direct-power-transport-normalization.json: statement, split; no whole-item Mathlib match.
- citations.json: nine verbatim excerpts, one for every cited node in every proof step.

No new nodes; zero Mathlib leaves. The item statement and all maintainer-owned fields are unchanged.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag and for compact transport, Frobenius transport and power terminology. AdicSystem.lean:151-169 defines Etale.compactPullback but gives no power-normalization theorem. The related Sheaf/Paper/FrobeniusOperatorCompactDescription.lean theorem still has sorry and assumes a strict Weil complex, so it is not an attachment for this arbitrary bounded constructible M. The generic induction theorem in Sheaf/CategoryTheory/NaturalTransportInduction.lean is proved and belongs to the already existing lem-trf-frobenius-transport-induction; it does not itself state this geometric item.

## WANTED

None.

## Audit findings

The imported item had no proof. Its statement is retained. All necessary auxiliary statements already exist, so making power normalization or its invertibility a new node would merely restate clauses. The four-step proof instead checks the domain, assembles the recurrence and actual-comparison equation, applies existing natural transport induction, and proves invertibility by composing degree-one inverses.

One neighboring notation should be reviewed separately: def-trf-frobenius-pullback-power-comparison writes C_{a,b}:P_{a+b}≅P_b∘P_a but then uses C_{1,m} in d_{m+1}=T(d_m)∘C_{1,m}; the displayed codomain would require C_{m,1}. The actual Lean construction frobeniusPullbackPowerSplit 0 r followed by whiskering d_r has codomain T∘P_r, and lem-trf-frobenius-pullback-comparison-coherence explicitly states precisely that comparison c_{g,g^r}. Our item specifies the actual canonical d_r; its proof uses the unambiguous component equation from that coherence statement. No swapped functors or literal identity between pullbacks is assumed. No edit to that other worker's definition node was made.

## What remains unfinished

Nothing in this stage-1 item. This delivery does not claim the existing auxiliary nodes' Lean sorries have been proved.

## Not duplicates

No new nodes. Whole-blueprint searches for “repeated transport” and “pullback power” returned no blueprint match. DAG searches found the existing composition, coherence and generic induction nodes, which are reused. The parent compact-description theorem also involves a Weil structure and its global operator, so it is not the present arbitrary-coefficient normalization assertion.

## Review by Q115

I read delivery-errors B–E in full, the chapter/unit records, the current main-20261015 compact-description proof, and Deligne Weil II (1.1.10), (1.1.11), (1.1.14), printed pages 151–153 (PDF pages 16–18). Deligne supplies the transport-of-structure motivation, not this explicit derived finite-level comparison identity; the proof_origin is therefore agent. I also read the actual construction and docstring in Sheaf/Paper/FrobeniusOperatorCompactDescription.lean, the recursive comparison and coherence theorem in FrobeniusPullbackComparisonCoherence.lean, and the complete proved NaturalTransportInduction.lean argument. There is no new-node source to check.

For step 1 I opened lem-weil-frobenius-square-cartesian and used only its explicit scheme-isomorphism clause, specialized to the structure morphism. Powers have the written inverse. I then opened lem-weil-isomorphism-derived-pullback: its finite A clause gives bounded constructibility and the derived-to-termwise inverse-image isomorphism. Here g^r is an isomorphism, ell is invertible since ell differs from the characteristic, and M is bounded constructible. This proves the domain for every P_r and, repeatedly, T^r without flatness or finite Tor-amplitude of M. Restriction of a natural isomorphism to a full invariant subcategory adds no theorem.

For step 2 I checked that def-weil-frobenius-cohomology-transport explicitly asserts naturality of the degree-one map. I read the entire statement of lem-trf-compact-frobenius-transport-composition: it fixes the same c_0 for all powers, defines direct maps from point transport and the actual compactification exchange independently of the recurrence, and gives that recurrence on arbitrary D^b_c objects. I matched its c_r with the inverse of c_{g,g^r} in the statement of lem-trf-frobenius-pullback-comparison-coherence. The latter gives d_{r+1}^{-1}T(d_r)=b_r with exactly T∘P_r as source. I read def-trf-frobenius-pullback-power-comparison for the prescribed actual comparisons, noting the indexing issue above and checking the actual Lean definition rather than silently choosing alternative comparisons.

For step 3 I checked every hypothesis of lem-trf-frobenius-transport-induction against steps 1–2: invariant category, P_1=T, d_1=id, comparison identity, natural eta, direct tau_1=eta and the recurrence. def-trf-coefficient-conventions states H=Fib_s Ra_! into finite A-module coefficient complexes. The result is equality in that derived category. The general induction is a genuine smaller existing categorical theorem, not a new copy of this geometric item.

For step 4 I read clause 3 of lem-weil-frobenius-cohomology-transport-iso and applied only its finite-stage statement at T^j M. Its hypotheses match the same finite field, scheme and coefficient data. The remaining assertion is elementary: functors send an inverse pair to an inverse pair, and reversing the order of the finite list of inverse maps gives the inverse of the composite. Equality from step 3 transfers invertibility to the independently defined direct map. The off-unit square, isomorphism-pullback and degree-one invertibility statements are generic tools; split_report.tool_uses explains each.

I tested r=1 (identity d_1, a single transport), r=2 (the recurrence and single comparison inverse), M=0, and the empty scheme. All formulas remain typed; there is no use of nonzero cohomology, properness of X_0, or a chosen Weil structure. For n>1 one can take a nonperfect finite A-module as a coefficient object; the argument still uses only bounded constructibility and scheme-isomorphism pullback. There is no extra finite-Tor hypothesis hidden in the cited finite clauses. Every step is shorter than 2000 characters, and the entire assembly is below 3000. No inline non-elementary sublemma remains.

Mathlib searches were run with msearch.py and their actual summaries read from searches.jsonl after an interrupted provider response. Closest hits were sheaf-module pullback composition (PullbackContinuous.lean:167–182), shift-pullback comparison (Shift/Pullback.lean:252), Frobenius ring-equivalence iteration (FieldTheory/Perfect.lean:142–157), and essential-image invariance (EssentialImage.lean:69–75). None states compact-support transport or gives the full item by one-line specialization. Two semantic phrasings were used. The inherited searches were preserved; five new logged searches were appended honestly. citations.json quotes were checked as literal substrings of the current node statements. No SGA route, Lean write, compiler invocation, or repository write was used.
