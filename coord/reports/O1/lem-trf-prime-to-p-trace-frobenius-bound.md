# Stage-1 delivery: lem-trf-prime-to-p-trace-frobenius-bound

## Files written

- dag/nodes/sec-trace-formula/lem-trf-prime-to-p-trace-frobenius-bound.json — statement, split; no Mathlib match for the whole estimate.
- citations.json — verbatim statement excerpts for every step/node citation (two excerpts for the trace node, covering finiteness and the formula).
- searches.jsonl — four actual O1 search responses; inherited item searches and their evidence retained in the item.
- report.md — this report.

No new nodes and no new Mathlib leaves. The proof reuses lem-sfb-algebraic-absolute-value-unique (Mathlib leaf), lem-trf-galois-trace-sum (Mathlib leaf), lem-trf-nonarchimedean-finite-sums (Mathlib leaf), and lem-trf-nonarchimedean-prime-power-root-estimates (existing unsplit node).

## Attachments

None. Searches of lean/WeilConjectures/ for the blueprint tag, normalizedTrace, trace_eq_sum_automorphisms, and the prime-to-p/Frobenius-trace notions found no project declaration giving this item. Matrix trace/Frobenius declarations concern different objects and do not attach the item. The public Algebra.normalizedTrace in Mathlib is defined under CharZero and does not supply the two norm estimates.

## Wanted sources

WANTED: Michael Temkin, Stable modification of relative curves, arXiv:0707.3953v3, archival PDF, Proposition 6.2.4 proof (printed p.47) and Lemma 6.2.10(i) (printed p.46), for lem-trf-prime-to-p-trace-frobenius-bound. The exact primary text was read online at https://arxiv.org/html/0707.3953v3#S6.SS2. The estimate in this item is an agent-supplied trace supplement, not a quoted theorem of Temkin. No source was downloaded or written into the shared repository.

## Problems found and repaired

The assigned node had no proof. Its statement is unchanged and is true under the hypotheses it actually has. The proof must include the correction between n^{-1} and n^{-p}; bounding only the pth-power cross terms would omit it. Applying the existing prime-power sum estimate to n copies of 1 supplies the needed bound without introducing a Fermat-congruence node. The proof also checks that the residue characteristic of E is p before applying that estimate to E. It uses neither tameness nor an algebraically closed base, which are absent from this item.

The current latest blueprint unit and ancestor concern contracting local terms. I read their current files; this assignment is an existing historical analytic auxiliary chain below that ancestor. I preserved its blueprint provenance and explained the precise normalized-trace support in split_report.blueprint, without replacing a unit or chapter step. The item is not the unit's key statement, so no unit record is changed.

## Unfinished work

None at the one-level stage-1 scope. The already existing prime-power estimate remains unsplit; this delivery does not rewrite or split another worker's node. No Lean was written and no compiler, Lake, or build tool was invoked.

## Not duplicates

No new nodes. Whole-DAG searches by trace/conjugates, absolute-value uniqueness, ultrametric sums, and prime-binomial divisibility identified the four reused nodes. The blueprint search command returned no matches for binomial, nonarchimedean, or Galois trace; the broad trace search and current ancestor did not give another statement of this item. In particular the affinoid Tate-trace bound has additional affinoid hypotheses and no normalized Frobenius estimate, so it cannot replace this item. The complete-minpoly norm formula is unnecessary because the existing absolute-value uniqueness leaf applies directly.

## Review by O1

I read the assigned statement, its parent coefficient-normalization statement, the chapter and unit records, the latest blueprint chapter, unit and locality node, and Temkin's online primary text at Proposition 6.2.4 and Lemma 6.2.10(i). For the existing Mathlib leaves I read spectralNorm_unique_field_norm_ext at Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean:770-773, trace_eq_sum_automorphisms at Mathlib/RingTheory/Trace/Basic.lean:263-272, and apply_sum_le_sup at Mathlib/Algebra/Order/Ring/IsNonarchimedean.lean:134-137. I also read the trace definition and scalar-trace proof at Mathlib/RingTheory/Trace/Defs.lean:65-123, the characteristic hypothesis in Mathlib/FieldTheory/NormalizedTrace.lean, and the matrix finite-field Frobenius hits. All four full cited node statements were opened. No new-node source review is needed because I created none.

Step 1 uses no black box: induction on integers gives norm at most one; reduction modulo the norm-less-than-one ideal and p not dividing n give norm n = 1. The residue injection is justified by equality of the kernels under the compatible absolute values; nonzero residue classes have unit-norm representatives with inverses in the unit ball. Thus the characteristic is the same in E and F. This explicitly supplies the hypotheses for step 5.

Step 2 is a diagonal-entry calculation in an n-element F-basis: multiplication matrices respect addition and scalar multiplication, while multiplication by c in F is c times the identity. This proves F-linearity and the retraction clause with no use of a general normalized-trace theorem. It uses the definition of the trace already given in the item's statement. I retained this elementary calculation instead of creating a duplicate or a clause-restatement node.

Step 3 uses exactly the uniqueness conclusion in lem-sfb-algebraic-absolute-value-unique. The two functions being compared are absolute values, their restrictions agree because each automorphism fixes F, the base F is complete and nontrivially nonarchimedean, and algebraicity follows by writing the linear dependence of powers in the finite-dimensional space. The node imposes no completeness condition on the extension; the stronger completeness of E in the item is harmless. There is no appeal to a norm-preservation fact hidden in the trace node.

Step 4 uses the finite automorphism group and trace-equals-sum formula from lem-trf-galois-trace-sum, with exactly finite Galois E/F as assumed. Identity supplies a nonempty indexing family. It then uses the first clause of lem-trf-nonarchimedean-finite-sums with the given absolute value; symmetry follows from absolute-value multiplicativity and |-1|=1. The uniqueness result from step 3 identifies the maximum with |x|. Compatibility and norm n^{-1}=1 finish the contraction. No equality between the cardinality of the Galois group and n is needed.

Step 5 uses only the first displayed inequality of lem-trf-nonarchimedean-prime-power-root-estimates. I checked its exponent is p^1, its family is finite nonempty in both applications, and its residue characteristic agrees by step 1. The first application gives |S^p-U| <= |p||x|^p, since every automorphism preserves powers and norms. The second has exactly n copies of 1 in F and gives |n^p-n| <= |p|. Dividing by n is legitimate with norm one. The root-existence and difference clauses of that node are not used.

Step 6 writes the exact two-summand identity, rather than asserting that trace transports Frobenius. Multiplication and inversion preserve the indicated norms, and the bound on U is the already proved contraction calculation applied to x^p. The ultrametric inequality takes the maximum of the two bounds, with no factor 2. All its facts are explicit algebra from earlier steps and the defining norm axioms.

I tested degree n=1 (T is the identity), x=0, x in F, mixed characteristic with p=2 and odd n, and equal characteristic p. In equal characteristic the two bounds used in the last step have zero right side, so the Frobenius assertion is exact; n is still nonzero since p does not divide n. For p=2,n=3 the nonzero mixed-characteristic normalization correction is accounted for by n^p-n=6, showing why it cannot simply be discarded. No statement dispute or additional hypothesis is needed.

Against delivery-errors B, every object used in the proof is introduced and no proof is hidden in a new statement. Against C, each non-elementary fact is one of the four existing statements, quoted verbatim in citations.json; the quoted facts have the hypotheses just checked. Against D, the six steps carry the argument and neither move the conclusion into a new node nor use the parent (which would create a cycle). Against E, the residue field, exponent, trace scalar and normalization terms are kept distinct. Every step is shorter than 2000 characters, so no long-step exception or hidden-lemma extraction is needed. All four new Mathlib searches were run with the required msearch command and read; two differently phrased semantic searches supplement the Loogle and grep results. Their real responses were appended, with no invented search entry. The inherited search records remain as prior evidence.

## Preflight repair

The first dry run rejected the uniqueness citation excerpt because it was shorter than the required 40 characters. I replaced it with the entire verbatim node statement, including the hypotheses and conclusion. The proof and its dependencies did not need changing.
