# Stage-1 report: lem-a1-punctual-bound-module-mixed

Group Q118, 2026-10-21. Direct delivery; no other agents were started.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-a1-punctual-bound-module-mixed.json: item, statement, split into seven proof steps.
- dag/nodes/sec-deligne-laumon-a1/lem-a1-quotient-dimension.json: new statement, Mathlib leaf, Submodule.finrank_quotient_add_finrank, Mathlib/LinearAlgebra/Dimension/RankNullity.lean:248–252.
- dag/nodes/sec-deligne-laumon-a1/lem-a1-real-logarithm-power.json: new statement, Mathlib leaf, Real.rpow_logb and Real.logb_le_iff_le_rpow, Mathlib/Analysis/SpecialFunctions/Log/Base.lean:146–148 and 206–207.
- citations.json contains a verbatim statement quotation for every proof-step citation. searches.jsonl preserves the actual msearch results. report.md is this report. write_split.py is sandbox-only scratch work.

## Attachments

No qualifying ATTACH under the direct brief's rule requiring a declaration under WeilConjectures/.

FrobeniusModule.hasWeightsAtMost_of_forall_hasEigenvalue, lean/WeilConjectures/ZetaLinearAlgebra/FrobeniusModule/Exact.lean:127, has proof `h`; its conclusion is the eigenvalue predicate HasWeightsAtMost, rather than the finite stable-filtration predicate. It therefore does not prove the whole item. In contrast, FrobeniusModule.isMixedOfWeightsAtMost_of_forall_hasEigenvalue in lean/Sheaf/LinearAlgebra/FrobeniusPunctualBoundMixed.lean:82 has the exact filtration conclusion and a proof with no literal sorry; it is already recorded by the node's lean/reviewed_proof fields. Those records were retained unchanged. This is evidence for the mathematics, but is outside the explicitly permitted attachment directory. No compiler or axiom audit was run.

## WANTED

None. The blueprint proof and Mathlib constituents are locally available. No SGA source was used, and no downloads were made.

## Corrections and source comparison

The master blueprint statement (order 2788) and main-20261015 statement (order 3132) agree. The item is true with precisely its existing hypotheses; there is no statement dispute. Its doubled TeX command backslashes were normalized, without changing any object, hypothesis or conclusion.

The imported three-step proof mentioned an uncited Mathlib eigenvalue theorem, an uncited quotient dimension decrease, an uncited project quotient-eigenvalue theorem, and logarithm monotonicity. The replacement uses the existing eigenvalue-existence leaf, the existing exact-sequence spectrum statement, and two searched Mathlib leaves. It does not invoke the different upstream HasWeightsAtMost predicate as if it were mixedness.

I retained the eigenline/quotient dimension induction below the unit level. This spells out a finite stable filtration rather than assuming Jordan–Holder; the blueprint's spectrum inheritance, real weights, and extension assembly are preserved. The chapter and unit records were read and are not changed. This item is not the unit's key node, so its realized fields are not edited.

## Not duplicates

DAG searches covered the full statements, finrank_quotient_add_finrank, rpow_logb, logb_le_iff_le_rpow, dimension/quotient and logarithm concepts. Whole-blueprint searches covered eigenvalue, triangular, quotient dimension, finrank, logarithm, logb and mixed of weights at most. Lean source searches covered the item tag, both candidate declaration names, and the new leaves' declaration names.

lem-a1-quotient-dimension vs lem-weil-pbc-invariant-flag-categorical-filtration: the latter assumes a complete invariant flag for a finite-field group representation and realizes categorical cokernels; it does not state the dimension formula for an arbitrary field and subspace. Its proof mentioning rank-nullity is not an interface that supplies rank-nullity.

lem-a1-quotient-dimension vs lem-weil-pbc-pth-root-residue-dimension-balance: the latter equates kernel and cokernel dimensions of a specified differential comparison for p-root algebras, not dimension of any vector-space quotient.

lem-a1-quotient-dimension vs lem-weil-pbc-condensed-field-presentation-corank: the latter is an overlap invariance of presentation coranks for condensed modules, not the generic dimension identity.

lem-a1-real-logarithm-power vs def-weil-real-power: the definition supplies the meaning of real powers; it does not state their inverse and order comparison with logarithms. The p-adic/formal logarithm nodes concern different objects. No existing node has either of the new leaves as its statement or Mathlib match. Neither new node restates this item's mixedness conclusion, and neither is a sheaf lemma needing a Stacks tag.

## Review by Q118

I read the item and proof in both blueprint snapshots, the chapter and unit statements and steps, and the live source declarations in Exact.lean and FrobeniusPunctualBoundMixed.lean. For the new dimension node I read RankNullity.lean:248–252 and the field instance DivisionRing.hasRankNullity at DivisionRing.lean:62. Its conclusion is exactly dim(V/S)+dim S=dim V; the field case is a direct specialization. For the logarithm node I read Base.lean around the definition of logb, its positive-base/nonunit hypotheses and rpow_logb, and the OneLtB hypotheses of logb_le_iff_le_rpow. The first clause needs a positive base different from one, both supplied by b>1; the second needs b>1 and x>0, both explicitly present. The two clauses have their own declaration names and verified lines. Searches were run only through msearch.py, and the rate-limited LeanSearch for the item is recorded as unavailable, not as absence. The item's second semantic phrasing produced generalized-eigenspace stabilization lemmas, which do not state a weight filtration. The two new nodes have exact Mathlib matches, not conjectural candidates.

For step 1 I read the entire definition def-weil-frobenius-module-weights, including its permission of m=0. The zero vector space has the required empty filtration. The induction claim explicitly quantifies over all modules of smaller dimension with the same coefficient data, not just over an unspecified quotient.

For step 2 I read the statement of lem-zl-alg-closed-endomorphism-eigenvalue: it assumes a nonzero finite-dimensional space over an algebraically closed field and returns a nonzero eigenvector. Those hypotheses follow here from n>0 and Qlb being an algebraic closure. I checked alpha is nonzero by injectivity of F. Both directions of F(L)=L are written using scalar alpha and its inverse, so F really induces an automorphism, not just an endomorphism, on the quotient. I read def-weil-pbc-quotient-module: its surjectivity and kernel clause supplies exactly the short exactness used. The inclusion and projection commute with F on actual vectors/cosets.

For step 3 the map c to cv proves that L is a line because v is nonzero. Quotient finiteness is checked directly by taking images of a finite spanning set. The new dimension statement is applied to a genuine subspace of the finite-dimensional field vector space; it gives dim C+1=n and strict decrease, including the case L=V.

For step 4 I read lem-a1-spectrum-exact-sequence's entire statement, not its proof. It asserts the multiset union for an equivariant short exact sequence of finite Frobenius modules, exactly the sequence constructed in step 2. It is stronger than the needed inclusion. Since its spectrum is in iota-images, I explicitly used injectivity of iota to recover the original eigenvalue bound. Induction is therefore applied only to a strictly smaller finite Frobenius module with every required hypothesis verified.

For step 5 the new logarithm node is used with q>1 and r=|iota(alpha)|>0. The input bound yields log_q(r)<=w/2, while the inverse identity gives q^(t/2)=r for t=2 log_q(r). Multiplication by positive 2 proves t<=w even for negative weights. No integrality, algebraicity over Q, or root-of-unity assumption is silently used.

For step 6 the cited definition says exactly that purity tests every eigenvalue and that a finite stable filtration of pure quotients gives mixedness. The scalar-action calculation forces every eigenvalue on the line to equal alpha. The single quotient L/0 is identified with L by a map explicitly checked to intertwine F. This is a few-line use of the definition, not a new lemma about transport hidden behind a word.

For step 7 I read lem-a1-extension-bounds: its conclusion is mixedness of the middle Frobenius module if both ends of an exact sequence are mixed with the same upper bound. This is precisely what steps 4 and 6 established, and the exactness/equivariance were established before the invocation. This lemma is inside the same unit; the spectrum lemma's unit is in the current unit's cited route, and the eigenvalue leaf and definitions are generic tools. No undeclared off-route theorem or circular downstream mixed-subquotient lemma is used.

I tested V=0; a scalar nonzero one-dimensional module, including modulus below one and negative w; a Jordan block with a repeated eigenvalue (the quotient remains a Frobenius module and no semisimplicity is assumed); and a diagonal module with different eigenvalue moduli, where the two real weights need not be equal. An eigenvalue zero is excluded exactly by invertibility. The auxiliary dimension identity works for S=0 and S=V. The logarithm statements exclude x=0 and b=1 explicitly and work for x=1 and 0<x<1. The new statements introduce all objects and have no proof sketches, while the item's elementary steps contain their actual short arguments. Every cited statement was opened and matched to its use; citations.json copies the statements verbatim. All seven steps are below 2000 characters. I checked delivery-errors B–E for self-contained statements, TeX, precise Mathlib matches, duplicate avoidance, no clause-restatement nodes, no circular induction, and no hidden hypothesis or unsupported identification.

## Unfinished work

No mathematical gap remains in this one-level split. The two new nodes are Mathlib leaves and have no further proof obligations. Server dry run and direct push are the remaining delivery checks.
