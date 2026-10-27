# Stage-1 report: lem-sfb-normalization-jet-codimension

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-normalization-jet-codimension.json: statement split into five steps; not a Mathlib leaf.
- citations.json: thirteen step/node records, checked against the complete live statements.
- report.md: this report. searches.jsonl is the search tool's original log. prepare.py is sandbox-only preparation code.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searches of lean/WeilConjectures/ for the exact blueprint tag, normalization jets, codimension, and the curve Riemann–Roch declarations found no declaration giving all clauses of this estimate. Existing curve Riemann–Roch is supporting material, not an attachment of this node.

## WANTED

WANTED: Ian Morrison, GIT Constructions of Moduli Spaces of Stable Curves and Maps, arXiv:0810.2340, Section 3.2, Theorem 8 step (4), printed pp.14–15, for lem-sfb-normalization-jet-codimension. No local PDF exists in literature/. I read the source online at https://arxiv.org/pdf/0810.2340; I did not download or write it into the repository. The simultaneous-jet estimate is an agent extension, not a theorem stated verbatim in Morrison.

## Corrections and scope

The mathematical statement is unchanged. No statement dispute arose. Removed no imported fields. The inherited blueprint.from.node is null (the ancestor command confirms this); retained the inherited place and via chain and searched the current whole blueprint for Riemann, normalization, sections, jet codimension, and section-degree-cap. The present source blueprint's direct-images proof (3) does not state a standalone jet lemma. Its unit route is untouched.

The proof avoids any asymptotic threshold: C = delta + sum of the genera of the normalized components works for every m >= 1. Here delta is the dimension of the normalization quotient's sections. I did not use the existing projective-curve-normalization-section-defect node, which assumes connectedness and only gives eventual estimates. Its statement is insufficient for the all-m assertion without extra treatment. The existing smooth-curve-section-degree-cap node, found by the Stacks 0CCS/DAG search, gives exactly the arbitrary-divisor upper bound needed, including the zero divisor, so no duplicate was created.

## Unfinished work

None for this stage-1 split. No Lean was written or compiled, and no compiler/Lake/build tool was run. Only the required server dry run and delivery are pending when this report is first written.

## Not duplicates

No new nodes. The existing general section cap is cited rather than restated, as are normalization geometry and the finite-support twisting lemma. The only delivered node is the assigned item.

## Review by Q120

I read the complete worker brief and delivery-errors B–E, the stage-1 contract, GOAL.md, SETUP's three blueprint levels, the chapter and unit records, and the latest direct-images blueprint proof and unit. I read Morrison's actual Theorem 8 step (4), including the normalization pullback and the vanishing-order dimension estimate on printed pp.14–15. The estimate there is contextual and asymptotic; the delivered proof supplies a precise uniform simultaneous-jet version using available general tools. I read Stacks varieties.tex lemma-prepare-delta-invariant (0C1R), especially its structure-sheaf injection and finite singular support; lemma-chi-tensor-finite (0AYT), especially unchanged Euler characteristic under an invertible twist; curves.tex lemma-grd-inequalities (0CCS), with the nonzero-section exact sequence proving r <= d; and lemma-rr (0BS6) for the relation with the source's Riemann–Roch language. I also read varieties.tex lemma-degree-tensor-product (0AYX). No SGA source is used.

Step 1: I opened every cited node and checked its statement. Projective-proper gives properness of the embedded D. Reduced-curve-normalization-genus explicitly allows disconnected proper reduced pure-dimensional curves, supplies finiteness and smooth proper connected normalized components. Normalization-singular-skyscraper applies to D because proper schemes are finite type, and gives the coherent exact sequence and finite singular support, not just a definition of normalization. Chi-zero-dim-support supplies finite dimension and identifies it with chi. No connectedness or nodality of D is introduced.

Step 2: I checked the line twist and projection identification directly on a trivializing open; the identifications glue because they have identical transition units. This is a two-line local calculation, not an appeal to an unrecorded projection theorem. The cohomology node explicitly states the long exact sequence, hence its initial exactness supplies the cokernel injection. The finite-support lemma states BOTH h0 = chi and invariance of chi under line twists, so it really gives the uniform delta bound. Sections of a finite coproduct are tuples by the sheaf gluing axiom. These facts do not depend on m or any prescribed jet order.

Step 3: I checked the hypotheses of global-functions (proper smooth connected over algebraically closed k), proper coherent finiteness, and noetherian vanishing above dimension one. Smooth-connected-curve-local-rings explicitly gives Noetherian integrality, so the vanishing hypothesis is met. I use the Euler-characteristic definition of degree, not an unproved identification of two degree conventions. Curve-degree-tensor-additive applies to each proper dimension-one C_i, giving degree m e_i by finite iteration. Then chi = h0-h1 and nonnegativity of h1 give the lower bound. This avoids citing the divisor-degree Riemann–Roch node for a different degree convention.

Step 4: I read the entire statement of smooth-curve-section-degree-cap. Taking its q=1 and B_i=sum n_q[q] is a direct specialization: it states both the identification of the vanishing subspace and its h0 bound, using precisely the Euler-characteristic degree of this item. The hypothesis N_i <= m e_i makes its maximum equal to m e_i-N_i+1. All multiplicities are nonnegative, every S_i has distinct closed points, and zero multiplicities or empty S_i are explicitly permitted. Thus no jet-evaluation-surjectivity claim is hidden here.

Step 5: I recomputed the intersection and subtraction. Injectivity identifies U with the intersection of the normalization image with the direct sum of the vanishing spaces. Its dimension is at most that direct sum's dimension. Subtracting gives sum N_i-delta-sum g_i. The constant is a nonnegative integer, so is also an allowed real constant. This is elementary finite-dimensional subspace arithmetic, and there is no new linear-algebra node to create.

Small cases: on a rational normal smooth curve delta=g=0, the result becomes the exact rank N of jets up to the degree bound; for all orders zero the bound is 0 >= -C; at N_i=m e_i the section cap still gives at most one dimension, even for a nontrivial degree-zero twist. At a node the two branches may lie over the same point; the argument estimates an intersection inside the direct sum rather than treating their jets as independent downstairs. For a cusp delta>0 absorbs descent conditions. Disconnected D merely replaces single curve spaces by finite direct sums. No normalization fiber is assumed injective on points. In characteristic p the argument uses neither derivatives nor separability of a function, so the same reasoning applies.

I checked C1/C4 by reading statements, not proofs, for all thirteen citations. Every non-elementary assertion is covered by its cited statement; only the explicitly written local line-trivialization calculation and final dimension subtraction are marked elementary. Every step has fewer than 2000 characters. There are no new statements to audit for B1–B9 or D1–D2; all new-node alternatives were rejected in favor of existing statements. The Mathlib search command actually ran LeanFinder, LeanSearch, Loogle, and grep, with second formulations; searches.jsonl retains the unmodified output digests. Returned results concern polynomial degrees, power-series ideal ranks, or relative normalization, not this estimate, so none is recorded as a leaf.

Off-unit generic tool uses are declared in split_report.tool_uses for review. They supply normalization/cohomology/degree facts for this supporting estimate and do not replace any step of the six-functor unit route. No inherited maintainer field was edited.

Dry-run repair: the first citation check requested longer quotations for global-functions, noetherian vanishing, and smooth-curve local rings. Replaced those three short excerpts with the complete statements; the mathematical citations and proof are unchanged.
