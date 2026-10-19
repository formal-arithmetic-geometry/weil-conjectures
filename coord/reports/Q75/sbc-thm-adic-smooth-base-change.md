# Q75: sbc-thm-adic-smooth-base-change

## Files written

- dag/nodes/sec-smooth-base-change/sbc-thm-adic-smooth-base-change.json: statement, split into eight steps; no Mathlib match.
- citations.json: verbatim statements for every proof-step citation.
- searches.jsonl: actual search-command results, including unavailable LeanSearch.

No new nodes and no Mathlib leaves. The sandbox initially contained only dispatcher brief markers, with no item, report, searches, or interrupted delivery. I copied the current repository item and retained its proof, existing reports in split_report, citations, historical Mathlib searches, source metadata, import flags, and Lean metadata. No Lean source was written or compiled. No repository git command was run.

## Attachments

None. Searched WeilConjectures in the slopmaster2 source for the exact blueprint tag, adic smooth base change, completed categories and exchange names. No declaration states this integral theorem. Read SmoothBaseChange.lean: its finite-coefficient theorem at line 181 is narrower and its comparison lemma still has sorry. It is not an attachment for this item. The upstream master Smooth.lean declarations are sorry and concern the distinct etale torsion targets.

## WANTED

None for this split. Sources already available suffice for the agent assembly. The existing coefficient-extension definition records its own missing local-field reference; this delivery uses its stated datum and assumes the quotient finiteness and perfectness explicitly.

## Statement and proof corrections

STATEMENT-DISPUTED (inherited correction, retained): both displayed endpoints are objects on X, not on S. The master and main-20261015 blueprint statements put the final Dbc landing on S, which is ill-typed: f has target S but f^* has target X, and h has target X. Retained the corrected X landing. The current Dbc definition also requires finite dimensionality of T and, for the conditional landing, X; these domain requirements are explicit in the existing item. No further statement change was made by Q75.

The source proof's reference to proper base change does not directly apply to the arbitrary qcqs g. The inherited proof correctly uses only its generic direct-image/limit and perfect-projection tools, followed by finite smooth exchange. I kept that distinction and removed step 2's obsolete discussion of hypothetical further reductions: the current finite theorem states its exact finite-ring assumptions unambiguously.

The completed coefficient sheaf is not identified with constant A. Finite operations are compared after restriction using the ring-sheaf adjunction comparison. The inverse of a restricted exchange is not lifted through a nonexistent fully faithful restriction functor: restriction merely reflects invertibility.

## Not duplicates

No new nodes were created. Blueprint search for adic smooth base change returns this item only. Additional whole-blueprint/DAG searches for compatible etale witnesses and normalization found definition nodes and other application proofs, not a separately stated witness-lifting theorem needed here.

## Review by Q75

I read coord/brief-stage1.md, stages/1-dag.md, the SETUP requirements and three levels, role and tools guidance, coord/delivery-errors.md B through E, GOAL.md, dag-sync.md, and the item's chapter and unit. The inherited sk-rem-rest unit is a roadmap without numbered proof steps. I read both the master paragraph and the current main-20261015 sk-thm-sbc-coefficients statement/proof: their finite-reduction route and their S/X error agree. The item's blueprint_update is absent; its ancestry and pointers are preserved.

For the item I checked Stacks proetale.tex lemma-naive-completion (099M), lemma-pushforward-Noetherian-case (099N), lemma-compare-constructible-derived (09AL), and the surrounding constructibility material including lemma-Noetherian-adic-constructible (09BX). I read the general proper-base-change reduction proof (09C9) only for its generic completion/projection/limit argument, not to invoke properness for g. I read sites-cohomology.tex lemma-pullback-K-flat (0G7E) and lemma-pullback-tensor-product (07A4). There is no SGA citation. No new node needs its own source review.

Step 1 uses the complete-category definition for completeness, the adic datum for the actual normalized reduction tower, and finite proetale modules for the meaning of bounded constructible etale origin. I opened these three statements: they give exactly those clauses. Reindexing P_m=A/I^m as A_{m-1} loses no level.

Step 2 uses the finite proetale smooth-base-change statement. I opened it and checked every assumption: finite commutative A_n, its additive group killed by its positive cardinal N, N invertible by the explicit item assumption, noetherian corners, smooth f, qcqs g, and the origin witness from step 1. The node asserts invertibility of the canonical ambient ringed exchange, without constructible output, exactly what the step uses.

Step 3 uses direct-image-limits for completeness of G and D, completed-pullback-reduction for completeness of E and B and their actual quotient reductions, perfect-projection-formula for arbitrary scheme maps and perfect quotient coefficients, ring-sheaf-change-adjunction for the restricted finite/integral operation comparisons, and profinite-coefficient-inverse-image for the coefficient isomorphisms and commuting projection squares. I opened all five statements. None requires properness for the clause invoked; K and E are complete when each complete-input comparison is applied. All comparisons remain in their specified ring-sheaf categories.

Step 4 uses completed-operations-linear-natural-exchange for the specific completed adjunction mate and its finite-reduction identification, and ring-sheaf-change-adjunction for reflection of isomorphisms. I read their statements, including the final finite-level-mate clause. The conjugacy equation for c_B and c_D identifies the actual map; it is not an inference from naturality alone. Step 5 uses the final assertion of levelwise-isomorphism-cones, which explicitly detects an isomorphism between complete objects from their reductions. Both endpoints are complete by step 3.

Step 6 uses constant-completion-equivalence only for its quotient-ring-sheaf identification, the adic datum for the canonical strict normalized towers, and normalized-constructible-local-effectivity for exactly the common finite stratification and bounded adic-lisse finite-type local models. I read these statements. The hypothesis is intrinsic constructibility in one common interval, supplied by the conditional assertion and the cohomology isomorphisms. The scalar linearity calculation uses local lifts along the quotient sheaf, not derived full faithfulness of restriction. Noetherian X is present; no Tor amplitude is added or presumed.

Step 7 uses finite-ring-constructible-derived-origin for each bounded origin and preservation/reflection of intervals, ringed-topoi-derived-tensor-pullback for K-flat tensor comparison, site-comparison-finite-level for exactness and the sheaf unit, adic-coefficient-datum for the normalization and cocycle, and site-comparison for bounded-below full faithfulness. I opened each statement. In particular A_n need not have finite Tor dimension over A_m: the argument proves the etale tensor bounded by exact inverse image and its sheaf unit before using D+ full faithfulness. Lifting both a map and its inverse proves the lifted map invertible. Applying the faithful functor proves the displayed cocycle and identity equations.

I specifically reviewed step 7, the sole non-elementary step longer than 2000 characters, under the 2026-10-17 instruction. It is one routine lifting argument under a fully faithful comparison, not an independent geometric comparison smuggled into prose. Its non-elementary tensor, origin and full-faithfulness inputs are all cited. The remaining cancellation and equality checks are written out; I made the iterated balancing formula explicit. Creating a node for precisely this local membership clause would only relabel the item's final argument. It is retained as one step for the independent reviewer to assess.

Step 8 uses the complete-category definition: I checked completeness, the uniform tower, compatible witnesses, finite-dimensional noetherian X and invertible ell individually. Fullness immediately carries the ambient map and inverse into the subcategory. The generic off-unit tools remain explicitly explained in split_report.tool_uses; none replaces the smooth finite-exchange route.

I tested n=0 against the datum's index 1, zero complexes, empty corners, identity squares and single-point schemes. There is no reduction modulo I^0, no nonzero-cohomology premise, no use of properness, and the proof treats empty schemes vacuously. The cardinal annihilation also holds for the zero ring. All cited nodes exist, and citations.json copies their actual statements verbatim. Existing Mathlib searches are retained as historical records and the new searches are appended with their actual results: algebraic smoothness and ordinary sheaf adjunctions are not matches; LeanSearch's rate-limit failure is unavailable.

## Unfinished work

No mathematical part is left out of the split. Downstream cited unsplit statements remain separate DAG work, as required by a one-level split. Delivery validation follows below.
