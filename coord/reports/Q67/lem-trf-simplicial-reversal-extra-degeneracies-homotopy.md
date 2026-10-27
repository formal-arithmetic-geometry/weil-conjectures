# Stage-1 delivery: lem-trf-simplicial-reversal-extra-degeneracies-homotopy

## Files written

- dag/nodes/sec-trace-formula/lem-trf-simplicial-reversal-extra-degeneracies-homotopy.json: existing statement, now split in nine elementary calculation steps; complete-item Mathlib verdict: no match.
- citations.json: a literal statement quotation for each step/node pair.
- report.md: this signed review. searches.jsonl contains the search command's actual records.

No new nodes and no new Mathlib leaves. The two existing dependencies are Mathlib leaves. No Lean, compiler, Lake, repository write, or worker git command was used.

## Attachments

None. Searched WeilConjectures/ for the exact blueprint tag and for simplicial reversal, extra degeneracy and homotopy with opFunctor. The project has Cech extra-degeneracy applications, not this arbitrary-category reversal theorem. Mathlib declarations cannot serve as project attachments.

## WANTED

None. The source for the application is available. The explicit reversal argument is agent-written and marked as such; no unavailable document is presented as having been read.

## Corrections and source scope

The original statement is retained, including all index ranges and naturality/evaluation clauses. No STATEMENT-DISPUTED issue was found. The original node had no proof. I supplied the calculations rather than transferring the same clauses into new nodes.

Read Stacks simplicial.tex, Situation 08N9 (situation-adjoint-functors), Tag 08NC (lemma-standard-simplicial), and Tag 08ND (lemma-standard-simplicial-homotopy), especially its second homotopy equivalence. Stacks proves the standard-adjunction application by Godement two-map homotopies; it does not explicitly state the reversal calculation in this item. The proof_origin is therefore agent, not document. Read the two cited node statements in full, and Mathlib/AlgebraicTopology/SimplexCategory/Rev.lean, SimplicialObject/Op.lean, SimplicialObject/Homotopy.lean:48-67, and ExtraDegeneracy.lean:72-83 to verify conventions.

Read the chapter/unit records and current literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/_section.md and lem-trf-local-term-locality.proof.md. The current locality proof uses Varshavsky, and is different from this auxiliary node's historical ancestry. This delivery makes no change to that chapter/unit route or the upstream statements. It handles only the generic reversal calculation already called by lem-trf-adjunction-standard-simplicial-homotopy. The item is not the key node of sk-i-curve-zero; its realization record is not mine to edit.

## Searches and duplicate audit

Preserved all original searches and added the six actually logged searches of 2026-10-23. Read the displayed hits. LeanFinder's first phrasing found SimplicialObject.opFunctor, opFunctor_obj_δ, opFunctor_obj_σ, opEquivalence and SimplexCategory.rev. LeanSearch found the same object-level reversal and unrelated short-complex homotopies. The first Loogle pattern used an unqualified identifier absent from its index; this was recorded as an invalid query, not mathematical absence. The corrected quoted-name Loogle query found only prevD chain/cochain lemmas. The second LeanFinder phrasing found truncated Kan path homotopies and chain/short-complex symmetry, not combinatorial simplicial homotopy reversal. The grep found Homotopy and Op sources, which were opened. Mathlib covers the ordinal/object operators, but no hit covers all clauses of the item.

Searched the whole DAG by ordinal reversal, SimplexCategory.rev, opFunctor, reverse homotopy, and Tags 08ND/08NC; ran blueprint_refs.py search for simplicial reversal, extra degeneracy, ordinal, reversal, and simplicial homotopy. The nearest existing candidate lem-coef-simplicial-opposite-homotopy-calculus concerns simplicial sets, Joyal mapping objects and horns. Its statement has neither extra-degeneracy data in an arbitrary category nor this H-index endpoint formula. The existing prism leaf supplies precisely the extra-degeneracy and homotopy conventions, and was reused. No fact needed a new node: every remaining argument is a substitution in definitions or in the supplied equations, displayed explicitly.

## Review by Q67

I checked B--E of delivery-errors.md against the written JSON and sources. B: the statement is self-contained with the two existing notion/convention dependencies; no unsplit node hides proof text, no new node lacks a source/search/blueprint link, and the JSON uses ordinary single TeX backslashes after decoding. The item's blueprint.from is retained with its precise auxiliary place and same_as is empty following the global searches. C: I read both cited statements and made the literal quotation ledger; no proof of a cited node is used. D: the steps carry the actual argument, not applications of renamed clauses. E: I checked the following degree and hypothesis details directly.

Step 1 uses only def-weil-pbc-simplicial-object, whose statement defines simplicial objects as functors and their morphisms as natural transformations. Monotonicity, composition, identity and double reversal are computed explicitly. No limit, smallness, additive, tensor or model-category hypothesis is needed.

Step 2 uses that same definition's omission/repetition formulas. The source degree of d_i is n, so the reversed face index is n-i; the source degree of s_i is n, so its reversed index is n-i too. The constant functor and q_n are fixed by their definitions, not by an uncited theorem.

Step 3 uses the displayed left-extra-degeneracy equations in the prism node's statement. The augmentation and exceptional degree-zero equations match literally. On t_{n+1}'s target the degree is n+2, and on its source n+1, so k=n+1-i gives exactly both faces. The hypothesis bounds 0<=i<=n+1 ensure 0<=k<=n+1, including both endpoints.

Step 4 uses the prism node's displayed degeneracy equation. The target/source degrees are n+1 and n, and k=n-i is in 0..n. The original right-data equation at k becomes the left-data equation at i. The prism node assumes no further self-extra-degeneracy relation, and none was added.

Step 5 uses the simplicial-object definition for the arbitrary section's naturality, applied at r(alpha); involution returns alpha, and the section equalities are degreewise unchanged. The prism node's statement explicitly supplies a_n=Z(q_n)h_{-1}, which is exactly the only special-section formula used here.

Step 6 uses the prism node's two endpoint identities. Since H lands in degree n+1, d_0 is D_{n+1} and d_{n+1} is D_0. Thus the new first endpoint is f and the new last endpoint g, correctly making the homotopy run from g to f. At n=0 the sole H_0 has these two endpoints too.

Step 7 uses exactly the three face identities printed in the prism statement. For i<j the transformed index is greater than k+1, and for i>j+1 it is less than k. The right-hand face is an operator on A_n, hence reverses using n, not n-1. I also checked the middle equality at k-1 and its required k>=1. The strict inequalities prevent undefined negative homotopy indices; these strict cases never occur at n=0.

Step 8 uses precisely the two degeneracy identities in that statement. The transformed index is n+1-i. The cases i<=j and i>j switch the two original inequalities, and the homotopy indices become k and k+1 in degree n+1 respectively. The source operators reverse using n. This covers i=0 and i=n+1 as well as all interior indices.

Step 9 uses the natural-transformation definition from the simplicial-object node. It writes each required compatibility as an equality, then reindexes it; for the explicit section it writes the naturality square at q_n. Evaluation of a functor category acts on components and preserves composition/identity by definition, so no assertion about choosing homotopies pointwise is required.

The longest step is 879 characters, so none crosses the 2000-character long-step review threshold. All steps are elementary: they are explicit finite-index substitutions, inequalities, or functor/natural-transformation definitions; no non-elementary existence or comparison theorem is asserted without a node. Numerical checks of every homotopy index and boundary in degrees 0..20 passed. An exhaustive check of monotonicity, involution and composition for ordinals of sizes 1..5 (and composite codomain sizes 1..4) passed 30,459 compositions. An initial verification-script assertion used n-1 rather than n for the source face reversal; correcting that test to the actual source degree made it agree with the already correctly written proof. The calculations in the proof are general, and the finite check is only an edge-case check.

The server review_split preliminary check passed with zero new nodes. Its notice that sk-i-curve-zero has no realization yet is about an existing unit, outside this non-key item's scope. The final full dry run is required before direct push.

## Unfinished work

None in the split. This is stage 1 only, not a claim of a completed Lean proof.
