# Worker report: lem-sfb-finite-module-fibre-product-patching

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-module-fibre-product-patching.json`: existing statement, now split into four complete steps; no matching Mathlib patching declaration found.
- `citations.json`: five step/node citations, each quote copied verbatim from the cited statement.
- `report.md` and the search command's `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. The item's statement and statement dependencies are unchanged. No Lean, compiler, Lake, repository writes or direct git commands were used.

## Attachments

None. Read-only searches under `lean/WeilConjectures/` for the exact blueprint tag, finite-module/fibre-product terminology and Milnor/patching found no complete declaration of this item. The older source checkout also gave no exact-tag or source-label hit. Unrelated coherent-ideal patching and inverse-limit Milnor sequences do not assert this ring-pullback theorem.

## WANTED

None. The item and all cited input statements have local sources.

## Problems found and changes made

The imported item is correct: it is Stacks 0D2H, label `lemma-finite-module-over-fibre-product`, in Situation 08KH, in `literature/stacks-project/more-algebra.tex:775–806`. Its unrestricted surjection hypothesis is essential to the two lifting arguments; neither an ideal finiteness hypothesis nor Nakayama's lemma is needed. The old node had no proof. I supplied the actual generator argument rather than creating a node that restates finite patching.

The existing lemma `lem-sfb-patched-module-base-change` states the second canonical isomorphism needed by the source. Its statement, rather than observations in its proof, is used. This is important because the projection from the patched module to M' need not be surjective. The proof only uses that its image generates M'.

The inherited `blueprint.from.node` is null, and `tools/blueprint_refs.py ancestor` confirms null. The precise inherited supporting-input place and via chain were retained. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/_section.md`, the current `sk-thm-sf-ctf-stability/_section.md`, and `sk-thm-sf-ctf-stability-direct-images.proof.md`. The latest direct-image proof states its proper/open/compactification assembly, without restating the historical alteration chain written in the inherited provenance. This delivery concerns its already-existing auxiliary commutative-algebra node; it changes no unit or chapter route or realization fields. The DAG unit record remains older text and has a different chapter assignment; no unauthorized edits were made to it.

Whole-DAG searches covered 0D2H, 07RU, `lemma-module-over-fibre-product`, finite module/fibre product, and Milnor/patching. Whole-blueprint searches used `blueprint_refs.py search` with `fibre product`, `finite module`, `0D2H`, and `patch`; none states this theorem. The finite-projective patching node has additional projectivity hypotheses and an equivalence conclusion; it does not cover arbitrary finite modules. The flat-patching node has a different hypothesis and conclusion. The canonical base-change node was reused.

I ran the required msearch command with two distinct LeanFinder phrasings, Loogle, LeanSearch and source grep, then read their hits. The actual logged results are appended without altering the inherited searches. LeanSearch's finite-limit suggestions were checked in `Mathlib/Algebra/Category/FGModuleCat/Limits.lean`: line 45 introduces `IsNoetherianRing k` before the limit construction. They concern a single fixed base ring, whereas M' need not be finite over R. `Module.Finite.of_exact` would require finiteness of the kernel, not assumed here. Scalar extension, transitivity, localization and finite-type results returned by LeanFinder are not this theorem. No service in these new searches was unavailable.

## Unfinished work

None for this one-level stage-1 split. Its existing dependency on the canonical base-change theorem is explicit. Validation and delivery are performed by the prescribed remote delivery command.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to compare.

## Review by NX

I read Stacks 0D2H and its proof in full, the Situation 08KH defining square, and 07RU (`lemma-module-over-fibre-product`), especially its final assertion and proof observations (1)–(13). I checked that the item's maps, quotient M'/IM', and coordinatewise action are exactly those of that situation, with R in place of the source's B'. I also read the statements of both cited definition nodes: `def-weil-finitely-generated-module` explicitly gives finite linear-combination generators, and `def-weil-pbc-module-tensor-product` explicitly says pure tensors generate. There are no new statements needing an additional source.

Step 1 cites the finite-generation definition solely to choose the two finite lists. The two surjectivity claims are proved by element lifts, using only the surjection A'→A and the defining quotient map M'→M'/IM'. No tensor exactness or flatness is assumed.

Step 2 cites the statement of `lem-sfb-patched-module-base-change`, not its proof: it gives the canonical map P⊗_R A'→M', with the exact formula used, as an isomorphism without extra hypotheses. Its ring maps, modules and isomorphism are literally the item's data. Pure-tensor generation in the tensor definition then writes each of the finitely many inverse images of x_i as a finite sum. Taking the union of their first factors is an elementary finite-list operation, and mapping those sums through the canonical isomorphism gives the needed A'-generating list of images. This is the only step invoking a non-elementary theorem, and it is marked non-elementary.

Step 3 cites no theorem. Subtracting the lifted generators kills the first coordinate, and the defining compatibility of a pair in P then puts its second coordinate in IM'. I wrote out the ideal-module expansion and coefficient regrouping: t_j=Σ_k i_k a'_{kj} is in I. Thus this step does not hide an unproved finiteness assertion about I or its product with M'.

Step 4 explicitly constructs s_j=(0,t_j). Membership in R follows from t_j∈ker(q); coordinatewise multiplication gives the exact residual vector. Together with the first list this writes every element as a finite R-linear combination. The cited finite-generation definition says exactly that this proves the conclusion. These coordinate calculations, unlike the base-change input, are marked elementary. All steps are under 700 characters and there is no long-step hidden-lemma issue.

For the edge cases I checked I=0 (then R≅B and P≅N), B=A (then R≅A' and P≅M'), and A=0 (then R=B×A' and P=N×M'). Zero modules give empty generating lists where appropriate, and the sums in the proof are still valid. To test the absence of a kernel finiteness condition, take A'=k[x_1,x_2,…], I=(x_1,x_2,…), A=B=k, N=k and M'=A'; then P≅A' is cyclic despite I not being finitely generated. To test the absence of nilpotence, take A'=Z, A=B=F_2 and I=(2): P≅M' again, and the coefficient lift is (0,2a), requiring no nilpotence. To test the non-surjective projection caution in step 2, let A'=A=k(t), B=k[t], I=0, N=B, M'=A; then P=B and P→M' is only the inclusion k[t]→k(t), whose image still generates over A'.

I checked delivery-errors B–E against these files: no new-node relabeling or disguised clause; unchanged self-contained statement and single TeX escapes; source tags and labels verified in `stacks-project/tags/tags`; every non-elementary fact has a statement citation; no citation of a node's internal proof; all citation quotes are literal substrings, not paraphrases; proof_deps is exactly the union of uses; the theorem input is in the same unit, while the two other inputs are definitions. There is no added route edge, no SGA source, and no dependence on the finite-module item in its base-change input. The corrections during writing were to remove ambiguous ring/module quotient notation from the generator choice and explicitly explain the ideal coefficient regrouping and the fact that P→M' need not be onto.
