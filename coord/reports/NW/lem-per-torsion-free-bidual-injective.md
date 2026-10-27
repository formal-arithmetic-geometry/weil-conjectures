# Stage-1 report: lem-per-torsion-free-bidual-injective

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-torsion-free-bidual-injective.json — item, statement, split into three steps; no Mathlib match. Statement unchanged; inherited citations, searches and blueprint lineage retained.
- dag/nodes/sec-deligne-laumon-a1/lem-per-finite-torsion-free-free-embedding.json — new statement-only node, unsplit, no Mathlib match: a finite torsion-free module over any commutative domain admits an injective linear map into some R^r. Source: Stacks Tag 0AUU, more-algebra-lemma-finite-torsion-free-submodule-free.
- citations.json — step 2's quotation from the new node, checked verbatim.
- searches.jsonl — actual searches recorded by msearch.py. Six searches concern the new embedding node; four concern the item. The item's older search records remain historical records and are not represented as searches by NW.
- report.md — this report and self-review.

One new node, zero Mathlib leaves. No Lean files, compilers, Lake, repository writes or git commands were used.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint id and for torsion freeness, biduals and evaluation injectivity. The project has finite locally free sheaf biduality and various unrelated evaluation lemmas, but no declaration stating this finite-module equivalence over an arbitrary domain. Mathlib declarations are considered below rather than attached as project proofs.

## WANTED

None. All mathematical source passages used are present in literature/stacks-project/more-algebra.tex and the tag-label map in literature/stacks-project/tags/tags.

## Problems found and changes

The item was statement-only, not a completed proof. Its statement is correct as written and agrees with Stacks 0AV0(3); no hypothesis or conclusion was changed. There is no released repair note and no previous split/report in this sandbox.

The proof supplied here adapts the coordinate-map argument of 0AV0(3), using the independently stated finite-free embedding theorem 0AUU. Accordingly proof_origin.by is agent, with the exact local source passages identified. The only non-elementary input is the embedding; the remaining domain cancellation and tests against coordinate functionals are written explicitly. No Noetherian, finite-presentation, freeness of T, or PID hypothesis is introduced. In particular the nonprincipal ideal (x,y) in k[x,y] is allowed.

The latest blueprint ancestor proof is literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md, Step 3. I also read the latest chapter and unit texts and the DAG chapter/unit records. The imported unit text is older than the latest blueprint; the inherited regular-pair/flat-reflexivity chain is historical refinement under its duality direction. I retain that chain exactly rather than claiming that the current geometric ancestor explicitly cites 0AV0 or 0AUU. The item's immediate parent uses this result to prove the saturated reflexive embedding criterion; the new child supplies a plain finite-free embedding, without asserting reflexivity or torsion-free cokernel. No chapter or unit records were changed.

## Searches and Mathlib verdicts

Before creating the new node I searched the whole DAG by Tag 0AUU, its label lemma-finite-torsion-free-submodule-free, and the phrases submodule of a finite free module, torsion-free embedding and finite free. I also inspected statement/title matches for torsion-free finite-free modules. Whole-blueprint searches used tools/blueprint_refs.py search with torsion free, submodule free, 0AUU, finite torsion, and embedding. For the item I also searched bidual and double dual. No node states the new embedding theorem or the item's equivalence. The existing reflexive-saturated embedding node depends on this item, and cannot be used without a cycle. Its stronger Noetherian/reflexivity hypotheses do not apply to an arbitrary torsion-free module.

For the new node the logged semantic searches are the two distinct phrasings beginning 'A finitely generated torsion free module...' and 'A finite module over a domain is isomorphic...'; the Loogle query is Module.Finite, Module.IsTorsionFree, the LeanSearch query begins 'Every finitely generated torsion free module...', and the two greps search RingTheory/Localization and LinearAlgebra/FreeModule. The JSON entries reproduce the exact query text, logged summaries and verdicts.

I read the candidates in the pinned source: Mathlib/LinearAlgebra/FreeModule/PID.lean:329-404 gives bases/freeness with an IsPrincipalIdealRing hypothesis, which an arbitrary domain does not satisfy. Module.Finite.of_injective transfers finite generation and does not construct an embedding. Mathlib/RingTheory/Localization/Free.lean:78-94 produces freeness after localization under finite presentation, not an embedding into a finite free module over R. Thus no candidate is exact or specializes in one line. The second phrasing likewise returned PID freeness and rank/torsion lemmas, not 0AUU.

For the item the new logged LeanFinder, Loogle, LeanSearch and grep searches agree with the inherited searches. I read Mathlib/LinearAlgebra/Dual/Lemmas.lean:160-182 and Dual/Basis.lean:174-180: eval_apply_injective assumes Projective, while Basis.eval_injective assumes a basis. Dual/Defs.lean:205-221 assumes reflexivity for bijectivity. Neither finiteness nor torsion freeness over a general domain implies these stronger hypotheses. Thus the item is not a Mathlib leaf either.

## Not duplicates

No existing node has source Tag 0AUU or states its finite-free embedding conclusion under the same or weaker hypotheses. The same-tag duplicate checklist is empty.

lem-per-finite-torsion-free-free-embedding vs lem-per-reflexive-saturated-free-embedding: the new node assumes only a commutative domain and a finite torsion-free module and produces a plain injective map; the existing node characterizes reflexivity over a Noetherian domain by an embedding with torsion-free cokernel and depends on the present item.

lem-per-finite-torsion-free-free-embedding vs lem-sc-dvr-fg-torsionfree-free: the existing node assumes a DVR and concludes the module itself is free; this does not cover arbitrary domains, and the new node asserts only embeddability.

lem-per-finite-torsion-free-free-embedding vs lem-per-torsion-free-bidual-injective: the new node constructs an embedding into a finite coordinate module, with no mention of duals or evaluation. The item's step 3 still proves the evaluation assertion by explicitly composing coordinate functionals with that embedding. It does not merely apply a restatement of its own conclusion.

## Review by NW

I read the item in Stacks Tag 0AV0, more-algebra-lemma-reflexive-torsion-free, especially the construction and coordinate map in its proof and the final paragraph for clause (3), at more-algebra.tex:5162-5214. For the new child I read Tag 0AUU, more-algebra-lemma-finite-torsion-free-submodule-free, at lines 4863-4884 and confirmed both tag-label assignments. The child's existence assertion is exactly the forward implication of 0AUU, with submodule rewritten as an injective linear map into R^r. It has no proof sketch or proof dependencies. Its statement spells out torsion freeness and the coordinate module, and cites the existing definition of finite generation; I read that definition to verify that 'finite' means finitely generated, not a finite underlying set.

Step 1 cites no node and uses only the definitions already in the item: if at=0 and a is nonzero, every functional has a phi(t)=0 in the integral domain R, so all phi(t) vanish and injectivity of evaluation gives t=0. This proves the reverse implication with no finiteness used. I checked that this uses cancellation in R, not an unproved assertion that T is torsion free.

Step 2 cites exactly lem-per-finite-torsion-free-free-embedding. I reread its complete statement: it supplies the integer r and injective R-linear map i that the step takes from it. All three hypotheses are available: R is a commutative integral domain, T is finitely generated by the item's hypothesis, and T is torsion free in this direction. The quotation in citations.json is a literal substring of that statement. There are no other proof citations to misquote and no off-unit generic tool uses: the child inherits the item's own unit.

Step 3 cites no additional theorem. Each coordinate projection composed with i is a linear functional, directly by coordinatewise addition and scalar multiplication. Equality of evaluations therefore implies equality of every coordinate of i(t) and i(u), and injectivity of i gives t=u. I wrote the formulas rather than invoking an unexplained naturality or dual-identification theorem. The empty-coordinate case r=0 works because there is only one element of R^0. This is a short elementary consequence of the preceding embedding and the evaluation formula, not another independent lemma.

I tested the item and child on the zero module, a field as base ring, Z/n for n>1, and the finite torsion-free nonfree ideal (x,y) over k[x,y]. The zero module permits r=0. For Z/n the dual to Z is zero, so evaluation is not injective and the module is not torsion free; the child does not apply. For the ideal (x,y), inclusion into R gives the child's embedding although the ideal is not free, and its inclusion functional detects each nonzero element. The domain restriction is used exactly where a phi(t)=0 is cancelled. No claim is made for rings with zero divisors or non-finitely-generated modules.

Against delivery-errors B through E, I checked self-contained statements, single TeX escaping, exact tag-label sources, real search logs and source readings, and the absence of proof text in the unsplit child. I checked that no elementary coordinate observation became a node, no parent conclusion was moved wholesale to a child, and no theorem is hidden behind a definition citation. The proof dependency union is precisely the single child, which depends only on the finite-generation definition, so there is no cycle. All proof steps are below 2000 characters; no long-step lemma is hidden. No SGA source is used. The checks required no mathematical correction to the item's statement.

## Unfinished work

The one new statement-only node is intentionally unsplit, as required by a one-level stage-1 split. No part of the item's natural-language proof is left unfinished. Delivery-check results are recorded below after running the required server-side dry run.

## Delivery checks

The required deliver.py --no-push invocation exited 0 and printed OK (not pushed), commit 2338022d707, with server preflight passed. The separate server-side check_dag invocation also exited 0: no finding introduced by the sandbox or on its nodes. The dry run includes review_split. No local compiler or local DAG-check execution was used.
