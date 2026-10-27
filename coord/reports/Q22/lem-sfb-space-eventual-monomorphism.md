# Stage-1 report: lem-sfb-space-eventual-monomorphism

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-eventual-monomorphism.json — unchanged statement; complete five-step split of Stacks 0828(4).
- dag/nodes/sec-six-functors-basics/lem-sfb-space-lft-diagonal-lfp.json — statement, unsplit; Stacks 084P, first assertion; no Mathlib match for algebraic spaces.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-closed-limit-stabilization.json — statement, unsplit; Stacks 0828(3); no Mathlib match for algebraic spaces.

Sandbox evidence: citations.json contains the verbatim statement used by each of the 11 step/node citation pairs. searches.jsonl records the actual commands; search-results.jsonl retains the complete returned hits. Neither evidence file is a new DAG node. There are two new nodes and zero Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures/ for the exact blueprint tag, algebraic-space terminology, eventual monomorphisms, and related inverse-limit/monomorphism declarations. No declaration supplies this theorem for algebraic spaces. Scheme-only results do not attach the item.

## WANTED

None. All cited sources are present under literature/stacks-project/.

## Corrections and scope

The imported item is correct: its hypotheses and conclusion agree with spaces-limits.tex, lemma-finite-type-eventually-closed, Stacks 0828(4). No statement correction or STATEMENT-DISPUTED is needed. The inherited proof was empty; it is now the kernel-pair proof of that clause. The source's non-elementary diagonal finiteness result and its earlier closed-system stabilization clause are exposed separately.

I read the chapter and unit records, the three levels in SETUP.md, and the current latest blueprint's sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md (proof (3)). This below-unit approximation prerequisite follows the ancestry already on the item; it changes neither the unit route nor the chapter. tools/blueprint_refs.py ancestor returns None for this inherited ancestry. I retained the null ancestor and the existing via list, and added the item at the front of each new node's via list. The source-specific from.place clauses identify exactly which auxiliary inputs of 0828(4) they serve. No unit realization fields are due: this item is not the unit statement.

## Not duplicates

lem-sfb-space-lft-diagonal-lfp vs lem-sfb-fp-etale-presentation-criterion: the existing 084P-citing node characterizes finite presentation over an affine scheme by a finitely presented etale scheme groupoid. It does not state local finite presentation of the relative diagonal of an arbitrary locally finite type space morphism, and it assumes substantially different data.

lem-sfb-space-closed-limit-stabilization vs lem-sfb-space-eventual-monomorphism: both cite 0828, but the new node is clause (3), about closed-immersion transitions with locally finitely presented limit; the item is clause (4), about eventual monicity of an arbitrary affine-transition system. The proof constructs the new closed system and verifies local finite presentation; the new node is not a reformulation of the item.

I searched the whole DAG by tags 084P, 03KN and 0828 and by diagonal/presentation, closed-limit and kernel-pair concepts, then opened the possible matches. The general diagonal-locally-finite-type and diagonal-scheme-test nodes assert only local finite type of every diagonal, which is weaker than the needed local finite presentation. The existing relative-lfp-permanence node is cancellation of a locally finitely presented composite against a locally finite type second map, not the diagonal theorem itself; the current split lacks an arbitrary-space local-finite-type base-change node that would make that cancellation a two-line proof. The existing space-qcqs-source-products node assumes its source factors quasi-separated, which the present A need not be, so I did not cite it for compactness. The 03KN-citing etale-atlas-distinct-tuple node treats affine etale atlases and distinct tuple loci, not this arbitrary-source kernel-pair system. No new 03KN node is created: the comparison is an elementary pullback calculation in Step 3. Whole-blueprint searches included monomorphism, finite presentation, locally of finite presentation, diagonal, closed immersion, closed subspaces, kernel pair, stabilization, and the three tags; none states either new algebraic-space theorem. Searches also found scheme-specific approximation nodes, whose object type excludes an attachment or duplication here.

## Review by Q22

I read spaces-limits.tex, lemma-finite-type-eventually-closed (0828), including the full proofs of (3) and (4), and spaces-morphisms.tex, lemma-diagonal-morphism-finite-type (084P), first assertion and proof. The new diagonal node keeps exactly the locally-finite-type hypothesis and concludes only local finite presentation; it does not add the quasi-separatedness required for the source's stronger second assertion. The new stabilization node introduces its own base, directed system, limit and finiteness hypotheses and states only 0828(3). It has no hidden proof or proof dependencies. Both nodes are statement-only, with definition references, source tags and labels, blueprint references and searches. I tested the diagonal assertion on the identity, empty source, and the non-finitely-presented quotient Spec(R/J) to Spec(R): the last is locally finite type and its diagonal is an isomorphism even though the original map need not be locally finitely presented. For stabilization, the constant system and an eventually empty system satisfy the conclusion; an infinite sequence of quotients killing successively more independent variables shows why the limit's local finite presentation hypothesis cannot be discarded.

Step 1 uses the statement of lem-trf-space-fibre-products-etale-covers for existence of R_i, lem-sfb-space-lft-cancellation for A to Z_0, and the new 084P node for delta_0. I opened all three. Cancellation explicitly permits arbitrary second arrow Z_0 to B. The diagonal is A to A times over Z_0 A, not a product over B.

Step 2 uses the exact first clause of lem-sfb-space-qcqs-permanence; I checked it requires A quasi-compact and Z_i quasi-separated but does not require A quasi-separated. That node uses point-space compactness, so lem-a1-space-etale-open-image supplies its explicit atlas/topology equivalence. lem-sfb-space-quasicompact-affine-tests states both arbitrary base-change stability and equivalence with testing all quasi-compact schemes. These justify p_2 quasi-compact and E quasi-compact. The fibre-product/etale-cover node supplies E to R_i. The scheme covering-composition node explicitly supplies the composite surjective etale map on every scheme test. Thus the written V atlas proves R_i quasi-compact without any unmentioned global separation assumption. This expands the source's final compactness sentence and avoids incorrectly invoking the qcqs product lemma.

Step 3 uses only the statement of lem-sfb-space-affine-locality: affine transitions have representable closed diagonals. I wrote the pullback identification on sections and then the direct scheme test of that closed diagonal. This proves closedness from the definition, so there is no unsupported appeal to a space base-change theorem and no new node for a two-line diagonal argument. Identity transitions present no exception.

Step 4 uses no additional non-elementary fact: it writes the universal-property argument for the limit cone. Directedness makes the two coordinate families constant; a common upper bound extends tail equalities to every index. The equalities also give the common B-map, so the assumed limit over B applies. The monomorphism hypothesis is given on schemes, and I explicitly test the equality of maps from an arbitrary algebraic space T on its scheme sections. These tests determine natural transformations of sheaves, yielding a=b. This supplies the relative limit over R_0 as well as the absolute cone.

Step 5 uses lem-sfb-space-closed-subspace-proper, whose statement includes local finite type of any closed immersion without finiteness hypotheses, to make every R_i to R_0 locally finite type. The new stabilization node supplies exactly an isomorphism of the limit projections. I checked each of its hypotheses against Steps 1–4, with base R_0, and proved monicity from the diagonal isomorphism on scheme sections. Composing a later equal pair to index i_0 proves the requested all-later-indices assertion explicitly. I tested A empty and a singleton index set; the same construction and argument work.

The off-unit fibre-product, atlas/topology and scheme-cover-composition citations are declared as generic tools in split_report.tool_uses, with their precise purposes. No source route is replaced. All step/node uses are backed by verbatim statements in citations.json. Every step is below 2000 characters, and the two elementary steps are universal-property/definition calculations with their arguments written. No SGA is cited. I checked delivery-errors B–E against the actual files, including same-tag duplicates, elementary versus new-node boundaries, object types and the missing quasi-separatedness of A. I removed a contemplated extra kernel-pair geometry node because its closedness assertion is already a short pullback-of-diagonal calculation, while compactness is proved from existing cited statements.

Mathlib searches were run through the required msearch.py command for the item and each new node, with two semantic phrasings, Loogle and a whole-Mathlib grep, plus LeanSearch. Every search is recorded with its literal query and returned output; all services answered. I read the hits, including the scheme-only LocallyOfFinitePresentation definition (FinitePresentation.lean:40–45), scheme pullback comparison closed immersion (Separated.lean:130–133), and scheme eventual equality statements (AffineTransitionLimit.lean:635–639 and 690–696). These require Scheme objects and do not give the arbitrary algebraic-space results. No unavailable service is reported as absence.

## Unfinished work

No unfinished part of the item's natural-language proof. The two new statement-only nodes are the next stage-1 items, as required by a one-level split. No Lean was written and no compiler or build tool was run.
