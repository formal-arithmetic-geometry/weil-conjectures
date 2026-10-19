# Worker report: lem-coef-kan-iterated-pullback-fibrancy

## Files written

- dag/nodes/sec-six-functors/lem-coef-kan-iterated-pullback-fibrancy.json: statement node, split; no exact Mathlib match for the recursive finite-tower assertion. Statement and statement dependencies unchanged.
- citations.json: exact quotations for the definition cited in each of the four steps.
- report.md: this report. searches.jsonl contains the actual Q12 search records.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searched WeilConjectures/ in the read-only slopmaster2 source for the exact blueprint tag, iterated pullbacks, Kan complexes and pullback fibrancy. The hits concern comma-category iterated pullbacks and blow-ups and do not state this item. No compiler or Lake command was run.

## WANTED

WANTED: an archived copy of Kerodon Subsection 3.1.1, Tag 00T0, Definition 3.1.1.1 and Remarks 3.1.1.6, 3.1.1.10, 3.1.1.11, for lem-coef-kan-iterated-pullback-fibrancy. Read https://kerodon.net/tag/00T0 online on 2026-10-17; no file was downloaded. The proof is marked agent-written because the finite induction and all lifts are expanded here, with no archived literature copy available.

## Corrections and route

No statement dispute: the imported statement is true including empty simplicial sets. Its last-coordinate endpoint assertion is essential to the simultaneous induction. The proof now gives the lifts rather than merely invoking closure under pullback or composition. There are no new clause-only nodes and no hidden standard lemmas.

The inherited Mathlib-search verdict mentions an endpoint-preserving constant-path comparison, which is a different assertion belonging to the neighbouring chain-comparison item. I retained those historical records and appended the actual Q12 searches with the narrower correct question. The item itself only asserts fibrancy, successive projection fibrancy and endpoint fibrancy.

Read the assigned chapter and unit records and the blueprint ancestor proof in main-20261015, prop-coef-integral-exceptional-adjoint.proof.md, paragraph 2. This item is a generic foundational step supporting the inherited classification-diagram dependency chain beneath the displayed coefficient adjunction. It is not a unit key node, and no unit record is changed. No SGA source is used. The projected finite-tower argument stays beneath the existing blueprint ancestry.

## Not duplicates

No new node was created. The whole-blueprint search for "iterated pullback" finds only the unrelated Nagata descended-model definition. The existing kan-fibration-tower-limit node concerns an infinite inverse limit and its coherent limit cone; the iterated-chain-comparison node concerns constant-path weak equivalences to homotopy pullbacks. Neither states this item's finite fibrancy claim, and neither is needed. The general Kan model-structure node is also unnecessary: all lifts are supplied directly from the stated right lifting properties.

## Review by Q12

I checked the whole B--E checklist against the item and the cited definition. For the source I read Kerodon 00T0 in full: its definition includes every horn in dimension n > 0, including outer horns; Remark 3.1.1.6 gives pullback closure, 3.1.1.10 gives composition closure, and 3.1.1.11 gives a Kan total space over a Kan base. I wrote their elementary horn calculations at the actual tower stage, so no uncited closure theorem is assumed. No new source-bearing node is introduced.

For step 1 I read the full statement of def-cbc-enhanced-diagrams-cones: it specifies degreewise pullbacks with coordinatewise operators, and defines Kan complexes using all positive-dimensional horns without nonemptiness. This justifies the pair notation and the endpoint identities; the base case is precisely the hypotheses P_1 = E and t_1 = t. I state the simultaneous induction before using any inductive conclusion.

For step 2 the same degreewise-pullback sentence ensures that a pair of simplicial maps with equal images really is a map into P_k. The equality on the horn needed to lift through s is t_{k-1} a = s b, so the original hypothesis on s supplies the required last coordinate. The constructed pair has the prescribed first coordinate and horn restriction. This is a few-line use of a hypothesis, not an appeal to a separate pullback theorem.

For step 3 I checked the order of both lifts: first lift b along t over the requested endpoint c, then lift a along t_{k-1} over s e. The latter is available by induction, and s e restricted to the horn equals s b = t_{k-1} a. Consequently the output pair lies in precisely the stated pullback and its endpoint is c. No assumption that (s,t):E -> B x B is a fibration is made or needed.

For step 4 the cited definition's Kan condition gives the first-coordinate extension by the induction hypothesis. The projection lifting property already proved in step 2 lifts it to an extension of the entire horn. Thus Kan fibrancy is a conclusion, not an additional induction hypothesis at the new stage. Each step cites only the definition whose content it actually uses; citations.json quotes a literal sentence from that statement for each occurrence. Other steps and the item's own hypotheses are referenced explicitly. All four steps are elementary because their entire argument is at most two horn lifts from the stated lifting hypotheses; no general result is concealed behind a definition citation. Every step is below 2000 characters.

I tested k = 1, k = 2, the one-point span, constant discrete spans, empty E with nonempty B, and empty B (which forces empty E). A discrete map is a Kan fibration even if not surjective on components, so no inappropriate surjectivity enters the proof. Horns in dimension 1 are nonempty; there are no positive-dimensional horn maps into an empty simplicial set, so the empty cases are vacuous, exactly as the statement requires. The endpoint lift respects s and t in the correct order and never identifies the two endpoint maps.

I read the Mathlib hits: Instances.lean:226--234 supplies the two binary pullback-projection fibration instances, IsCofibrant.lean:96--102 supplies fibrancy over a fibrant base, and PathObject.lean:189--204 requires good path-object data that the item does not assume. The strict-Segal second-phrasing hits concern reconstruction of simplices from spines and have no such tower claim. The recursive finite induction is still required; the whole item is not a one-line specialization. The logged searches were actually run, with no unavailable service counted as absence. No new node searches are claimed. The proof-dependency list is exactly the union of the four step citation lists, and all quotations were checked against the definition's statement.

## Unfinished work

No mathematical part remains at this split level. The required server dry run and delivery are the remaining validation steps.
