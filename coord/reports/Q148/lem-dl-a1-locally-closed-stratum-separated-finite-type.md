# Stage-1 delivery: lem-dl-a1-locally-closed-stratum-separated-finite-type

Group Q148, 2026-10-24. Direct delivery with the worker's own source review.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-locally-closed-stratum-separated-finite-type.json: existing statement, now split into five proof steps. Its statement and statement dependencies are unchanged. No exact Mathlib declaration for the entire item was found; existing Mathlib leaves supply the general permanence results.
- citations.json: fourteen step/node entries, each quoting the cited node's statement verbatim.
- report.md: this report. searches.jsonl is the unmodified log written by msearch.py.

New nodes: 0. New Mathlib leaves: 0. No Lean files, compilers, Lake commands, repository writes, or manual git commands were used.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and for locally closed strata, finite type, separated composition, and reduced subschemes. The relevant project declarations do not give all the clauses of this item under precisely its hypotheses. In particular, the availability of the construction of reduced induced closed subschemes is not itself an attachment of this permanence lemma.

## Wanted sources

None. All the source material used is already in literature/stacks-project. I read the current latest blueprint's p-dl-a1-exact proof, the chapter and unit records, and the three-level rule in SETUP.md. This item is an auxiliary geometric fact below the unit's geometric-stalk detection argument; it changes neither the chapter nor the exactness unit's route or statement.

## Audit and corrections

The seed had an empty proof and candidate Mathlib references, so there was no complete split to retain. On resumption the sandbox had only dispatcher marker files, no item or report, and no running deliver.py process for Q148. The live node was unsplit and had no released repair note.

The statement is true as written. The point that needs an actual argument is finite type of the arbitrary open U: an arbitrary open immersion need not be quasi-compact. I proved Spec k Noetherian explicitly, applied the existing finite-type-over-Noetherian lemma to T, and then used the existing open-immersion-into-locally-Noetherian quasi-compactness leaf. No extra quasi-compactness assumption was added to U. I avoided treating the title or the proof of a cited node as its usable statement.

The semantic searches produced general immersion, separation, finite-type, and Noetherian facts, not a declaration giving the full reduced-stratum statement. A second formulation was tried. Loogle and both semantic services answered; none was falsely recorded unavailable. The actual msearch.py queries and outcomes are preserved in searches.jsonl and appended to the item's pre-existing search record. In particular the search found separated composition, but the whole-DAG source-tag search then found that lem-weil-pbc-proper-fp-permanence(e) already states it. No new node was created for it. Searches initially made with the prospective lemma id were rerun with this dispatched item as the logging argument; the delivery uses the actual item log, not reconstructed search records.

## Not duplicates

There are no new nodes. The prospective separated-composition leaf would duplicate clause (e) of lem-weil-pbc-proper-fp-permanence, so it was not created. Searches included the whole DAG by source tags 01KU, 01T3, 01T5, 01T6, 01OX and by concepts, and blueprint_refs.py search for locally closed, separated morphisms, composition of separated, 01KU, and permanence. The nearest blueprint ancestor was verified as p-dl-a1-exact. No blueprint node states this full reduced-stratum assertion in another form; blueprint.same_as remains [].

## Review by Q148

I read the item's cited Stacks statements and the relevant proofs in schemes.tex (01J3, lemma-reduced-closed-subscheme; 01J4, definition-reduced-induced-scheme; 01KU, lemma-separated-permanence), morphisms.tex (01T3, lemma-composition-finite-type; 01T5, lemma-immersion-locally-finite-type; 01T6, lemma-finite-type-noetherian; 035C, lemma-closed-immersion-finite), and properties.tex (01OV, definition-noetherian; 01OX, lemma-immersion-into-noetherian). I also read Mathlib's Separated.lean at the composition instances, and Noetherian.lean at the locally finite-type permanence and Noetherian-source quasi-compactness declarations. There are no new-node sources to audit.

For Step 1 I opened lem-weil-pbc-reduced-induced-closed-subscheme: its clause (2) really gives a closed immersion and exactly the image S, not merely the existence of some closed subscheme. I apply it inside the stipulated open U, where S is closed. The definition in def-weil-closed-immersion explicitly calls a closed immersion followed by an open immersion an immersion, so no composition theorem is being smuggled into the elementary step. I opened def-weil-open-immersion and checked that the open inclusion carries the same subset S into T. For the empty case the underlying space is empty; the empty-cover sheaf axiom forces the zero ring of sections on its sole open. Thus the empty scheme conclusion is explicit, with no nonemptiness assumption.

For Step 2 I opened def-weil-pbc-noetherian-ring and pqf-def-locnoeth. They say every ideal is finitely generated and that an affine cover by Noetherian rings suffices. The ideal argument for a field is written out, so this step is elementary. I opened lem-weil-pbc-affine-scheme-qcqs; it states quasi-compactness for an arbitrary affine scheme, and its application is just X = Spec k. This supplies both parts of the scheme-Noetherian condition needed next.

For Step 3 I opened lem-weil-pbc-finite-type-over-noetherian: its general assertion applies to any Noetherian target, not just the particular Spec Z mentioned afterward. Both hypotheses are present: p is of finite type by assumption and Spec k is Noetherian by Step 2. I opened lem-sfb-noetherian-open-immersion-qc, whose exact assertion requires only that T be locally Noetherian. I then opened lem-weil-pbc-qc-open-immersion-finite-type and applied it to the resulting quasi-compact open immersion u. The argument does not confuse quasi-compactness of the underlying open with an unexplained claim of quasi-compactness of its morphism.

For Step 4 I opened lem-weil-pbc-separated-cancellation: clause (a) expressly includes open immersions, and supplies separatedness of u. I opened lem-weil-pbc-proper-fp-permanence: clause (e), not its properness clauses, expressly supplies separatedness under composition. I opened lem-sfb-finite-type-composition-base-change: clause (1) supplies finite type under composition. The two maps are exactly u:U -> T and p:T -> Spec k; all their required properties have been verified. These are existing Mathlib leaves, so no proof route from another unit is substituted.

For Step 5 I opened lem-weil-pbc-closed-immersion-integral-separated-uc and checked that clause (c) actually says finite, not only integral. I opened lem-weil-pbc-finite-over-separated-finite-type, whose general statement takes a finite nu and separated finite-type g. Here nu is i and g is p composed with u from Step 4. The conclusion concerns the correct composite (p composed with u) composed with i = p composed with a. It gives both required properties and introduces no extra field, reducedness, finite-presentation, or nonemptiness hypothesis.

Against delivery-errors B, all objects are already introduced in the unchanged item, no new statement-only nodes are required, and the existing-node citations carry the exact notions used. Against C1/C4 I checked every cited statement as described above and supplied all fourteen verbatim quotes; every non-elementary permanence assertion is a cited node. The reduced-induced theorem is explicitly declared as an off-unit generic tool in split_report.tool_uses; it is the scheme construction already named by the item, not a replacement exactness argument. Against D, the five steps carry the argument and no clause has been repackaged as a new lemma. Against E, I checked the empty stratum, S = |T| (with U = T and the reduction closed immersion), nonreduced T, and arbitrary open choices of U. No statement dispute arose. No proof step exceeds 2000 characters; the non-elementary steps are applications of the exact interfaces above, and the field/empty arguments are the only elementary subarguments.

## Unfinished work

None in the mathematical split. Delivery validation and the push are performed by the prescribed deliver.py commands; their outcome is recorded below after execution.

## Validation

The prescribed deliver.py --no-push process completed with exit code 0 and printed `OK (not pushed)` at 7f6119cf081, with server preflight passed. The process finished before the push invocation was started. No Lean compilation was performed.
