## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-module-quotient-map-small-models.json: item, split into five steps; no exact Mathlib match.
- citations.json: a verbatim statement quote for each of the six step-node citations.
- report.md: this report. searches.jsonl is the unmodified search-command log.

No new nodes and no new Mathlib leaves. This repairs the returned delivery at 232a3fa2506, whose sandbox proof, report, citations and search log were retained. The imported statement, source, created record and blueprint ancestry are preserved.

## Attachments

None. Searched the live WeilConjectures source for the exact item id, quotient/kernel and smallness terminology, including the GrothendieckAbelian files. GeneratingMonoQuasiIsos.lean:158-164 uses the cokernel-of-kernel argument for a complex, but does not state this item's literal-subsheaf indexing or fixed-domain representative theorem. No exact project declaration was found, so no attachment is claimed. No Lean was written and no compiler was run.

## Literature

WANTED: none.

Read literature/stacks-project/modules.tex, Tag 01BC (lemma-set-isomorphism-classes-finite-type-modules), especially the parametrization of local finite-free quotients by kernel subsheaves and the following set-size argument. Read the entire preceding kernel and cokernel construction in the section Tag 01AF, and Tag 01AG (lemma-abelian). The extension from fixed finite-free sources to one arbitrary fixed module is the same kernel argument; the expanded proof is correctly marked agent-written. The categorical notion is the existing def-sp-abelian, whose full statement explicitly supplies normal epimorphisms. I also read the Stacks homology.tex definition-abelian-category, Tag 0109; its image/coimage formulation is compatible with the already-reviewed Mathlib leaf's normal-epi formulation.

Read dag/chapters/sec-proper-base-change.json, dag/units/sk-thm-p1.json and the current main-20261015 lemma-weil-pbc-h1-constructible-representation.proof.md under sk-lem-pbc-p1-injective-fibre. This supports the existing finite-pushforward/approximation chain; no unit or chapter route is replaced and no realization field needs editing.

## Corrections and scope

No statement dispute or source error was found. The original statement is retained verbatim. Its empty proof is replaced by the argument; proof_deps is exactly the union of the uses lists. In particular, an epimorphism of sheaves is never assumed surjective on every open's sections. The source's unexplained quotient parametrization is expanded into a literal kernel and two compatible inverse maps, including the equality with the original epimorphism, rather than only an isomorphism of the targets.

## Searches and reuse

Searched the whole DAG by statements for epimorphisms as cokernels, cokernels of kernels, and image/coimage; searched blueprint_refs for quotient, cokernel of, and subshea, and asked for the item's blueprint ancestor. Reused def-weil-sheaf-of-modules-category and def-sp-abelian, reading both files in full. Their statements, not arguments hidden in their proofs, supply everything cited.

The current msearch log has leanfinder queries in two phrasings, loogle, grep, and leansearch. The live services returned results; none is recorded as unavailable. Earlier searches inherited from Q54 are retained as historical records with their original results, including that earlier LeanSearch outage. New exact query strings and hits are appended. Read ModuleCat/Subobject.lean:55-70 and Presheaf/Generator.lean:80-103: their well-powered instances concern module or presheaf subobjects, not this sheaf quotient family. The semantic hits describe small sections, generating sections of epi targets, quasicoherent presentations, or Grothendieck categories; none supplies the literal-kernel-indexed family and compatibility with every p in one line.

## Not duplicates

No new node is proposed. All needed categorical notions and assertions are already stated by the two cited Mathlib leaves. In particular, I did not create a node for set-sized families of subsets, a literal kernel, the epi property of a cokernel, or uniqueness of two cokernels: their short arguments are in the item itself.

## Review by Q82

I checked each proof step against the sources above and against the complete statements of its cited nodes. In step 1, def-weil-sheaf-of-modules-category identifies the sectionwise module structures and semilinear restrictions that are inherited by a literal subsheaf. The universe assumption in the item puts Op(X) and each M(W) in the fixed universe; closure under power sets, indexed products and subsets gives T in that same universe. The fields of the subsheaf carry no independent structure beyond the subset family. This argument needs no well-poweredness theorem.

In step 2 the module-category node explicitly says the category is abelian for a small site and describes cokernels as sheafifications. In this repair I made the simultaneous construction explicit: for each literal K, take the presheaf W ↦ M(W)/K(W) with its induced restrictions and sheafify it, obtaining Q_K and the induced q_K. Thus the family is specified by one construction on the small index set T. Op(X) is small here by step 1. The cited def-sp-abelian explicitly asserts the existence of kernels and cokernels in an abelian category. Thus a cokernel exists for every literal inclusion, with its concrete sheafification construction staying in the universe. The epi property is proved by cokernel uniqueness. I marked this step non-elementary because it invokes the existing abelianity assertion, rather than passing that assertion off as elementary. Neither citation is merely a definition of a notion without the property being used: both statements explicitly give that property.

In step 3 the module-category node gives sectionwise kernels, and the text additionally verifies the submodule condition, stability, gluing and the kernel universal property. The vanishing of the glued image uses separatedness of N as a sheaf, not sectionwise surjectivity of p. Linearity and naturality ensure that the factored maps really are module-sheaf morphisms. No extra hypotheses on X or M are introduced.

In step 4 the same module-category statement supplies abelianity, and the exact phrase 'every epimorphism is a cokernel' occurs in def-sp-abelian. This only gives that p is a cokernel of some a; I did not pretend it says p is the cokernel of its own kernel. The latter is proved here: a factors through the literal kernel, so any h annihilating that kernel annihilates a, and factors uniquely through p. This is a three-line universal-property deduction, appropriately kept as an elementary step rather than made into a new lemma or silently quoted as a first-isomorphism theorem.

Step 5 uses only the two cokernel universal properties already established. It writes both comparison maps and checks both composites via uniqueness. This yields the required equation psi q_K = p with the correct direction of psi. No fresh non-elementary fact or external node is used in this step, so its uses list is empty.

I tested the empty space, the zero module, K=0, K=M, and an isomorphism p. On the empty space or for M=0 there is still the zero subsheaf and its zero cokernel; on K=0 the map is an isomorphism, while K=M gives the zero quotient. An isomorphism p has zero literal kernel and is recovered with the required factorization. Nothing requires finite generation, finite presentation, quasi-compactness, or a separated topological space. Redundant isomorphic targets in the T-family are permitted by the statement; uniqueness of t was never asserted.

Against delivery-errors B--E: no new node hides a proof, repeats a clause, or lacks hypotheses; no unavailable search is reported as a negative result; all six citations have checked verbatim quotes in citations.json; no theorem is taken from a cited proof; and no universal-property calculation is replaced by 'transport' or an unexplained comparison. All steps are shorter than 2000 characters. Both external nodes are existing Mathlib leaves, so the cross-unit citations are generic tools with no route change or new tool-use waiver. The entire proof is written out without moving any clause into a replacement node.

## Unfinished work

None at stage 1. The earlier delivery expanded every citation to its complete verbatim statement. The initial dry run for this repair passed before edits; the final dry run and direct push validate the revised construction and repair report.


## Repair of return L (2026-10-22)

The return names approved head 232a3fa2506 and says that side completion had not been promoted to the live DAG. I continued its retained sandbox rather than reconstructing or discarding that proof. The current read clone has this item unsplit, with empty proof and proof dependencies. Comparing it with the retained delivery showed differences only in split-owned fields: proof, proof_deps, proof_origin, status, mathlib_searches and split_report. Statement, stmt_deps, source, created record, chapter, unit and blueprint ancestry agree. No released repair-note file exists for this item.

I re-read the entire current def-weil-sheaf-of-modules-category and def-sp-abelian files, including their Mathlib matches. All six saved quotations remain verbatim substrings of the current statements, so their mathematical interfaces require no citation replacement. The former explicitly supplies sectionwise kernels and sheafified sectionwise cokernels on a small site; the latter supplies that every epimorphism is a cokernel of some arrow. The proof still establishes the stronger cokernel-of-the-kernel property itself by factorization. I re-read modules.tex, Tag 01BC and the kernel/cokernel constructions preceding Tag 01AG, and the current main-20261015 ancestor proof. The source and route therefore support the retained argument under the current DAG.

The substantive clarification is in step 2: it now constructs each quotient by the same sheafification of the literal sectionwise quotient presheaf and its induced map, rather than saying to choose a cokernel separately. This makes the family and its universe bound explicit using precisely the construction asserted by the existing citation. Empty X, zero M, K=0, K=M and an isomorphism p still satisfy every step. No step exceeds 2000 characters, and no additional lemma is hidden in this clarification.

The current project-source search for the exact blueprint tag and quotient-smallness/co-well-powered terminology found no declaration stating the item. The retained msearch results have been read and remain applicable to the unchanged statement, so no searches were repeated or invented. The delivery tool rebuilds the commit on the fetched current origin/sheaf-dag, preserving its maintainer-owned fields; the successful initial dry run confirms that this current unsplit item is admitted for delivery. This report and the explicit quotient construction replace an unchanged re-push.


## Resumed repair verification (2026-10-22)

The interrupted tool session was no longer present, and no delivery command for this item remained running. The replacement initial dry run exited successfully: `OK (not pushed)` at aacdd69cbc8. I re-read both complete current dependency files and verified all six saved quotes verbatim. Comparing the current item against the sandbox found differences only in proof, proof_deps, proof_origin, mathlib_searches, split_report and status. No repair-note record exists. The item statement and all its statement dependencies remain unchanged.

I clarified step 2 once more: abelianity and the sheafified-cokernel assertion are applied inside the category of module sheaves with section sets in the fixed universe. Consequently the resulting cokernel belongs to that category; the universe bound is supplied by the cited assertion, rather than being an unstated additional sheafification theorem. The smallness hypothesis holds because the opens are a subset of the power set of the universe-small point set. This preserves the explicit, uniform quotient construction introduced by the repair. I re-read Tag 01BC and the sectionwise kernel and sheafified cokernel construction before Tag 01AG, and the current ancestor blueprint proof. No additional node or new search is needed for this clarification.

The retained search-command log and the current Mathlib subobject and presheaf generator declarations were re-read. They still concern module or presheaf subobjects, rather than the asserted family of module-sheaf quotient maps. The current project-source search again found no exact tag or quotient-small-model declaration. The proof-dependency union is exact, all five steps remain below 2000 characters, and the empty space, zero module, zero/full kernel and isomorphism cases still work. A final dry run and push follow this edit.
