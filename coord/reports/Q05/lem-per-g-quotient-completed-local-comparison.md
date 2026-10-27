# Q05 stage-1 delivery

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-g-quotient-completed-local-comparison.json: statement, now split into six steps; no Mathlib match.
- citations.json: one verbatim statement quote for each node cited in each step.
- report.md: this report. searches.jsonl is the required search command log.

New nodes: 0. New Mathlib leaves: 0. The original statement, statement dependencies, created metadata and blueprint ancestry are retained.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag and by completed-local, quotient-completion and Rotthaus concepts, and checked the relevant RingTheory files. No declaration states this entire item. The existing completion-regular and formal-smoothness declarations are tools for individual steps, not attachments for the item.

## Literature

WANTED: Rotthaus (1979), Komplettierung semilokaler quasiausgezeichneter Ringe, Lemma 4 and Corollaries 4.1–4.2, pp.175–176, for lem-per-g-quotient-completed-local-comparison. No copy was found under literature; the inherited Cambridge URL could not be read by the web tool. No claim to have read that paper is made. The inherited source attribution remains metadata. The delivered argument is explicitly agent-written from the locally available Stacks sources below, rather than attributed to that unread paper.

Read literature/stacks-project/algebra.tex: 00MA (lemma-completion-tensor), 0316 (lemma-completion-Noetherian-Noetherian), 05GG (lemma-hathat-finitely-generated), 05GI (lemma-radical-completion), 00CT (proposition-localize-quotient), and 00HR (lemma-local-flat-ff). Read literature/stacks-project/more-algebra.tex: 0AH2 (lemma-map-G-ring-to-completion-regular), 07C0 (lemma-regular-local), 07EL (theorem-regular-fs), 07NQ (proposition-fs-flat-fibre-fs), 07ED (lemma-formally-smooth-completion), and 07PM (proposition-fs-regular). No SGA source is used.

## Corrections and scope

There was no prior sandbox node or report. The live node was unsplit, with no repair note. Its imported assertion is well formed and no statement correction is needed. Its final warning against imposing completeness or a G-ring hypothesis on B is respected. In particular, 07PM is applied only after completing BOTH prime localizations. Applying a closed-fibre regularity criterion to the uncompleted source without an additional hypothesis would be an incorrect shortcut.

The quotient-completion identification is written explicitly, including multiplicativity of the finite-module completion comparison. The equality of the closed fibres uses J contained in p; it is not inferred just from the existence of a quotient. The proof uses the actual coordinatewise completed local map.

## Searches and reuse

Read the existing Mathlib search results in the item and retained them. Ran leanfinder with both a general flat-local phrasing and the semilocal G-quotient phrasing, loogle for FormallySmooth, leansearch for completed local maps, and a RingTheory grep for G-rings/geometric regularity/regular completions. All service calls succeeded. The hits give flatness, discrete formal smoothness, finite-presentation smoothness and regular sequences, not this theorem; Basic.lean defines discrete FormallySmooth, which is not the adic lifting property used here. All fresh queries are recorded verbatim and appear in searches.jsonl. No new node was necessary.

Searched the whole DAG for Rotthaus, formal smoothness, semilocal completion, quotient completion and regular localization, and read every cited node statement. Ran blueprint_refs.py ancestor and whole-blueprint searches for formally smooth, G-ring, completed local and completion regular. No blueprint node states the item in another form; same_as is empty. Read the chapter and unit records and the current latest ancestor proof. This is a generic commutative algebra input below that route; off-unit tools are declared individually in split_report.tool_uses.

## Not duplicates

No new nodes; no new/existing pairs to justify. Existing general lemmas are cited directly.

## Review by Q05

I checked delivery-errors B–E against the actual files and sources, not just their field layout. The item retains its self-contained objects and definitions. There are no new statements, disguised clauses, duplicate nodes, or unsplit proofs. All six steps are below 2000 characters. Every citation in citations.json is copied verbatim from a cited node statement and was read for the precise claim used.

Step 1 uses adic-completion-noetherian for C, noetherian-completion-flat for B to C, and flat-local-ring-maps for B_p to C_Q. Their hypotheses are exactly the given Noetherian B and contraction p of Q; they do not require B to be a G-ring.

Step 2 uses completion-finite-module-tensor with finite B-module B/J and ideal r, g-ring-completion-regular with the given G-ring B/J and ideal r(B/J), surjective-image-noetherian for C/JC, and regular-local-maximal to localize that regular map at Q/JC. The latter explicitly covers every prime, despite its name mentioning maximal ideals. Its target Noetherian hypothesis has been proved. Multiplication on pure tensors upgrades the module comparison to the ring comparison, and the quotient-tensor formulas are displayed rather than hidden in a new lemma.

Step 3 uses localization-at-prime-of-quotient twice, quotient-local-structure for A/JA, and the regular-map definition for the closed fibre. I checked J is contained in p and hence JD is contained in mD. This is why killing m after killing J gives the very same D/mD with its original k-algebra structure. This step is elementary assembly of the cited statements, not an assertion that geometric regularity itself is elementary.

Step 4 uses quotient-local-structure and surjective-image-noetherian to check that D/mD is a Noetherian local k-algebra. Geometrically-regular-local-field-adic-smooth applies without finite-type or separability assumptions. Flat-formally-smooth-closed-fibre-adic then applies to the flat local map from Step 1. Its conclusion is adic formal smoothness, not discrete formal smoothness.

Step 5 uses local-completion-local-ring to identify both maximal ideals, adic-completion-noetherian for both rings, module-completion-complete for their completeness (the original maximal ideals are finitely generated), and fs-adic-complete-source-target for formal smoothness of the specified completed map. That cited statement gives the canonical quotient-coordinate map. The coordinate formula sends the source maximal-ideal generators into the target maximal ideal, proving locality without assuming that an arbitrary map of complete rings is local.

Step 6 uses formally-smooth-complete-local-regular only with the complete Noetherian local rings verified in Step 5. Its statement supplies regularity and flatness. Flat-local-hom-faithfully-flat then gives faithful flatness. Neither statement requires finite type or equality of residue fields.

I tested J=0 (the G-ring hypothesis is then on B itself), J=r (the quotient is a product of fields), already complete B (the comparison reduces to the completed identity local map), field/Artinian B (no nonmaximal primes, so the assertion is vacuous), and the zero ring (no primes). The proof does not use nonmaximality and therefore also behaves consistently at maximal primes. No dubious extension to arbitrary uncompleted local maps is claimed. I also checked the generic inputs do not use the current item in their dependency closure; the remote DAG check is the final mechanical cycle check.

## Unfinished work

No mathematical work remains for this one-level split. The cited unsplit or split DAG nodes remain their own items. Remote dry run and push results are recorded below when completed.
