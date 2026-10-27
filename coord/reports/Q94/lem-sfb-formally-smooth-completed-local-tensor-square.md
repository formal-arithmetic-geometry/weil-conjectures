# Q94: lem-sfb-formally-smooth-completed-local-tensor-square

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-formally-smooth-completed-local-tensor-square.json`: existing statement, now split into eleven steps; Mathlib verdict no match for the whole statement.
- `citations.json`: one verbatim statement quotation per step/cited-node pair (34 entries).
- `report.md`: this report.

No new DAG nodes and no new Mathlib leaves. The sandbox also retains `searches.jsonl`; `write_split.py` is the sandbox-only preparation script.

## Attachments

None. Searched the live read-only `lean/WeilConjectures/` by the blueprint tag and by completed-tensor/formal-smoothness terminology. No project declaration without sorry states all the item's clauses under these hypotheses. The ordinary formal-smoothness and finite-module-completion Mathlib hits do not give this statement.

## Missing literature

WANTED: EGA I, Chapter 0, 7.7.1--7.7.7, for lem-sfb-formally-smooth-completed-local-tensor-square.

WANTED: EGA IV, Chapter 0, 19.3.5(iii)--(v) and 19.3.6, for lem-sfb-formally-smooth-completed-local-tensor-square.

The EGA source metadata inherited from Q102 is retained. I read the cited online English EGA adic-rings page for context. The combined diagonal-localized tensor assertion has no single source theorem there: `proof_origin.by` is `agent`, and the proof below uses the actual local Stacks statements, not an unverified EGA assertion.

## Issues and changes

The imported node had a complete statement but no proof. Its statement and `stmt_deps` are unchanged. There is no statement dispute and no route change. One tempting intermediate assertion would be unjustified: the uncompleted ring `(R tensor_A R)_q` is not assumed Noetherian. The split avoids it by proving that its maximal ideal is finitely generated and its residue ring is a field, then invoking the general completion criterion 05GH. Likewise the quotient/completion identification is not deduced from a completion-exactness theorem with a missing Noetherian hypothesis: the proof uses surjective kernel towers and only applies Krull intersection after establishing that E is Noetherian.

The current blueprint was read under `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`. Whole-blueprint searches for the completed tensor-square statement and variants gave no equivalent node. The ancestry command returns a null blueprint ancestor for this inherited created-node chain; its existing precise `from.place`, `via` chain and empty `same_as` are retained and explained in `split_report.blueprint`.

## Unfinished

Nothing in the stage-1 split remains unfinished. No Lean, build or compiler operation was performed.

## Not duplicates

There are no new nodes. Every general algebra input is an existing node, including the general completion criterion, the adic formal-smoothness tools and inverse-limit exactness. No clause of this item was relabelled as a new lemma.

## Review by Q94

I read delivery-errors B through E against the actual JSON statements and the local Stacks source. The main item is an agent assembly of elementary tensor/fraction formulas and existing algebra theorems. I read algebra.tex at Tags 00FN (Noetherian permanence), 05GG (finitely generated ideal completion), 05GH (Noetherian quotient completion), 03CA (Mittag-Leffler exactness), 00IQ (Krull intersection) and 00MC (local completion is faithfully flat), and more-algebra.tex at Tags 07EG (base change), 07ED (completion), and 07NP (adic formal smoothness implies local flatness). There are no newly created nodes requiring separate source checks. All 34 `uses` entries have a corresponding verbatim quotation in citations.json; I read those statements, not just their titles or proofs.

1. Step 1 uses the definition of Noetherian rings for finite generators of m_R and of q/H; the tensor-quotient node gives each factor quotient; the finite-algebra node applies because a finite k-basis of l spans l tensor_k l over l; the localization definition supplies the local ring S and its maximal ideal. The displayed finite-generator argument proves q finitely generated directly. It uses no finite-type or separability assumption on R/A.
2. Step 2 takes exactly the conclusion of the general completion-Noetherian node, whose hypotheses are only a finitely generated ideal and Noetherian quotient. The completion-mod-power node supplies the surjective coordinate maps and their kernels. Both are valid before knowing S Noetherian; this was the main hypothesis check.
3. Step 3 is the elementary inverse calculation in the local quotients S/n^N and the compatible-sequence definition of completion. Its two definition citations really state those objects. The residue composites explicitly identify both inverse images of the maximal ideal and each induced residue-field map. No Henselian or coefficient-field assertion is used.
4. Step 4 takes the adic base-change statement, not an ordinary algebraically formally smooth variant. I checked that its ideal is the image of m_R from the other tensor factor. A map continuous for n kills a power of that smaller ideal. The definition of adic formal smoothness supplies the lift of P. Every inverted denominator remains invertible after a square-zero lift by the displayed b(1-u) formula; the fraction formula proves the localization step rather than citing a definition for an unproved localization theorem. The continuity power is 2N. The factors are interchanged in exactly the same formula, so neither map is omitted.
5. Step 5 invokes the completion formal-smoothness node with the already finitely generated n. Its statement does not assume S Noetherian. In contrast the local-flatness node does assume both source and target Noetherian local: R has that hypothesis and steps 2--3 prove it for E. Both maps are local by step 3. Flat-local faithful flatness is then exactly the cited statement.
6. Step 6 uses the tensor universal property for multiplication, fractions for its extension to S, and the definition of completeness of R for its extension from compatible quotients. The completion-mod-power statement supplies the continuity kernels. The products of residues are nonzero precisely for denominators outside q. Both retraction identities are checked at every quotient of R and then use the separation included in completeness. This is an explicit construction, not an implicit continuity-extension theorem.
7. Step 7 uses tensor-quotient and tensor-pushout statements for the maps between R tensor_A l and B tensor_k l. The inverse is independent of the lift because m_A acts trivially on l. For the localization comparison, the fraction formulas check denominators using the inverse image q of r and check the quotient ideal K. These formulas establish S/K = F_r, and identify the maximal ideal, rather than assuming a localization/completion interchange.
8. Step 8 uses exactly the surjective-kernel clause of the tower-limit node. The index is the countable positive-integer tower of S-modules; the quotient maps commute, the sequences are short exact, and a representative k in K proves surjectivity of every K-transition. The completion definition identifies the resulting target. There is no unsupported general assertion that inverse limits are right exact.
9. Step 9 uses the canonical surjections and kernels in the completion-mod-power node to compute the preimage of K_N as J+m^N. Krull intersection is applied to the cyclic (hence finite) E-module E/J, with E Noetherian and m its unique maximal ideal, hence its Jacobson radical. This gives exactly the kernel J of theta. The formula for the image of j_1(r) establishes the claimed compatibility and canonicity.
10. Step 10 invokes surjective-image Noetherianity for B, finite-algebra Noetherianity for F using the written finite spanning set, and localization Noetherianity for F_r. B is local as a proper quotient of R; its residue is l, and the composite to l computes r's contraction exactly. No condition that l/k be separable is inserted.
11. Step 11 takes the field-extension-base-change faithful-flatness statement for the k-algebra B and uses the faithful-flatness definition's explicit implication to flatness. The localization-flatness node applies at r with contracted prime m_B; B localized there is B. The local-completion theorem applies to the Noetherian local ring F_r established in step 10. Flatness of composites and the flat-local faithful-flatness lemma then prove the desired closed-fibre faithful flatness. The target is the actual quotient E/J through the explicit step-9 isomorphism, and locality follows from the computed residue map.

I also checked the elementary limiting cases: A=R, including mixed characteristic and nonreduced complete local rings, gives E=R and the stated retractions; k to k[[x]] gives the familiar two-variable completed square and quotient by the second variable. The finite-dimensional diagonal argument works without separability and the lifting proof never assumes a coefficient field. No false strengthening such as Noetherianity of P or S was retained. The statement remains self-contained, with the original definition dependencies, and has no new axiom or construction hidden in a source reference.

For C7/C8, the five off-unit non-Mathlib tools are declared only in `split_report.tool_uses`: completion with Noetherian quotient, adic base change, adic completion, adic local flatness, and surjective-kernel tower exactness. These are generic algebra tools for the inherited completed-square route, and no node of this six-functor unit supplies their statements. No top-level maintainer-owned `tool_uses` field was written. For D, the eleven steps actually prove every clause using these strictly more general inputs; there is no new restatement, circular downstream normal-power-series citation, or invocation of another node's internal proof. For B, there is no new-node schema or leaf claim to justify; existing metadata and searches were preserved and actual Q94 searches appended. The malformed initial Loogle name query is explicitly recorded as unavailable, followed by the successful quoted-name query. For E, all base rings, ideals, square-zero assumptions, finite generation, locality and Noetherian hypotheses are accounted for above. All non-elementary steps are under 2000 characters, and the explicit fraction and compatible-sequence calculations contain no suppressed comparison lemma.
