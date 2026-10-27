# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-commutative-group-local-constant-product.json: statement, now split into six steps; no Mathlib match for the whole item.
- citations.json: one entry for every step/node citation, with the complete verbatim statement of the cited node.
- report.md: this report. Auxiliary source extraction milne.txt and the task-specific script write_split.py stay in the sandbox; they are not delivery nodes.

No new nodes and no new Mathlib leaves. The inherited statement, source, chapter, unit, created record and blueprint ancestry were retained. Added statement pointers to the existing definitions of the constant group scheme, fibre product, spectrum and open immersion, all notions used in the statement.

## Attachments

None for this item. The project search for its exact blueprint tag and for finite group schemes, connected components, and constant products found no project declaration covering its product isomorphism, subgroup, local augmented algebra and dimension clauses together. GroupScheme/Finite.lean proves other finite-group-scheme results, while GroupScheme/Basic.lean proves translation of connected components; neither states this entire item. The existing closed input AlgebraicGeometry.exists_comp_eq_id_of_isFinite belongs to lem-sc-finite-nonempty-point; it is used through that existing node, not claimed as an attachment of the item.

## WANTED

None. The item source Milne, Algebraic Groups (2017), Propositions 11.1–11.3, printed pp.209–210 and Proposition 2.37, printed pp.51–52, is available and was read. The local algebra and affine-scheme sources used below are in the Stacks checkout.

## What was wrong or incomplete

The item was a statement-only node, with no proof. Its statement is correct and unchanged. The inherited blueprint.from.node is null: tools/blueprint_refs.py ancestor prints None for this deep created-node chain. I preserved that inherited metadata and supplied the exact role of the split in split_report.blueprint. Whole-blueprint searches for finite commutative group schemes, finite group schemes and Artinian inputs found no equivalent statement; the available finite-order and finite-point blueprint nodes have different conclusions. The newest blueprint's direct-image proof (3) is the current upper route; this auxiliary group-scheme argument does not replace any unit step.

The proof follows the finite-local-component content of Milne 11.1–11.3, but I marked proof_origin.by as agent: the explicit tensor-locality, translations and gluing argument is my expansion, rather than pretending Milne writes every one of these details. In particular I did not invoke Milne 11.3 itself as a new node restating the item.

## What remains unfinished

Nothing in this stage-1 split. The cited unsplit tool lem-trf-integral-local-tensor-purely-inseparable remains its own future stage-1 task; it is cited only for its stated conclusion, with all its hypotheses checked. No Lean was written, and no compiler, Lake or build tool was run.

## Mathlib and duplicate searches

Preserved the item's prior searches and added the actual recorded current-session leanfinder queries in two phrasings, leansearch, loogle and grep. Read their returned hits: Galois-category connected decompositions and finite scheme coproducts do not give the local–constant group-scheme decomposition. Searches are recorded in searches.jsonl, with the exact query text copied into mathlib_searches. No unavailable service was treated as a no-match.

Before considering auxiliary nodes, searched the whole DAG by titles/statements, local Artinian components, tensor locality, finite spectra and the Stacks tags 00JB, 00J8, 092Y, 06LH and 04GH, and used blueprint_refs.py search for Artinian and finite group scheme statements. These exposed sufficient existing inputs, so no node was created. In particular the general integral local tensor lemma already covers the residue K/K case. The full Stacks 00JB product theorem is not asserted by the existing self-finite-length node, so I did not cite that node for a product decomposition: Step 1 obtains the product of the actual open components directly from the sheaf gluing axiom.

## Not duplicates

No new nodes: there are no new/existing pairs requiring a distinction.

## Review by NA

I read Milne 11.1 and 11.2, including their proofs of finite discrete spectra and local component rings, 11.3 including its perfect-field hypothesis and semidirect-product warning, and 2.37 for the identity-component interpretation. I kept the algebraically closed and commutative hypotheses: algebraic closure supplies rational points of each component, while commutativity is used precisely in Step 5. The split does not assert a direct product for a noncommutative group or over an imperfect field. No SGA reference is used.

For Step 1 I opened all five cited node statements. The finite-over-field node gives both the affine realization and finite dimension. The finite-over-zero-dimensional-local node really states finite discrete spectrum, and applies to the field K with its sole prime (0). The finite-discrete-scheme-affine node applies to each singleton open, without adding separation hypotheses. Its section ring is a direct factor because sections on a disjoint open cover are a product, directly by the sheaf axiom. The finite-dimensional-Artinian node gives Artinianity, and the definition of a finite morphism gives finiteness of each component from that affine finite algebra. I read Stacks 01WH and the 03J3 paragraph, 06RS's finite-spectrum argument, 01ZV and Milne 11.1–11.2 against these uses. No product decomposition theorem was taken from a node which only states finite length.

For Step 2 I opened the finite-nonempty-point, spectrum, Artinian-local-nilpotence, and group-scheme statements. The first applies to every component because Step 1 proves it finite and nonempty. The spectrum statement identifies its rational point with a K-algebra map; it is surjective because constants map identically. The Artinian local hypothesis of the nilpotence node is established, not assumed from a definition. I read Stacks 00J8 and 00KH. Killing that nilpotent ideal and then using the quotient K proves uniqueness explicitly; this also checks the residue-field and augmentation assertions without invoking an unstated uniqueness theorem. The group law on H comes from the group-scheme definition.

For Step 3 I opened the full local-tensor tool statement, affine-fibre-product statement and unique-prime and Artinian statements. Read Stacks 092Y (algebra.tex, lemma-local-tensor-with-integral), 01I4 (schemes.tex, lemma-fibre-product-affine-schemes), 00J6 and 00KH. Both base maps K to B are local because nonzero constants are units; integrality is proved by linear dependence of powers, not silently inferred. Both residue extensions are K/K and so purely inseparable. The tensor is finite-dimensional by a displayed finite spanning family, and the local-Artinian unique-prime node gives exactly the singleton spectrum required. The identity pair supplies that singleton's image, so multiplication lands in the open identity component. Factorization here is through an OPEN subscheme, where the structure-sheaf restriction gives the factorization; it does not use the false general claim that topological image in a closed subscheme suffices. All group identities restrict along the open monomorphism. The tool is declared explicitly in split_report.tool_uses.

For Step 4 I checked the group-scheme, constant-group-scheme, coproduct-family, fibre-product and scheme-morphism-gluing statements. The constant definition alone does not claim group axioms, so I wrote their componentwise verification. The coproduct node supplies the open components and their universal mapping property; the fibre-product universal property identifies their pullbacks with C. The gluing node supplies the maps in both directions, and the inverse is written on each component as translation by -h. I added this gluing citation during self-review instead of leaving the scheme gluing fact implicit. This generic off-unit tool is declared in split_report.tool_uses. The only other off-unit statements used are definitions, Mathlib leaves or the existing closed rational-point node, as permitted. All step citations are repeated verbatim in citations.json.

For Step 5 I checked the precise multiplication in the constant-group definition and the functor-of-points equivalence in the group-scheme definition. The calculation compares (c+c')+(h+h') with (c+h)+(c'+h') over EVERY test scheme, not just K-points (K-points alone cannot detect nonreduced group schemes). Open-cover equality is exactly what the gluing node states. The inverse is a homomorphism because the already constructed underlying scheme isomorphism cancels the homomorphism equation. Thus there is no hidden identification or claim that translations themselves are homomorphisms.

Step 6 uses the preceding component isomorphisms and product algebra, and writes the finite-product basis calculation; it requires no extra theorem. I checked that d and q are positive using the identity section, rather than assuming all finite algebras are nonzero. Every step is under 2000 characters. Elementary steps contain only the displayed universal-property, gluing or group calculations from their cited statements; the non-elementary algebra inputs are separate cited nodes, not inline hidden lemmas. New-node requirements B1–B10 are vacuous, C1–C8 were checked citation by citation, D1–D5 are met by the actual translation/subgroup argument, and E1–E7 by the hypothesis and edge-case checks above.

Small cases checked: the trivial group gives d=q=1; a constant finite commutative group gives d=1; alpha_p and mu_p over an algebraically closed field of characteristic p give q=1 and d=p; products of these with a constant group give the expected dq. The identity rules out the empty scheme. Noncommutative semidirect products explain exactly why commutativity cannot be dropped, agreeing with Milne's warning after 11.3. There is no statement dispute or weakened conclusion.
