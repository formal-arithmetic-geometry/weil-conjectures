## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-split-simple-absolute-irreducibility.json: item, split; statement and statement dependencies retained exactly.
- dag/nodes/sec-six-functors-basics/lem-sfb-split-simple-multiplicity-one-weight.json: new statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-scalar-endomorphisms-absolute-simplicity.json: new statement, unsplit; no Mathlib match.
- citations.json: verbatim statement excerpts for the two citations in steps 1 and 3.
- searches.jsonl: actual msearch.py log; retained. Supporting source extraction and writer are confined to this sandbox.

Two new nodes, zero Mathlib leaves. No unit file is changed: this item is a supporting lemma rather than its unit's key statement.

## Attachments

None. Searched the project WeilConjectures source for the blueprint tag, split simplicity, absolute irreducibility, highest weights and related statements. The hits on absolute irreducibility concern polynomials and scheme fibres, not rational representations. No project declaration states this item. A further Sheaf search also found no finished declaration of either new statement.

## WANTED

None. Milne's Algebraic Groups is present as literature/milne-algebraic-groups_iAG2017.pdf. The proof uses this reference, not SGA.

## Findings and route

The item is correct; no STATEMENT-DISPUTED change is required. Its imported proof was empty. Milne 22.4 explicitly deduces absolute simplicity from scalar endomorphisms via 4.19. The essential representation-theoretic input to the scalar calculation is the multiplicity-one weight of 22.2 and 22.18(b). Merely citing the existing algebraically closed highest-weight theorem would add an unavailable hypothesis on k. This split keeps the actual field k throughout and uses the arbitrary-field input instead.

Read the current latest blueprint's sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). The present item is an inherited distant supporting prerequisite for that direct-image alteration argument, through the existing characteristic-zero Weyl-character chain. No chapter, unit, or prescribed route changes. The ancestor command returns None because the inherited created.item chain terminates at a non-blueprint root. The item keeps its precise existing from.place and via list, and each new node adds this item to that list. same_as is empty after the blueprint searches.

## Search record

All Mathlib discovery for this delivery used the required msearch.py command. Each new node records its own semantic searches in two phrasings, Loogle, and grep, with the exact queries from searches.jsonl. Read the returned hits. For multiplicity one they concern Lie root spaces and generalized Lie weight chains, not a rational character weight in a simple algebraic-group representation. For absolute simplicity they concern abstract-group irreducibility, Schur's lemma or the finite-group character criterion. Read the candidate source passages in Mathlib/RepresentationTheory/AlgebraRepresentation/Basic.lean (lines 21--40), RepresentationTheory/FinGroupCharZero.lean (lines 67--95), and CategoryTheory/Preadditive/Schur.lean (lines 96--134). Their algebraic-closedness hypotheses and finite abstract-group scope rule out a one-line specialization to these nodes. They do not prove simplicity after arbitrary field extension. No unavailable service was treated as a negative result.

Searched the whole DAG by highest weight, scalar endomorphisms, absolute simplicity, endomorphism algebra, and the source places 22.2, 22.18 and 4.19. Ran blueprint_refs.py searches for absolute irreducibility, highest weight, endomorphism, simple representation, multiplicity, scalar extension, absolute simplicity and multiplicity one. No existing node covers either required statement. Source places here are Milne theorem numbers, not fictitious Stacks tags.

## Not duplicates

lem-sfb-split-simple-multiplicity-one-weight vs lem-sfb-simple-module-dual-highest-weight: the existing statement assumes an algebraically closed field and includes contragredient classification; this node supplies one multiplicity-one weight over an arbitrary ground field with a split torus.

lem-sfb-split-simple-multiplicity-one-weight vs lem-sfb-primitive-cyclic-weight-bound: the existing statement assumes an algebraically closed field and an already provided cyclic Borel eigenvector; this node obtains a multiplicity-one torus weight from simplicity over an arbitrary field, without those extra hypotheses.

lem-sfb-split-simple-multiplicity-one-weight vs lem-sfb-split-lie-module-classification: the latter is a theorem for Lie algebra modules over Q, whereas this node concerns rational group-scheme representations over any field and character weights rather than differentiated weights.

lem-sfb-scalar-endomorphisms-absolute-simplicity vs lem-per-finite-algebra-hom-scalar-extension: the existing statement concerns the base-change map on Hom for finite-dimensional associative-algebra modules; it does not assert the simplicity of rational group representations under scalar extension.

lem-sfb-scalar-endomorphisms-absolute-simplicity vs lem-sfb-split-simple-absolute-irreducibility: this is a general affine-group criterion with the extra hypothesis that every equivariant endomorphism is scalar. It supplies no proof that the hypothesis holds for the item's split semisimple group. That proof is step 2 of the item, using the distinct multiplicity-one input; neither new statement alone restates or proves the item.

## Review by Q16

I read Milne 22.2--22.4 on printed pp.463--464, 22.17--22.18 on pp.467--468, Remark 4.18 and Proposition 4.19 on pp.90--91, and Exercise 22-1 on p.482. The first new statement is exactly the needed consequence of 22.2/22.18(b), omitting the unnecessary classification, dominance and ordering assertions. Chapter 22a works over a field k with a split reductive group, not just over an algebraic closure; semisimple groups are a special case. The second new statement is 4.19(b), with Remark 4.18's all-algebras definition of endomorphism written explicitly. Both are genuinely non-elementary statements, so both remain statement-only unsplit nodes. The criterion does not impose separability; 4.19(c)'s separability restriction concerns a different assertion about arbitrary semisimple modules.

For step 1 I reread the new multiplicity-one statement and copied its actual conclusion into citations.json. The item supplies precisely the group, field, torus and simplicity hypotheses, and the new node allows characteristic zero. For step 2 the equation for t(f(v)) proves preservation of the full character space for every algebra A. One-dimensionality makes f(v)=av with a in k. I checked the kernel after arbitrary algebra extension by choosing a complement: its basis has independent q-images, which remain independent in an extended basis. This proves rational invariance and justifies applying the original simplicity hypothesis. The nonzero vector v forces the kernel to be V, so q=0. There is no appeal to Schur's algebraically closed-field scalar conclusion, Lie/group comparison, or semisimplicity after extension. This is the elementary linear-algebra argument written in the item, not another node. For step 3 I reread the new criterion and quoted its hypotheses and conclusion verbatim. Affineness and finite type are assumed for G, V is nonzero and finite-dimensional, and step 2 supplies exactly its scalar-endomorphism hypothesis. Its conclusion uses invariance after all K-algebras, as does the item. K/k is arbitrary, including transcendental extensions.

I tested trivial G (the only simple module is one-dimensional), rank-zero T, one-dimensional trivial modules for any G, and the SL2 standard module and its symmetric powers in characteristic zero. The first new node also handles Frobenius-twisted simple modules in characteristic p, since its weights are characters, not Lie differentials. Zero V is explicitly excluded in all three statements. Dropping splitness would fail for the two-dimensional real representation of an anisotropic torus, so it is retained. The scalar criterion's hypothesis is essential: real representations of the constant cyclic group of order three have a simple two-dimensional rotation module with endomorphism algebra C, and become reducible over C; this does not satisfy the criterion. The kernel argument works for any algebra extension, including one with nilpotents.

I checked delivery-errors B--E against the JSON: all objects and simplicity notions are introduced, every non-elementary input is a cited node whose statement gives it, proof_deps is the union of uses, there are no cycles back through the new statement dependencies, new nodes contain no proof sketch, and no result was moved wholesale into a single renamed node. Existing statement dependencies were read and retained. The proof steps have 455, 876 and 611 characters, so none hides an over-2000-character argument. I corrected the Exercise 22-1 page from an initial draft's 481 to the actual printed 482 after checking the page break. The actual item statement was never changed.

## Unfinished work

No part of this one-level split remains unfinished. The two new inputs intentionally remain unsplit for subsequent stage-1 work. Required delivery validation and direct push follow this self-review.
