# Stage-1 report: lem-sfb-relative-fp-module-fibre-product

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-fp-module-fibre-product.json: item split into eight proof steps, statement and statement dependencies retained.
- citations.json: thirteen verbatim statement quotations, one for each step/node citation.
- report.md: this report. searches.jsonl is the search command's actual log; write_split.py is sandbox-only preparation code.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves. The proof reuses existing nodes, including four existing Mathlib theorem leaves and the tensor and finite-presentation definitions. No new definition or restated clause is introduced.

## Attachments

None. Read-only searches of lean/WeilConjectures by the item blueprint tag and by relative finite presentation, patched modules, fibre/fiber products and Milnor terminology found no project declaration giving this statement. The Milnor matches concern derived inverse limits, not ring-pullback patching.

## WANTED

None. All source arguments used are present in literature/stacks-project/.

## Changes and errors

The imported statement is correct: it is precisely the flat-ambient-algebra case of Stacks Tag 08KP, lemma-relative-finitely-presented-module-over-fibre-product. The source's first reduction to a polynomial ambient algebra is unnecessary because this item's S is already R-flat. I did not add finite presentation of S over R or any finiteness condition on I. No statement dispute, source error, changed statement dependency, or change to the unit/chapter route is needed.

The item's existing searches were retained. Five additional Q100 searches were run through msearch.py and read, with exactly their logged queries and results appended to mathlib_searches. Both semantic phrasings found base-change/transitivity/flatness statements, not this gluing assertion. Loogle returned finite presentation after tensor extension and local-ring freeness; grep found flat tensor functors and ring pullback definitions. I read the finite-presentation source and the ring-pullback source; these results do not make the item a Mathlib leaf. All services answered successfully.

## Blueprint and route

Read the chapter/unit records and the latest blueprint's sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. This is the existing module input to the recorded nodal-curve/moduli support chain of direct-image preservation, not a replacement route for a unit. The direct-images proof is clause (3). The existing item's detailed from.place is retained and described in split_report.blueprint. blueprint_refs.py ancestor reports a null blueprint ancestor for this imported support chain; the item already has that value, and no new node requiring an ancestor is made. Whole-blueprint searches for 08KP, 08IH, finitely presented module, and fibre-product found no blueprint node stating this assertion, so same_as remains [].

The three patching nodes used are already in this item's unit. The finite-kernel theorem, flat-quotient tensor theorem, tensor right exactness, tensor-over-quotient theorem and definition nodes used from elsewhere are Mathlib leaves, hence no off-route non-Mathlib tool is needed.

## Not duplicates

No new nodes. In particular, I reused lem-sfb-finite-module-fibre-product-patching (0D2H), lem-sfb-flat-module-fibre-product-patching (0D2I), and lem-sfb-patched-module-base-change (07RU), instead of creating relative versions: the flat ring square lets each existing statement apply directly. The kernel finiteness input is already lem-trf-finite-presentation-surjective-module-kernel (0519). There is no new-id/existing-id pair to compare.

## Review by Q100

I read the complete proof of 08KP in more-algebra.tex, particularly its paragraph beginning “Assume B′ → D′ is flat”, and read its prerequisites 0D2H, 0D2I, 07RU and the relative finite-module argument 08IH. I also read algebra.tex's 00HL (lemma-flat-tor-zero) and 0519 (lemma-extension, especially part (5)), and opened every cited DAG node's statement. No new node has a separate source to review.

For step 1, 0D2I's second assertion explicitly gives the canonical comparison for every flat R-module; applying it to S uses exactly the flatness in the item's hypotheses. Its explicit map respects multiplication, yielding a ring square. The tensor-right-exactness node explicitly gives surjectivity and the kernel as an image after tensoring I → A′ → A → 0. That image is IS_A′ since pure tensors map to multiples of the image of I. This verifies the surjective leg required by both later patching applications.

For step 2, I checked balancing and both inverse formulas for the tensor identifications, including naturality on pure tensors; these are short universal-property computations, not an additional comparison lemma being asserted without an argument. The cited quotient-tensor node explicitly identifies tensoring with a ring quotient with quotienting the module, giving the M′/IS_A′M′ form required by the patching nodes. This step uses that cited theorem and the written elementary balancing calculations, not an uncited identification.

For step 3, the finite-presentation definition supplies a surjection from a finite free module and hence finite generators. The 0D2H node states finite generation of a patched module with no flatness or ideal-generation condition, exactly what is taken from it over the new square. For step 4, 07RU explicitly gives both canonical component isomorphisms and their naturality; tensor right exactness gives surjectivity of both base-changed q maps. The basis tensor formula and equality of the two reductions on each p_i were written out, so the common q_A is specified rather than assumed.

For step 5, the existing 0519 Mathlib leaf explicitly states finite generation of the kernel of a surjection from a finite module to a finitely presented one. I checked both source modules are finite free and each target has the required finite presentation over its own component ring. No Noetherian assumption is used. For step 6, 00HL explicitly gives short exactness after arbitrary tensoring when the quotient is flat. Here those quotients are N over B and M′ over A′, exactly the hypotheses of the item; there is no assumption that N is flat over S_B or M′ over S_A′. The kernel comparisons use the canonical inclusions, and I checked their S_A-linearity and the tensor-balancing identifications. This supplies the compatibility required to patch the kernels, not merely their separate finite generation.

Step 7 is the elementary restriction of the already obtained coordinatewise ring identification to vectors annihilated by q. I verified the inverse explicitly: equality in K_A implies equality in S_A^n, and vanishing of both components implies vanishing in the literal pair module P. It uses no hidden flatness-of-kernel or kernel-base-change theorem. In step 8 the same 0D2H statement now applies to the finite kernel components and the isomorphism of step 6; finite generators of K then give the written finite presentation by the definition node. Thus the proof is an argument for the item, not an application of a newly restated clause.

I tested I=0 (the A′ leg is an isomorphism), A=0 (the square is a product ring), N=M′=0 (n and m may be zero), and the zero ambient ring. Each construction and cited theorem permits these cases. I checked that B → A need not be surjective, that the quotient identification uses only A′ → A, and that no ideal is assumed finitely generated. Against delivery-errors B–E: no new statement-only-node or duplicate issue arises; all non-elementary facts are explicit node citations; the citations take statements, not proofs, and citations.json quotes them verbatim. All eight steps are below 1000 characters, so no step exceeds the 2000-character hidden-lemma review threshold. The two tensor formulas and kernel inverse are genuinely routine computations written in full. No source or SGA route prohibited by the brief is used.

## Unfinished work

None in this one-level split. Existing unsplit patching inputs remain their own DAG items. No Lean files were written and no compiler or build command was run. Delivery validation and push are performed with the authorized launcher tool.
