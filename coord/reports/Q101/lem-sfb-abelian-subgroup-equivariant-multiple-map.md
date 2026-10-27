## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-abelian-subgroup-equivariant-multiple-map.json: statement, split in eight steps using existing nodes; Mathlib searches found no match.
- citations.json: all 22 step-to-node citations, each backed by the verbatim full statement actually read.
- searches.jsonl: six fresh searches made by msearch.py, preserving their actual outputs. Inherited searches remain in the item unchanged.

No new nodes, no new Mathlib leaves. No Lean written or compiled. Only sandbox files written.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id, Rosenlicht, equivariant multiples, abelian subgroups and the abelian-variety directory. There is no project declaration stating all clauses with a finished proof. Upstream declarations containing sorry were not treated as proofs.

## WANTED

None. The proof source is locally available.

## Corrections and route

The statement is unchanged. In particular n is positive, the equality is a scheme-morphism equality tested on arbitrary schemes, and phi need not preserve the identity. No affineness, properness or commutativity of G has been added. Milne's printed statements 8.22 and 8.23 merely say “an integer”; his proof gives the positive degree of a separable residue extension, or 1. The existing torsor node explicitly includes positivity, so there is no dispute to repair.

Milne Proposition 8.23 uses the quotient generic torsor, Lemma 8.22, rational-map spreading, 8.18, and dense equality. These are exactly the steps here. The quotient need only be the homogeneous quotient scheme; constructing its group law is unnecessary. In particular we do not invoke Chevalley decomposition, an almost-complement, or the parent Rosenlicht node, which would be circular. The only use of centrality beyond the given inclusion is to prove that A is commutative from injectivity on test schemes; no abelian-variety commutativity theorem is silently imported.

Read the current latest blueprint sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, clause (3), under sec-six-functors-basics. This is a supporting algebraic-group prerequisite in the item's recorded via chain, rather than a separately stated current blueprint theorem. blueprint_refs.py ancestor prints from.node = None; that inherited value is retained and its existing precise Milne place retained. Whole-DAG and blueprint searches for Rosenlicht, abelian subvariety, positive weight, torsor, and rational-map extension found no blueprint duplicate. Existing homogeneous quotient, torsor-positive-weight, Weil extension and local spreading nodes were reused. No unit realization fields are changed: this is not the unit's key node.

Generic off-unit tools are declared in split_report.tool_uses, with their exact purposes. In particular the trace-formula-named smooth geometric-fibre integrality node states a generic scheme fact, and is used only for that fact. Neither the trace formula nor Poincare duality is assumed. No SGA source is used.

## Not duplicates

No new nodes were created. The potential split lemmas already exist as lem-sfb-algebraic-group-homogeneous-quotient, lem-sfb-commutative-torsor-positive-weight, lem-sfb-weil-extension-to-abelian-variety and lem-sfb-local-ring-map-spread. The commutative quotient node would be inapplicable to noncommutative G, so the general homogeneous quotient is used instead.

## Review by Q101

I read Milne, Algebraic Groups (iAG2017), printed pp.152–153, including the complete proofs of 8.22 and 8.23 and the statements 8.16–8.21, and printed pp.104–105, including the torsor quotient 5.27 and general quotient 5.28. No new node has a separate source to check. I also read the cited generic facts in the local Stacks sources: varieties.tex 04KV (lemma-geometrically-connected-if-connected-and-point), 056S/056T (smooth regular/geometrically normal); properties.tex 033M/033N (normal schemes decompose into integral components); more-morphisms.tex 057J (last geometric-fibre integrality argument); morphisms.tex 0BX6 (lemma-morphism-defined-local-ring); descent.tex 02VL (lemma-descending-property-smooth); and the precise relative separated equality declaration in Mathlib AlgebraicGeometry/Morphisms/Separated.lean:295–313. Sources are identified by tags and labels, not unstable section numbering.

For each step I opened each cited node and read its statement, not its proof, before using it:

1. lem-sbc-connected-rational-point-geometrically-connected says a connected scheme with a rational section is geometrically connected. Both identities supply the sections and nonemptiness. lem-trf-smooth-connected-fibre-normal-integrality then gives integrality after every field extension; its nonempty geometrically connected smooth fibre hypotheses are exactly met. Commutativity is proved directly from the given centrality and subgroup monomorphism, on affine test schemes and then by gluing, so no uncited non-elementary rigidity theorem enters.
2. lem-sfb-algebraic-group-homogeneous-quotient allows nonaffine, noncommutative G and gives separated finite-type Q, a flat surjective finitely presented p, and the coset criterion for EVERY test scheme. The natural unique difference a from that criterion supplies the torsor kernel pair. lem-galois-yoneda-fully-faithful states the required full natural-transformation bijection, rather than merely faithfulness; it therefore really turns the natural inverse into a scheme morphism. No pointwise-only criterion is substituted.
3. lem-pc-proper-base-change (2) gives the smooth projection after identifying the torsor kernel pair. lem-trf-smooth-fpqc-base-descent applies to p pulled back along itself: p is flat, surjective and quasi-compact. lem-sbc-smooth-flat-surjective-source-descent applies because p is also locally finitely presented and G/k is smooth; it gives Q/k smooth, not merely p smooth. lem-weil-pbc-smooth-scheme-over-field-regular gives Q regular. Surjectivity transfers nonempty connectedness to Q, so lem-sc-regular-connected-integral applies. None of these nodes is only a definition of the property needed.
4. lem-weil-pbc-flat-morphism-base-change and lem-weil-pbc-surjective-base-change give a faithfully flat nonempty generic fibre. The torsor identity is pulled back explicitly. Finite presentations remain finite after tensoring on affine charts. lem-pc-proper-base-change gives A_K proper AND smooth, so it is separated finite type; the geometric integrality from step 1 and directly proved commutativity meet every hypothesis of lem-sfb-commutative-torsor-positive-weight. That node permits arbitrary, possibly imperfect K and requires no K-point of the torsor. Its displayed equality is an equality of morphisms and it gives a strictly positive n.
5. I wrote the domain localization argument identifying the function field of V with that of G; this is not an unstated generic-fibre spreading lemma. The local-ring morphism is then spread by lem-sfb-local-ring-map-spread. The source G is locally Noetherian by lem-weil-pbc-smooth-scheme-over-field-regular and A is locally finite type, exactly its hypotheses. The resulting open contains the generic point and is dense. lem-sfb-weil-extension-to-abelian-variety applies because G is smooth, nonempty integral, separated and finite type and A is abelian. It supplies the global morphism phi.
6. The rational-map extension alone does not give equality with the ENTIRE generic-torsor map. I added this step to prevent that gap: the maps V to A_K agree on Spec k(G), whose image is dense in reduced V. lem-sfb-relative-separated-dominant-ext states precisely equality after a dense-image morphism into a reduced source with separated relative target. It gives the equality on V without a missing injectivity or spreading assertion.
7. lem-pc-proper-base-change and lem-trf-smooth-composition give smoothness of G times A over k; sbc-lem-smooth-geometrically-reduced then gives reducedness. lem-sc-geometrically-irreducible-product applies to the geometric integrality established in step 1 and gives irreducibility. The identity section of the projection supplies surjectivity; its composite with p is dominant. The generic fibre therefore contains the generic point and has dense image. This is a localization argument, not an assertion that the generic fibre is open or that equality of k-points suffices.
8. After step 6 the torsor equality really gives equality of the two global morphisms restricted to X_eta. Apply lem-sfb-relative-separated-dominant-ext a second time, now with reduced X=G times A and separated A/k. This proves the formula as a scheme-morphism equality, hence on all T-points, including nonreduced T. No division by n, separability of [n], or normalization at the identity is used.

Small cases checked: A=0 permits the zero map; A=G (necessarily commutative) permits n=1 and the identity, and the generic quotient can be a point; G=A times an affine group permits projection. Positive characteristic dividing n is allowed because no etaleness or inverse multiplication is used. The quotient and generic torsor are nonempty, so the torsor lemma cannot be applied vacuously. The argument handles a zero-dimensional quotient as well as positive dimension and does not falsely infer that a torsor over k(Q) has a rational point.

Against delivery-errors B–E: there are no new nodes to duplicate, restate clauses, or leave unsplit with proof sketches. Every non-elementary use has a node, and each of the 22 citation quotes is verbatim from its statement. Group-scheme, generic-fibre and product identifications are written out. All eight steps are under 2000 characters; no long step hides a lemma. The statement and dependency notions are retained, no noncanonical data is sorried, and no cycle through the parent construction is introduced. The proof follows the source, rather than moving the item into a new equivalent lemma.

## Unfinished work

None in the stage-1 split. The cited existing unsplit or sorried prerequisites remain their own independent DAG items; this delivery claims no Lean proof.

## Validation

Server review_split passed before writing this report: 0 new nodes; inherited unit realization is not yet recorded. The required full delivery dry run is run after the report is written.
