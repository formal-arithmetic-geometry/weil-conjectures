## Files written

- dag/nodes/sec-six-functors/lem-coef-dualizing-affine-space.json: statement item, split in seven steps; not a Mathlib leaf. No new nodes and no new Mathlib leaves.
- citations.json: every proof-step citation, with the verbatim statement of the node used.
- searches.jsonl: actual queries recorded by msearch.py; the inherited item searches are preserved as received.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag and the dualizing/coefficient notions. SmoothDuality/AffineSpace.lean gives conditional smooth duality from affine-line duality, not this coefficient-changing counit mate. OrientationDatum.lean has coefficient-change data as a field, not a proof of the asserted map. Neither is an attachment.

## WANTED

None. The argument is explicitly agent-written from the named interfaces; the archived blueprint supplies its route but does not contain the scalar-detection argument.

## Corrections and route

The statement is unchanged. The item was an extracted, statement-only node. The blueprint's claim that the Tate rank-one object reduces does not by itself identify the adjoint-defined map with an isomorphism. The proof now derives invertibility of its compact-support image from its defining equation, then uses the existing connected Tate-line detector. It does not assume coefficient compatibility of exceptional adjoints or equality of traces at different coefficient rings. This supplies the missing argument within the affine-space part of the retained parent route. The chosen-adjoint counit normalization is obtained by uniqueness of right adjoints with counits, rather than an arbitrary isomorphism of objects.

The scalar-linearity and connectedness prerequisites are carried by existing nodes, not new restatements of the item. Generic tools from other units are declared in split_report.tool_uses with their purpose. No SGA source is used. The chapter and unit records are unchanged; this extracted node is not the key statement of its unit.

## Not duplicates

No new nodes. Reused lem-coef-connected-tate-line-endomorphisms (same biduality unit), lem-pur-a1-components, both linearity tools, and the ordinary finite Tate and coefficient-extension tools. Whole-DAG searches for scalar endomorphisms, rank-one lines, compact-support linearity and affine connectedness, plus blueprint_refs searches for “Tate scalar”, “dualizing affine”, “compact support linear”, “Tate line” and “scalar endomorphisms”, found those existing interfaces. No new id is proposed.

## Review by Q118

I read coord/delivery-errors.md B–E in both copies, the chapter and unit records, and the parent main-20261015 proof at sec-smooth-purity/sk-lem-sp-tower/lem-coef-finite-dualizing.proof.md. Its second paragraph identifies the affine-space adjoint; its third paragraph supplies the Tate reduction context. I also read the main-20261015 affine-space adjunction and top-trace blueprint statements, the unique-right-adjoint statement, and the statement of every node cited in the seven steps. For the sheaf mechanisms I read Stacks sites-modules.tex Tag 03DI (lemma-extension-by-zero), including its direct-sum formula, and etale-cohomology.tex Tag 03PK (section-kummer), including the roots-of-unity definition. These sources justify the objects and the formula context, not an unrecorded purity theorem. The additional scalar argument is attributed to the agent.

Step 1 uses cor-amb-affine-space-adjunction for the entire ordinary unbounded-category adjunction; det-sp-unique-right-adjoint supplies exactly the inverse, counit-compatible transformation; lem-amb-affine-space-top-trace supplies the invertibility of the coordinate-tower counit including dimension zero. I checked that s is Noetherian and that both finite quotient rings have the same annihilating power of ell invertible on s. Transport through the comparison of adjoints therefore proves invertibility for the chosen counit, rather than assuming the right adjoints were chosen identically.

Step 2 uses lem-asd-finite-etale-twist-line for flatness and rank-one local bases, and lem-pur-derived-change-of-rings for computation on K-flat representatives. It explicitly proves that a flat single complex is K-flat by exactness, that shifts preserve this, and writes mutually inverse balanced tensor maps on a local generator. The generator-change factor e^r is the same on both sides, so no nontrivial descent statement is hidden. In particular B is not assumed flat over A. This is an elementary calculation from the two cited statements, not a new lemma node or a pro-etale/etale identification.

Step 3 uses def-amb-etale-compact-support for the actual composite Rq_* Dj_!. The localized-site node states the small-etale slice equivalence on sites and abelian sheaves; the step explicitly extends its underlying composition/forgetting maps to B-modules by preserving the sectionwise action. The extension-zero node then states B-linearity on the full unbounded derived category, not just on sheaves. The ringed-derived-pushforward node states linearity without exactness of q_*. Its compatible-central-scalar assumptions hold because both scalar maps are constant B sections and the structural map preserves them. Thus the detector's exact B-linear functor hypothesis is established for the actual compact-support functor.

Step 4 uses precisely the component-preimage clause of lem-pur-a1-components. The induction starts at the one-point Spec k; every intermediate affine space is a nonempty separated finite-type scheme in the stipulated purity datum, and its zero section ensures nonemptiness of the next. One component therefore gives connectedness at each stage. This is an elementary iteration of the existing statement, not an invocation of a general irreducibility result with missing hypotheses.

Step 5 uses lem-fix-compact-support-coefficient-change on omega_{P,A}, whose bounded constructible finite-Tor condition is an explicit hypothesis of the item. Its statement gives the actual comparison as an isomorphism. Cancelling the invertible counit in the defining equation gives the displayed formula for F(u), with the direction of c^{-1} checked. A functor preserves the inverse equations for the A-counit; no Tor bound on the A-module B is needed.

Step 6 uses the invertibility-detection clause of lem-coef-connected-tate-line-endomorphisms, not just its scalar-endomorphism computation. Its k, N, B, nonempty connected Y, shifted Tate line, B-linear G and G(L) isomorphic to B_s hypotheses are all supplied explicitly by steps 1–4. Conjugation turns u into an endomorphism of the exact shifted Tate line required there. The detector is already in the DAG; I did not introduce another version of it.

Step 7 uses the top-trace statement's identity adjunction in dimension zero and the coefficient-comparison node's canonical tensor construction. For the identity functor this tensor comparison is the literal tensor-unit map, so the equation reads u=1 after the specified identifications. This is a direct identity calculation, not a coefficient-trace compatibility theorem.

I checked r=0, r=1, identity coefficient reduction m=n, and nonflat quotient reduction n>m. In all cases the conjugated scalar argument remains valid; there is no assumption that compact supports reflect arbitrary isomorphisms. The general detector also permits the zero ring, although the finite coefficient datum here is nonzero. The empty-scheme pitfall is excluded by the explicit zero-section/nonempty argument. All proof steps are below 2000 characters, and no step hides a new comparison theorem: tensor maps and open-site transport are written explicitly. All quotes in citations.json are verbatim whole statements copied from the live node files.

## Unfinished work

None for this one-level stage-1 split. Existing cited nodes retain their own status and proofs. No Lean was written, compiled or built. The required remote delivery checks and delivery outcome are recorded below after they finish.
