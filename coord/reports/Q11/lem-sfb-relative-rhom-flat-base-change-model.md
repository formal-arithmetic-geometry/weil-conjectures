# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-rhom-flat-base-change-model.json`: statement item, now split in six steps, unchanged statement; no Mathlib match for the whole assertion.
- `citations.json`: one entry for every step/node citation, copying the complete cited statement verbatim so the hypotheses remain visible.
- `searches.jsonl`: actual Mathlib search results, written by the required search command.

No new DAG nodes and no new Mathlib leaves. The sandbox initially contained only dispatcher briefs, with no item, report, or earlier search log to continue. The current repository item was used as the starting copy. Its original searches, source, statement, ancestry and other metadata have been retained.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and item id, relative RHom/relatively perfect terminology, and the bounded-flat Hom-model notion. The HomComplex and derived internal-Hom infrastructure does not state the whole model theorem with arbitrary base change and transition maps. In particular, the scheme adjunction in `DerivedInternalHomAdjunction.lean` is a different statement; it supplies no attachment here. A sorry declaration would not establish an attachment.

## WANTED

None. All mathematical sources used here are present in the read repository. The inherited reference to `coord/dag-sync.md` points to a file absent in this shared checkout; no alternate state or older blueprint was substituted.

## Audit of the input and route

The imported item agrees with More on Algebra, Tag 0E1U, `lemma-compute-RHom-relatively-perfect`, clauses (1), (2), (a), (b). Its final finite-presentation paragraph is deliberately outside the item. The chain isomorphism and the transition normalization are the explicit termwise comparison in the proof, with its degree-zero consequence written out. There is no false-statement correction or STATEMENT-DISPUTED issue.

Read `GOAL.md`, the chapter record, the unit record, and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` unit and direct-images proof. This is the existing ordinary-algebra prerequisite along the recorded continuity/duality ancestry, not a new route for the constructibility unit. `blueprint_refs.py ancestor` returns None because this long created-node ancestry has no imported blueprint ancestor recorded at its endpoint. I preserved the item's existing null ancestor and its specific place/via description; I created no child requiring a fabricated ancestor. Whole-blueprint searches for RHom, last-one-flat, projective and flat base change found no blueprint assertion equal to this item; `same_as` stays empty.

The substantive reuse checks searched the whole DAG by tags 0E1U, 0653, 0661, 0A66 and 0646, by bounded-above free/projective model terminology, and by projective flatness, finite products of flat modules, and K-projective morphisms. These found all necessary inputs already present. In particular it would be a duplicate to create a new flat-truncation lemma: `lem-pc-module-flat-opcycles-tor-criterion` already states the needed universal-tensor criterion. The scalar exchange is already `lem-sfb-flat-algebra-derived-module-tensor-exchange`, and the projective Hom model is already `lem-pod-projective-hom-evaluation-model`.

The actual Mathlib queries were run through msearch.py, with two semantic phrasings, LeanSearch, Loogle, and grep in Algebra/Homology. Read the returned results. LeanSearch found HomComplex and generic derived/localization/Ext declarations; LeanFinder found IsBaseChange, flat ring-map base change, exact extension of scalars and Ext. None states this item's combination. The grep query had no pseudo-coherent/relative-RHom hit. The Mathlib KProjective source was separately read at `isKProjective_of_projective` and `Qh_map_bijective` to check the existing cited leaf interfaces; these readings are not falsely recorded as msearch calls.

## Not duplicates

No new nodes: there are no new/existing pairs to distinguish. Existing special cases and general tools were cited directly.

## Review by Q11

I read the statement and proof of Stacks Tag 0E1U in `more-algebra.tex`, including the warning supplied by its hypotheses: it is R to S that is flat, while T and later U are arbitrary. I also read Tag 0653 (`lemma-last-one-flat`), Tag 0661 (`lemma-base-change-comparison`, including its preceding counterexample when Tor independence fails), and Tag 0A66 (`lemma-RHom-out-of-projective`), plus Derived Categories Tag 0646 (`lemma-projective-resolutions-exist`) and Algebra Tag 00HI (`lemma-flat-base-change`). I read the statements of every cited DAG node, including the definitions, rather than borrowing constructions from their proofs. No new statement needs a separate source review.

Step 1 uses the precise finite-free existence assertion in `def-pc-ring-pseudo-coherent-complex`. For the target, `lem-weil-pbc-bounded-above-projective-model` applies because testing the given Tor interval with N=R gives cohomology bounded above by b. I checked that it supplies projective terms with that same upper bound and has no Noetherian hypothesis. Projective-flatness and `lem-pc-module-flat-transitive` then give R-flatness of Q, since S is R-flat. `lem-pc-module-bounded-flat-kflat` applies to this bounded-above R-complex. The opcycles node asks for vanishing of ordinary tensor cohomology only in degree a-1 for every module: K-flat computation and the hypothesis give exactly that. It gives the quotient Q^a/im(d^{a-1}), not an image or a kernel. The quotient truncation has this module in degree a and the induced differential, and its quasi-isomorphism is checked on cohomology. This follows the source's truncation construction using projective rather than free terms; nothing in that argument needs freeness of Q. No pseudo-coherence of L is inserted.

Step 2 uses the actual product Hom definition, not a direct-sum Hom for unbounded complexes. The bounds c-n <= p <= min(m,d-n) prove finiteness, and n<c-m proves the lower bound. In finite bases each Hom factor is a finite product of copies of the appropriate F term. The cited finite-product-flat node says this including rank zero. The projective definition recognizes finite free modules as projective, and the projective-Hom evaluation node says the required derived isomorphism for bounded-above projective P and arbitrary target. Thus it applies to every allowed P,F, rather than only the construction made in step 1.

Step 3 uses the flat-algebra tensor-exchange node with the R-module underlying T. I checked that its statement gives the isomorphism in D(S), retains the S-action, and normalizes the augmentation to the derived-to-ordinary map. It requires only R-flatness of S and allows arbitrary complexes and coefficient modules. Both representatives are R-K-flat by the cited bounded-above flat result. Tensoring the acyclic cone of a free resolution augmentation is acyclic by this meaning of K-flatness, so the actual ordinary tensors are the claimed derived models. This is the point where a flatness assumption on T would have been an error; none is used. I do not claim that the bounded-below complex E itself is K-flat or that its ordinary tensor is its derived tensor.

Step 4 writes the inverse coordinate argument for the degreewise map, using finite rank of P, and the differential equality with the sign (-1)^n. Finite degree support was proved in step 2. Thus it does not appeal to an uncited general base-change theorem for Hom out of merely finitely presented modules. The only non-elementary input is the already-read projective-Hom model over S_T, whose hypotheses still hold. The result is an isomorphism of derived objects, not just a list of cohomology isomorphisms.

Step 5 expands cycles and boundaries directly using the total-Hom differential: cycles are chain maps and boundaries are ds+sd. The cited bounded-above projective K-projectivity node applies to P_T. The cited K-projective-derived-Hom bijection states exactly localization's bijection from homotopy classes to derived morphisms; it is not merely full faithfulness of a different embedding. I checked both declarations in Mathlib at their recorded interfaces. This gives every derived morphism, with the additive structure from the chain-map quotient.

Step 6 checks its own hypotheses after the first extension: the flat-module-base-change node gives S_T flat over T and every F_T term flat over T, while projective-flatness and transitivity give the same for P_T. Step 3 can therefore be applied again even if T to U is nonflat. The displayed balancing formula identifies iterated scalar extensions of K and L. Evaluation on p tensor u gives h(p) tensor v(t)u on both sides of the comparison square. Homotopies extend by the same tensor operation, so this equality descends to precisely the Hom groups from step 5. Evaluating a pair of successive algebra maps gives w(v(t)); the identity gives t. Those are explicit checks of the claimed normalization and coherence.

I checked delivery-errors B through E against the files: there are no unsplit children with hidden proofs, undefined new notions, duplicate clauses or relocated whole theorem. Every non-elementary input is an existing cited statement, and all quotes in citations.json are verbatim complete statements. Definitions are used for definitions and existence built into the definition; the actual Hom and tensor theorems have their own citations. All cross-unit non-Mathlib statement tools are declared in split_report.tool_uses and retain the same ordinary-algebra route. Every proof step is under 2000 characters; the longest has no hidden standard comparison, since its tensor formula is written out. No prohibited SGA route occurs.

Small cases checked: K=0, L=0, rank-zero P terms, and an empty interval of contributing Hom factors all give the zero complex and zero Hom group. The construction with a=b has its sole truncation quotient in degree a. Shifts agree with E^n=Hom(P^p,F^{p+n}) and the lower bound c-m. The zero target ring T gives zero tensors. As a nonflat test, take R=S=Z, T=Z/2 and P=Z in degree zero, F=Z in degree zero: the comparison is the identity on Z/2; later U need not be flat over T either. More generally the proof only uses boundedness and finite rank in the degreewise Hom calculation, and uses base flatness rather than flatness of either scalar extension in the derived model calculation.

No numbered return entry was supplied for this item. The defects repaired were the empty proof and undeclared proof dependencies; the statement and statement dependencies remain unchanged.

## Unfinished work

None in this stage-1 split. No Lean was written, compiled, or built. Delivery validation is performed only by the authorized server dry run.
