## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-biproduct-cokernel-cofork.json`: statement item, now split into four elementary universal-property calculations; Mathlib searches found no exact match or one-line specialization.
- `citations.json`: verbatim statements for every step/node citation.

No new nodes; no new Mathlib leaves. The item's statement, source, created record, chapter, unit and blueprint ancestry are retained.

## Attachments

None. The previous attachment was rejected because the supplied source then lacked the file. In the present read clone `WeilConjectures/SixFunctors/ProEtale/Adic/ZModPowGLLift.lean` exists: lines 50–74 define `CategoryTheory.Limits.isColimitCokernelCoforkBiproductMap`. Its proof handles an indexed family of chosen biproducts by componentwise cokernel descent. As explicitly instructed, this delivery does not propose ATTACH again and does not rely on this project declaration as a proved dependency.

## WANTED

None.

## Problems found and corrections

The item had an empty proof. I supplied the zero-composite calculation, both injection squares, explicit component factors and their sum, the factorization equation, and the uniqueness calculation. Its source identifies an auxiliary calculation extracted by an agent from the finite-direct-sum assertion in Stacks Tag 01PJ, not a verbatim categorical theorem in that tag. The proof is therefore explicitly marked agent-written, with the defining identities sourced to Homology Tags 0103, 0104 and 0106. No statement dispute or route error was found.

The present Mathlib search results are not the previously proposed project declaration. `biprod.isCokernelInlCokernelFork` and its right analogue (BinaryBiproducts.lean lines 884–910, read) concern the cokernel of a biproduct injection. `BiproductToPushoutIsCokernel.isColimitBiproductToPushout` (Abelian/Basic.lean lines 617–644, read) concerns the relation map for a pushout. `kernelCokernelCompSequence` (Abelian/DiagramLemmas/KernelCokernelComp.lean lines 70–113, read) concerns a triangular composition diagram, not this block diagonal map. The other search phrasing returned coequalizer/cokernel equivalences and general colimit constructions. These do not provide a one-line specialization of this item under its additive-category hypotheses. All searches added to the item were run through msearch.py and recorded in searches.jsonl; the inherited search history remains intact.

## Unfinished work

None for the natural-language split. No Lean was written, and no compiler, Lake or build command was run.

## Not duplicates

No new nodes were created. DAG searches for block-diagonal cokernels, coproduct cokernel coforks and the proposed declaration, and whole-blueprint searches for `block diagonal` and `cokernel cofork`, found no blueprint theorem stating this item. The blueprint ancestor command confirms `lemma-weil-pbc-h1-constructible-representation`. Its current main-20261015 proof and the current sk-thm-p1 statement were read; this remains the finite-presentation auxiliary branch and replaces no unit-level step.

## Review by Q75

I read Stacks properties.tex at `lemma-directed-colimit-diagram-finite-presentation` (Tag 01PJ), specifically the proof's use of the finite direct sum of finitely presented modules. I also read homology.tex at `remark-direct-sum` (0103), `definition-additive-category` (0104), and the cokernel clause of `definition-kernel` (0106), checking the tags against tags/tags. There are no new nodes requiring additional sources.

For Step 1 I opened both cited definition nodes. The additive-category statement explicitly supplies all five biproduct relations, and the preadditive-category statement explicitly supplies bilinearity. Expanding the two block maps gives the displayed zero composite, and evaluating on each injection gives both commuting squares. No theorem about preservation of cokernels is assumed.

For Step 2 the same two statements justify restrictions to the summands and the sum defining h. The cokernel hypotheses are the item's own explicit universal properties: f_k a_k vanishes because f a does, so they apply with the same arbitrary target T. This gives h_k without assuming all cokernels exist or assuming the category is abelian. The equalities h i_k^C=h_k follow from the same injection/projection relations.

For Step 3 I re-read the bilinearity and decomposition-of-identity statements cited there. Substitution of h_k c_k=f_k computes h c=f with the actual stated map c, so there is no unidentified isomorphism or implicit transport of the projection map.

For Step 4 I checked the cited additive-category statement's decomposition of the identity on C_1 plus C_2. The competitor h' restricts to factors through each original c_k, whose uniqueness is an explicit hypothesis of the item. These restrictions coincide with h_k, so the decomposition proves equality of the competitors. This supplies uniqueness for every T, not merely existence or an isomorphism of cokernel objects.

Against delivery-errors B: no new statement-only nodes or missing notion definitions; the original self-contained statement is unchanged; TeX uses single mathematical backslashes; no unsupported Mathlib leaf is claimed, and search evidence is genuine. Against C: every citation was opened and its exact statement copied to citations.json; no result is taken from a cited proof, and the only mathematical inputs are the stated hypotheses and two definition nodes. Both dependencies are existing Mathlib/closed tools and cannot introduce a new cycle or a unit-route departure. Against D: the argument stays in the item, with explicit equations instead of new nodes restating its clauses. Against E: I checked all maps' domains and codomains, composition order (declared ordinary composition), and the arbitrary target T. The proof uses neither abelianness nor ambient existence of all cokernels. For small cases: a_k=0 allows c_k=id, when the construction gives h=f; a_k=id allows C_k=0 and c_k=0, when f_k=0 and the zero factor is forced; taking either entire summand to be zero reduces to the other cokernel property. A cokernel of multiplication by 2 in abelian groups gives the expected quotient map componentwise. None requires cancellation of a_k or an unprovided epimorphism assumption. Every proof step has fewer than 600 characters, so no long step hides a separate comparison lemma.


## Repair of the 2026-10-22 return

The return identifies the reviewed delivery head as `44235e12699` and says its side completion had not been promoted to the live queue DAG. I retained that delivery's four-step proof, report, sources, and all six logged search results. I compared the retained item to the current shared read clone: its statement, statement dependencies, source, created record, chapter, unit, and blueprint ancestry agree; the live item still has status `unsplit`, no proof, and only the five inherited Mathlib searches. This repair supplies the retained proof against that current unsplit item rather than treating the side completion as a live completed node.

I re-opened the entire current statements of both cited nodes, `def-weil-additive-category` and `def-weil-preadditive-category`. Both remain Mathlib leaves. Their statements exactly match the full verbatim quotations retained in citations.json: the former supplies the four projection/injection equations and decomposition of the identity, and the latter supplies bilinearity. Thus no changed mathematical hypothesis or definition requires a new argument. I did find one citation worth making explicit on this re-reading: Step 4 distributes h' over the sum expressing the identity, so it now explicitly cites the preadditive-category node as well as the additive-category node. I regenerated all eight step/node quotation entries from those current statements. The proof dependency union remains the same two existing nodes. No new nodes or Mathlib leaves are introduced, and no target statement is changed.

I re-read Stacks homology.tex at Tags 0103, 0104 and 0106 and properties.tex at Tag 01PJ, and rechecked the source labels against tags/tags. The four steps still prove the zero composite and both injection identities, construct the unique component factors, verify their sum factors the actual block map, and prove uniqueness. In particular the last calculation uses bilinearity explicitly, with no unstated cancellation or existence of other cokernels. The zero-map, identity-map and zero-summand tests in the signed review still apply. All steps are below 600 characters and contain only the displayed universal-property calculations.

The required initial dry run completed successfully at `af93c862db5`. The delivery tool fetches `origin/sheaf-dag` and overlays only worker-owned fields on its current node; it therefore performs the requested rebase while preserving current maintainer metadata. The proof and citation clarification above makes this a revised delivery, not an unchanged re-push. A final dry run and push follow this repair.
