# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-ideal-twist-vanishing-implies-ample.json`: repaired split with eight proof steps; statement unchanged; no Mathlib match.
- `citations.json`: twenty verbatim step/node statement quotations.

No new nodes and no new Mathlib leaves. The rejected `lem-trf-twisted-closed-point-affine` was never landed and is excluded from this repair; its returned text is retained as `returned-twisted-closed-point-affine.json.bak`. The previous logged searches remain in `searches.jsonl`, and the item's previous search records are retained. The final report below replaces the inaccurate review of the former four-step proof.

## Attachments

None. Read-only searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint tag, item id, `quasi-compact-h1-zero-invertible`, ideal/twist, and ampleness/cohomology terminology found no project declaration proving this criterion. The hits concern existing ampleness, basic opens or Serre vanishing in other settings. No Lean was written and no compiler or Lake command was run.

## WANTED

None. The full mathematical source is present in the repository.

## What was wrong and what changed

D1/D2: the returned proof invoked a new statement equivalent to the ampleness criterion via the closed-point covering argument. Its essential reduced-ideal and twisted-H1 construction was deferred. The repaired item itself now constructs I and J, checks the tensor sequence in local generators, glues the quotient section, lifts it using H1(J tensor L^n)=0, and identifies the nonvanishing locus with a principal open in an affine trivialization. There is no replacement child lemma.

F2/F5: the previous report described four construction steps that were absent from the delivered node. This report reviews the eight steps actually written in the repaired node. The earlier review was inaccurate; the new review explicitly distinguishes the statements used from the local calculations now supplied.

Bibliography: the supporting result is Stacks Tag **0B5P**, `coherent.tex`, `lemma-quasi-compact-h1-zero-invertible`, not Tag 01XF (`lemma-quasi-compact-h1-zero-covering`, the untwisted affineness criterion). All proof-step and proof-origin references now use 0B5P. Tag 0B5U, `lemma-vanshing-gives-ample`, is the correct source for the unchanged item statement. This is a citation correction, not a statement dispute.

I compared the retained returned item with the current repository item: the latter still has the same statement, empty proof and unsplit status. The repair starts from that current repository record, preserving its created/chapter/unit metadata, pointers and blueprint ancestry, and restores the recorded earlier searches. The delivery tool rebases the repaired files on the current server base. The rejected child's search history remains available but is not presented as a new search or a leaf.

## What could not be finished

Nothing in the one-level split remains unfinished. The existing cited nodes keep their own statuses; no closure or independent proof of those nodes is claimed.

## Review by Q88

I read `coherent.tex` Tag 0B5U, including the full three-part criterion and its (3) => (1) citation, then the entire proof of Tag 0B5P, and `schemes.tex` Tag 01J3, `lemma-reduced-closed-subscheme`, including its explicit vanishing ideal formula and quasi-coherence argument. The item assumes precisely the Noetherian ring, proper map to its spectrum, invertible O_X-module, and one positive vanishing twist for each quasi-coherent ideal required by 0B5U(3), and concludes its absolute ampleness. The supporting 0B5P proof needs only quasi-compactness; using the stronger item hypotheses therefore adds no assumption. There are no new node statements to check against a source.

I also read the chapter and unit records and the current main-20261015 `sk-i-curve-zero` and `lem-trf-local-term-locality` proofs. The criterion is an imported supporting tool reached through the inherited 0B5X curve-degree ancestry, not a claim that the unit directly states an ampleness theorem. The repair retains that ancestry and follows the same Stacks route. Generic off-unit tools are declared in `split_report.tool_uses`; no unit or chapter record is changed.

Step 1: I opened `pqf-lem-proper-basic`. Its statement explicitly says that proper over affine implies quasi-compactness of X. That is exactly the input used; no Noetherian or Jacobson consequence is taken from it.

Step 2: I opened `lem-pc-invertible-common-free-generator`: it gives an affine U inside an arbitrary W with free generators for two invertible modules. Setting both modules to L and W=X satisfies all hypotheses and supplies the required e. I opened `lem-weil-pbc-reduced-induced-closed-subscheme`: clause (1) supplies the quasi-coherent ideal for each closed subset and its actual sectionwise vanishing formula. The closed-point assumption makes Z union {x} closed. That formula gives J subset I, I|_U=O_U, and I=J on X minus {x}; at x it gives precisely the kernel of O_{X,x} -> kappa(x). Thus it says more than merely existence of a closed subscheme, and supplies every reduced-ideal fact used here.

Step 3: I opened `def-weil-sheaf-of-modules-category`, whose statement provides abelianness, sectionwise kernels and sheafified sectionwise cokernels. It supports forming Q=I/J and its short exact sequence. I opened `def-pur-sheaf-tensor-product`, which defines the sheafified tensor and its powers, `def-sc-invertible-module`, which supplies local rank-one generators, and `def-weil-pbc-ample-invertible-module`, whose statement explicitly includes invertibility of each tensor power. The step does not infer exactness from a definition of flatness. It writes mutually inverse local maps F tensor M_n <-> F and checks the maps in both the quotient sequence and I tensor M_n -> M_n become the original maps. This is an elementary local identity calculation using the cited kernel/cokernel description; no tensor-exactness lemma is left implicit.

Step 4: I rechecked the statements of the reduced-ideal, module-category and tensor-definition nodes. The construction now glues on the open cover U and X minus {x}; the latter is open because x is closed. On their overlap Q=0 since I=J, so the two displayed sections agree. The sheaf axiom supplies q_n. Its value at x is explicitly the class of e^{tensor n} modulo m_x, so no global identification Gamma(X,Q tensor M)=A/m is silently assumed. I checked that n is chosen using J (the kernel ideal), not I, and that only one positive n for J is needed. This local gluing and evaluation are elementary from the statements already cited. The untwisted `lem-pqf-h1-closed-point-ideal-quotient` is deliberately not cited: its statement only tests global lifts and does not supply this twisted quotient-section identification.

Step 5: I opened `lem-sc-ringed-space-module-sheaves-enough-injectives`, which states both abelianness and enough injectives for O_X-module sheaves, not merely abelian sheaves on an etale site. I opened `lem-weil-pbc-right-derived-universal-delta-functor`: its statement gives exactness for every short exact sequence and explicitly R^0 v naturally isomorphic to v. `pqf-def-cohomology` identifies the relevant H1 with the right derived functor of module global sections. Gamma is additive and left exact by the sectionwise kernel description. Thus all hypotheses for the cited abstract theorem hold in this Zariski module category. Exactness and H1=0 give an actual section lift of q_n, then its image s under the inclusion, without a hidden comparison of coefficient categories or an unsupported R0 identification.

Step 6: I reopened the reduced-ideal formula and the nonvanishing definition. At x the residue is 1 in a generator coordinate; outside U every local coordinate of s lies in I and therefore has zero residue. This proves containment in U even for a nonreduced X. Within U, writing s=f e^{tensor n} gives exactly the unit-germ principal open U_f. I opened `lem-weil-pbc-affine-ideals-closed-subscheme`; its statement (0) explicitly asserts that U_f is affine. The affineness claim is taken from this Mathlib leaf, rather than from the definition of a scheme or from another node's proof.

Step 7: I opened `lem-sc-scheme-sober`, which states uniqueness of a generic point of every irreducible closed subset; the step explains the elementary deduction of the Kolmogorov condition from uniqueness of the closure of a point. I opened `lem-sc-quasi-compact-kolmogorov-closed-point`, whose statement applies directly to every nonempty closed subset of a quasi-compact Kolmogorov space and returns a point closed in X. Its conclusion has exactly the ambient closedness needed for the contradiction. `def-weil-pbc-ample-invertible-module` explicitly gives openness of each X_s. Consequently the application has its quasi-compactness and separation hypotheses verified. The old closed-subset-quasi-compactness citation is unnecessary for this stronger direct formulation and has been removed.

Step 8: I checked both clauses of the actual ampleness definition: quasi-compactness comes from step 1, and W=X gives the positive-power affine neighbourhood for every point. This is an elementary unpacking of the stated definition.

For B1-B10, no new node, hidden statement-only proof, unsupported Mathlib leaf or fabricated search is introduced. I searched the whole DAG for 0B5U, 0B5P and the ampleness criterion and ran `blueprint_refs.py search` for ampleness and the criterion; no blueprint node states this item. The existing reduced-ideal, local-generator, derived-functor and affine-principal-open nodes are reused. `blueprint_refs.py ancestor` confirms the retained `lem-trf-local-term-locality` ancestry. The old new-node duplicate comparisons are obsolete because no such node is delivered.

For C1-C8, every non-elementary input above is supplied by an opened node statement, and the local exactness/gluing/coordinate arguments are written explicitly. The twenty step/node quotations in citations.json are verbatim statement text. The dependency union equals proof_deps, every used node is unmerged, and a traversal of every proposed dependency closure found no path back to the item. The generic tool uses are declared with their purposes; none substitutes a different proof of the unit's local-term theorem.

For D1-D5, the proof carries the reduced-ideal and twisted-H1 construction itself. No clause is moved into a new child, and no source phrase such as “in the same way” is left as the argument. Each proof step is below 1000 characters, hence below the 2000-character review threshold, and none conceals a comparison or an additional standard lemma.

For E1-E7, I checked the empty scheme (no closed point needs choosing and the empty union equals X), X affine with U=X (Z empty, I=O_X and J the reduced closed-point ideal), a nonreduced affine test X=Spec(k[epsilon]/epsilon^2) with its unique closed point (J=(epsilon), quotient k, residue 1 still nonzero), and a nontrivial line bundle (only its generator on U and local generators elsewhere are used, never a global trivialization). No separatedness of U intersections, Jacobson property, coherent-ideal replacement, eventual-in-n vanishing, or global triviality is assumed. Properness supplies only quasi-compactness; Noetherianity remains in the unchanged statement. No source mathematical error or statement dispute was found.

The preliminary server `review_split` check passes with zero new nodes. The final full dry run and delivery are performed after this report is written.
