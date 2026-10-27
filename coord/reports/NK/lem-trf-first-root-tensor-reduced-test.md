# Stage-1 report: lem-trf-first-root-tensor-reduced-test

## Files written

- dag/nodes/sec-trace-formula/lem-trf-first-root-tensor-reduced-test.json: existing statement split into six proof steps, with no change of statement or statement dependencies. Not a Mathlib leaf.
- citations.json: one verbatim statement quotation per node citation per step (12 entries).
- searches.jsonl: actual msearch.py records; existing upstream mathlib_searches are retained in the item.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. All required supporting statements already exist; elementary calculations stay in the proof.

## Attachments

None for the item. The project source Algebra.isSeparableExtension_of_forall_isReduced_tensorProduct (WeilConjectures/FieldTheory/GeometricallyReducedExtensionSeparable.lean) assumes reducedness for every field extension, so does not attach to this item. Its proof is source material only and is not cited as a theorem giving the weaker first-root hypothesis. The existing tensor-reducedness node already records Algebra.isReduced_tensorProduct_of_isSeparablyGenerated (WeilConjectures/FieldTheory/SeparablyGeneratedTensorReduced.lean); no existing node was edited.

## WANTED

None. The actual algebraic proof and all its source inputs are in the local Stacks algebra.tex. No BGR analytic claim is proved or required in this delivery.

## Problems found and changes

The item was statement-only, not an earlier delivery to repair. Its statement agrees with Tag 030W, lemma-characterize-separable-field-extensions, (3) implies (4), with geometric reducedness expanded. No statement dispute or correction is needed.

The proof runs through finite p-power independence, then through finitely generated intermediate fields. In particular it does not assume the arbitrary extension F/k is itself separably generated, and does not confuse separability of an arbitrary field extension with algebraic separability. The completion and norm arguments belonging to the parent node are outside this item.

## Not duplicates

No new nodes. I searched the DAG for 030W, first-root, p-independence and tensor-reducedness statements, and searched the whole imported blueprint with blueprint_refs.py for 030W, p-power independence, root and geometrically reduced. I reused lem-weil-pbc-p-power-independence-separably-generated and lem-weil-pbc-separably-generated-tensor-reduced rather than introducing duplicate statements. The reverse implication in lem-weil-pbc-geometrically-reduced-extension-separable cannot prove the present implication under its hypotheses.

## Mathlib searches

I ran msearch.py with LeanFinder, Loogle, grep and LeanSearch, read the actual returned hits, and ran a second semantic phrasing plus a FieldTheory grep. The current records are in searches.jsonl and copied without changing query strings into the item's mathlib_searches. All services answered. GeometricallyReduced.lean:60-103 tests the full algebraic closure and does not prove reducedness from the first root extension. SeparablyGenerated.lean:189-206,282-296 gives the p-power independence criterion in the finitely generated case, already the existing Mathlib leaf. PerfectClosure reducedness is a statement about the perfect closure itself. None gives the entire item by a one-line specialization.

## Review by NK

I read coord/delivery-errors.md sections B through E, including the merged copy, and checked the completed split against the actual statements, not their proofs. I read the chapter and unit records and the latest blueprint lem-trf-local-term-locality statement and proof. The latest node uses contracting correspondences; the present algebraic tool belongs to the already inherited historical analytic support chain. This delivery changes no chapter or unit statement, no unit route, and cites no SGA source.

For the item I read Stacks algebra.tex Tag 030W (lemma-characterize-separable-field-extensions), including the (3) to (2) Frobenius argument and (2) to (1) reduction, and Tag 030U (lemma-separable-extension-preserves-reducedness), including its finitely generated reduction and its separably generated case. There are no new node sources to audit. I opened every cited node and copied its statement into citations.json; the precise uses are as follows.

Step 1 uses def-weil-algebraic-closure for roots of nonconstant polynomials, def-weil-ring-frobenius for preservation of sums and products in characteristic p, and def-weil-vector-space-scalar-extension for tensors and scalar operations. Since p is prime it is positive and X^p-c is nonconstant. The field operations and inverses preserve the first-root field by the displayed calculations, and the tensor characteristic is checked directly. The use of inverses is only for nonzero elements. These are elementary consequences of the cited statements and the inline definition of the first-root field.

Step 2 uses the Frobenius ring-homomorphism formula and tensor balancing. All roots r_i are in the first-root field by step 1; it is not necessary to place any roots inside F. The displayed equality x^p=(sum c_i b_i^p) tensor 1 verifies the exact relation needed for reducedness. The reducedness hypothesis is precisely on Q=F tensor_k k^{1/p}; p>=1 is verified before using it.

Step 3 cites lem-weil-pbc-vector-space-basis-through-vector, whose statement explicitly extends every independent subset, and def-weil-vector-space-scalar-extension, whose statement explicitly says a basis stays a basis after scalar extension. Thus no unrecorded theorem about independence under base change is hidden here. Vanishing coefficients in this extended basis gives the original c_i=0. This proves p-power independence rather than simply restating the desired geometric reducedness.

Step 4 cites lem-weil-pbc-p-power-independence-separably-generated. Its statement requires prime p, characteristic p, finite generation as a field, and independence of pth powers of finite independent families. Each holds for the arbitrary finitely generated intermediate field F_0: the inclusion preserves coefficients and powers, and injectivity gives equivalence of relations. Its conclusion is exactly separable generation, which is what step 5 needs. The finite generation hypothesis is imposed only on F_0, never on F. The substantial minimal-inseparability-degree argument of 030W is already this Mathlib leaf; it is not repeated or hidden inline.

Step 5 cites lem-weil-pbc-separably-generated-tensor-reduced, whose statement allows any reduced commutative k-algebra S and any separably generated K/k. We set K=F_0 and S=E. The explicit inverse argument proves reducedness of E; step 4 supplies separable generation of F_0. No algebraicity or finite generation of E is used. This is a generic field-theory tool; the split_report declares it for the maintainer's route review even though its Lean audit is already closed.

Step 6 uses lem-weil-pbc-module-over-field-flat for flatness of the k-vector space E and def-weil-pbc-flat-ring-map for the exact assertion that tensoring an injective linear map stays injective. Thus flatness is not used merely by name without a supporting theorem. The scalar-extension statement supplies the induced linear map, and the product formula in the item verifies that this map is a ring map. The tensor element is a finite sum by the construction of the algebraic tensor product, so F_0=k(f_1,...,f_s) is finitely generated regardless of the size of F. Injectivity, not an assertion about abstract filtered colimits, brings z_0^n=0 back to F_0 tensor E. Step 5 then kills z_0. No hidden existence or comparison theorem about filtered colimits is required.

I tested the argument on F=k, E=k, perfect k (where k^{1/p}=k), and a purely transcendental extension F=k(t). I also tested the excluded inseparable case: for k=F_p(t), F=k(t^{1/p}), the nonzero element t^{1/p} tensor 1 - 1 tensor t^{1/p} has pth power zero; thus the hypothesis correctly fails. Empty independent families and the zero tensor are handled explicitly; for an empty tensor sum the intermediate field is k. The positive nilpotence exponent n is arbitrary. Infinite-degree F and E still involve only finitely many f_i in each tested tensor. There is no new statement to test separately.

I checked that the existing dependencies have no path back to this item. Every proof step is below 2000 characters. There are no clause-restatement nodes, no unsplit node with a proof, no new notion without a definition, and no altered imported fields. The citations contain literal substrings of the cited node statements. Only sandbox files were written; no Lean, compiler, Lake or local preflight/check script was run.

## Unfinished work

No mathematical gap remains at this split level. The maintainer's independent review and eventual Lean formalization remain the project's normal later stages. Delivery validation results are recorded below after the required server checks.
