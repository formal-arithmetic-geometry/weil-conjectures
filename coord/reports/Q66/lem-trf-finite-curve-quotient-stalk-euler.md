# Q66 stage-1 delivery: lem-trf-finite-curve-quotient-stalk-euler

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-finite-curve-quotient-stalk-euler.json`: statement item, split into seven steps; no Mathlib match for the whole statement. Its mathematical statement is unchanged; the explicit short-exact-sequence definition was added to statement dependencies.
- `citations.json`: verbatim statement quotations for every node used in each proof step.
- `searches.jsonl`: actual msearch records for the item, supplementing the inherited searches, which were retained.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searched the project Lean source for the exact blueprint tag and for finite curve quotient, normalization, stalk, coherent and Euler notions. The curve normalization comparison concerns etale coefficient sheaves rather than this structure-sheaf quotient; the structure-sheaf germ and finite-fibre declarations found by semantic Mathlib searches do not assert this item.

## WANTED

None for this split. The primary sources used are already present as Stacks TeX files. The historical parent refers to Temkin Appendix B, but this item is proved from the available Stacks normalization-sequence and coherent-cohomology arguments, without using an unavailable PDF as evidence.

## Corrections and scope

The live item was unsplit and the sandbox contained only dispatcher brief files. There was no earlier proof or report to replace. The item's statement is true as imported, including arbitrary field, disconnected X, nonnormal and possibly nonreduced Y, and the empty scheme. No STATEMENT-DISPUTED correction is needed.

The source 0C1R itself concerns normalization, not an arbitrary finite modification. The proof now explicitly gives the generalization: schematic density supplies injectivity; the finite algebra description gives coherence; the specified generic isomorphism locus gives a boundary missing every component generic point. It does not apply the normalization theorem directly to an arbitrary f, and it does not identify singular support with the support of this general quotient.

The current blueprint's local-term unit and lem-trf-local-term-locality use contracting correspondences. This item is a historical coherent-curve input created under that ancestor; its blueprint.from place and via chain are preserved. No assertion that coherent Euler characteristics prove the current local-term theorem is made, and no unit or chapter route is changed. The generic off-unit tools are each declared in split_report.tool_uses.

## Search and reuse

Read the current item and its chapter/unit records, the current blueprint local-term statement, and the latest schematic-density statement and proof. Whole-DAG keyword/source searches found the existing coherent finite-support skyscraper decomposition, coherent zero-dimensional-support vanishing, proper coherent finiteness, coherent-cokernel closure, affine permanence, schematic-image definitions, and Noetherian/sober topology nodes. Whole-blueprint searches for finite support, quotient stalk, zero-dimensional support, schematically dense, finite curve modification, coherent zero, and stalk dimensions found no duplicate of the item. Existing more specialized normalization-support nodes require algebraically closed k and/or normalization and cannot replace this item for arbitrary f. They were not duplicated.

All five new msearch queries for this item ran through the mandated command: two semantic phrasings with leanfinder, a Loogle Euler query, a grep for finite-support cohomology/Euler/coherent skyscraper notions, and a LeanSearch finite-support query. Read the returned signatures. They concern finite fibres, normalization, reducedness, scheme structure-sheaf germs, restriction vanishing and general sections. None gives the coherent defect, the germs decomposition and Euler calculation under these hypotheses. No service was recorded as absent when it was unavailable, and no unrun searches were added. The inherited Q104 searches remain intact.

## Not duplicates

No new nodes were created. The proof reuses existing statements rather than introducing variants of 0C1R, 0AYT or 0B3J.

## Review by Q66

I checked delivery-errors B through E against the seven steps and the actual cited statements. The item follows the short exact sequence in varieties.tex Tag 0C1R (lemma-prepare-delta-invariant) and the finite-support H0/vanishing/Euler calculation of Tag 0AYT (lemma-chi-tensor-finite). I read those statements and their proofs. I also read coherent.tex Tags 01XZ (lemma-coherent-Noetherian), 01Y0 (lemma-coherent-abelian-Noetherian), 0B3J (lemma-coherent-support-dimension-0), and 02O6 (lemma-proper-over-affine-cohomology-finite), and morphisms.tex Tags 01S7 (lemma-affine-separated), 01T6 (lemma-finite-type-noetherian), and 056D (lemma-reduced-scheme-theoretically-dense), together with the latest blueprint dense-image statement/proof. There are no new-node sources to certify.

For Step 1, I opened lem-trf-proper-field-invertible-coherent: it supplies both Noetherianity and coherence of O_X without dimension or connectedness assumptions, and applies with the trivial rank-one line bundle, as defined by def-sc-invertible-module. The finite-morphism definition explicitly supplies that f_*O_Y is quasi-coherent of finite type; pqf-lem-coherent-ft-locnoeth applies because the first tool made X locally Noetherian. The locally Noetherian coherent-kernel/cokernel statement explicitly gives coherence of this actual cokernel. This avoids assuming Y normal or replacing the cokernel by a sectionwise quotient on arbitrary opens.

For Step 2, I opened affine-morphism-permanence: its third clause gives quasi-compactness and quasi-separatedness, not just a property of affine schemes. The dense-image lemma assumes exactly reduced target plus qcqs map with dense image. Finiteness supplies affineness, and surjectivity supplies density. I opened the schematic-image definition to check that for a quasi-compact map its ideal is the actual kernel of O_X to f_*O_Y. The isomorphic image inclusion therefore forces that kernel to vanish. Merely citing a definition of normalization would not have justified this step; the proof now uses the general dense-image tool and its explicit hypotheses.

For Step 3, I read the sheaf-of-modules category and exact-sequence definitions. They provide the abelian category with sectionwise kernels and sheafified cokernels and the image/kernel definition of short exactness. The elementary step is the monomorphism/cokernel sequence argument and the local identity map on the given isomorphism locus N. It does not assert surjectivity of B(U) to F(U) for arbitrary U. Local quotient classes vanish on N, which is exactly what is needed for the support inclusion.

For Step 4, I opened the Noetherian closed-subset component theorem and the sober-scheme statement: the former says a closed subset is a union of finitely many components; the latter supplies the generic point of each irreducible closed subset and uniqueness. Pure dimension one is defined by chains of irreducible closed subsets. Every x outside N is nongeneric in every component containing it. A distinct specialization would give the displayed chain of length two, contradicting that definition. This explicitly proves closedness and then finiteness of the entire boundary, so there is no concealed appeal to an algebraically closed-field curve lemma or to normality. Closed subspace components are closed in X, so the sober-scheme statement applies to them. The case E empty makes every argument vacuous.

For Step 5, I opened lem-trf-coherent-finite-support-skyscrapers and checked that it states the canonical germ morphism and its module linearity, rather than only existence of some decomposition. Its hypotheses are locally Noetherian X, coherent F and finite closed support, all proved by Steps 1 and 4. Evaluating the finite direct sum is evaluating a finite product componentwise, and the explicitly stated skyscraper sections over X are precisely F_y. Therefore this is the required k-linear germs map, including the nonrational closed-point case; it is not a residue-field-vector-space dimension mistaken for a k-dimension.

For Step 6, I opened lem-sfb-coherent-zero-dimensional-support: its cohomology is explicitly Zariski module-sheaf cohomology, the same convention as the item. It gives positive-degree vanishing on locally Noetherian X; finite closed support has dimension zero. I checked lem-pc-coherent-hi gives finite A-modules when the base is Spec A with A Noetherian, and used A=k. I also opened lem-sc-open-cohomology-zero-sections to justify H0 = ordinary sections, applying it to the full open. Each stalk in S is then a direct summand of a finite-dimensional k-vector space by Step 5, so is finite-dimensional; stalks outside S are zero. This avoids silently using an etale finite-support acyclicity result for coherent Zariski modules.

For Step 7, the Euler definition is exactly the alternating sum of k-dimensions of coherent cohomology on a proper scheme. Step 6 leaves only degree zero, and concatenating the finitely many finite bases gives the sum-of-dimensions formula. The remaining closed stalks are zero by the definition of S. Empty X, f an isomorphism, and S empty give zero F and zero sums. A normalization of a nodal curve gives the usual defect contribution; a finite thickened point attached to an otherwise identical curve source is also allowed and contributes through the same coherent quotient. None of these checks requires reducedness of Y, algebraic closedness of k, connectedness or nodality.

I checked C4 by copying the full statement of each cited node verbatim into citations.json; no proof-only fact is treated as part of a node's statement. I checked C1 by identifying the non-elementary inputs step by step as above; the remaining operations are an abelian cokernel sequence, evaluation of a finite product, and a finite-basis dimension calculation. No proof step exceeds 2000 characters (the longest is under 1000), and no new node repackages a clause of the item. No Lean was written and no compiler or build tool was invoked.

## Unfinished work

No mathematical part of the one-level split remains. Independent maintainer review and further splitting/proving of the existing cited nodes remain the project's later work.
