# Stage-1 delivery: lem-trf-affine-base-skyscraper-tensor-cohomology

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-affine-base-skyscraper-tensor-cohomology.json`: statement, split; no Mathlib match. Two proof steps, both citing the existing derived comparison. Statement, statement dependencies, source, creation data and blueprint ancestry retained.
- `citations.json`: one verbatim statement quotation for each step's citation.
- `report.md`: this report. `searches.jsonl` was written by the required search command.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the project library by the exact blueprint tag, item id, inverse-image base-skyscraper, relative stalk resolution, skyscraper/tensor and stalk/homology terminology. The nearby ordinary stalk-tensor/skyscraper pullback constructions and exact affine stalk homology results do not state this relative unbounded derived tensor formula with arbitrary local-ring module coefficients. No exact project declaration was found. No compiler or Lake command was run.

## WANTED

None. All sources used are available in the read repository.

## Findings and changes

The imported item is true as stated. It is already deliberately a per-degree consequence of `lem-trf-affine-relative-stalk-resolution-iso`. That node's statement supplies both the exact stalk-and-scalar-transport functor and the full derived tensor comparison specialized to the chosen base skyscraper. Splitting off a new cohomology lemma would only duplicate the elementary consequence of exactness. The proof now explicitly computes kernels, images and their quotient, then applies the cohomology functor to the existing derived comparison and its inverse.

No statement correction, statement dispute, route substitution, or new hypothesis was needed. No maintainer-owned field was changed. There is no new node carrying a clause of the item, and no new statement-only node to be searched or reviewed later.

Read the chapter and unit records, and the current files under `literature/blueprint/latest/blueprint/sec-trace-formula/`, including the chapter, `sk-i-curve-zero` and the statement and proof of `lem-trf-local-term-locality`. The latest ancestor concerns contracting local terms; this affine algebra item is an auxiliary descendant via the existing relative-duality/Tor ancestry, not a direct restatement of the latest ancestor. This delivery keeps that ancestry and the unit route. Blueprint searches for `stalk cohomology`, `skyscraper` and `derived tensor`, and DAG searches for inverse-image base-skyscraper tensor comparisons, found no imported blueprint statement of this particular formula. `blueprint.same_as` remains empty.

## Mathlib searches

Preserved all searches inherited from the item's creation, and read their recorded results. Ran the required command under Q42 for two new LeanFinder phrasings, Loogle, LeanSearch and two grep patterns; their exact queries and returned records are appended to `mathlib_searches` and remain in `searches.jsonl`. All services returned successfully. Hits include ordinary `ModuleCat.Tilde.stalkIso`, skyscraper stalk isomorphisms/adjunctions, structure-sheaf stalk isomorphisms, open-restriction stalk isomorphisms and sheaf cohomology definitions. They do not state the comparison in this item. The second phrasing asked about exact stalks and unbounded cohomology, to check for a more general formulation. No whole-item Mathlib match was found. General functoriality of cohomology is used only as the elementary application of a functor to an isomorphism.

## Not duplicates

No new nodes, so there are no new/existing same-tag pairs. The existing derived comparison is used directly; no node is created for its skyscraper specialization or for preservation of a kernel/image quotient by an exact functor. The per-degree item itself was assigned as an existing node and is retained.

## Review by Q42

For the item I read Stacks `perfect.tex`, Tag 0DHY, `lemma-tor-dimension-rel-affine`, especially the opening identification of the inverse-image structure stalk with the base localization and the associated-sheaf stalk with the localized module complex. I then read `cohomology.tex`, Tag 09U9, `lemma-tor-amplitude-stalk`, whose proof explicitly writes the derived tensor stalk comparison and the equality of its cohomology with stalks of cohomology. I also read `modules.tex`, Tag 01AG, `lemma-abelian`, and its discussion of kernel/cokernel stalks. The last is supporting source inspection, not an uncited extra theorem needed by a step: exactness itself is explicitly supplied in the statement of the sole cited derived-comparison node. There are no new-node sources to review.

I opened every statement dependency of the item. In particular the module stalk definition concerns actual module stalks, the skyscraper uses the action by germs of the ringed-space structure sheaf, the affine localization statement identifies the relevant local rings, and both K-flat conventions permit unbounded complexes. I did not replace inverse image by scheme pullback, nor replace the module stalk by its underlying additive group.

For Step 1 I read the entire statement of `lem-trf-affine-relative-stalk-resolution-iso` and copied into citations.json its sentence saying that the induced derived functor comes from the exact stalk and scalar transport. This is precisely the input the step takes: its exactness yields the kernel, image and quotient identifications written in the proof. The step is elementary relative to this stated input. Scalar transport is along the identical `e_x` named in the item, so the identification is R_p-linear. The displayed kernel/image calculation also verifies representative independence by preservation of quasi-isomorphisms; it requires no choice of a bounded complex or acyclic resolution for stalks.

For Step 2 I checked that the same cited statement permits every commutative ring map, every complex M, every prime q, its contracted prime p and every R_p-module L. Its final skyscraper clause states exactly the specialized derived isomorphism used by the step, including linearity under e_x; that sentence is copied verbatim in citations.json. Applying H^i to that isomorphism and its inverse gives inverse R_p-linear maps. Composing with Step 1 proves the requested isomorphism and records that it is induced by the specified derived comparison. No extra tensor-flatness fact is asserted in this passage.

I checked small cases: L=0 or M=0 gives zero on both sides; R=A and f the identity reduces to the usual tensor stalk comparison; for R=A=Z, q=(2) and M=L=Z/2 in degree zero, degree -1 can be nonzero because of Tor, and the proof retains that degree rather than replacing derived tensor by ordinary tensor. Generic/nonclosed points use the same ringed-module skyscraper and its stated stalk, with no closed-point assumption. Arbitrarily shifted and unbounded complexes cause no change because each H^i calculation uses only the three adjacent degrees. If Spec A is empty there is no point x and the statement has no instance.

Against delivery-errors B--E: no new nodes or new definitions; no relabelled clause; no hidden long lemma (steps are 821 and 964 characters); all non-elementary geometric/derived content is taken from the existing derived-form statement; exactness is quoted from that statement, not inferred from a definition or borrowed from its proof. Each citation quote was checked as a literal substring of the cited live statement. There are no new dependency edges below that cited node that could create a cycle. This delivery leaves only the independent maintainer review of the split after the required preflight and push.

## Unfinished work

None within the assigned one-level split. Proving or splitting the existing derived-comparison node is a separate DAG item.
