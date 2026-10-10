1. Files written

- `lem-weil-pbc-dimension-preserved-field-extension`: statement node, split; no new nodes.

2. Attachments

- None. No sorry-free slopmaster2 declaration states the item exactly.

3. WANTED

- None.

4. What was wrong or incomplete

- The unsplit item had the correct 00P3 statement but no proof decomposition.
- The one-line 00P3 source citation hides the pointwise and empty-spectrum details. The split uses the already reviewed 00P4 local-dimension extension lemma, faithful-flat scalar extension and its surjective spectrum, and the reviewed 0B7I supremum-of-local-dimensions lemma.
- The proof explicitly identifies `S tensor_k K` with `K tensor_k S` by the canonical symmetry isomorphism. The empty algebra case is covered because both spectra are empty and the supremum convention is `-infinity`.
- Whole-blueprint searches for 00P3, polynomial-dimension, and injective finite scalar-extension statements found no duplicate blueprint node; the proof therefore cites existing DAG nodes rather than creating duplicates.

5. Unfinished

- Nothing unfinished in the stage-1 split. Lean was not written or built, per the stage-1 contract.

## Review by M1

- Source review: Stacks Algebra 00P3 is the target statement. The proof uses the stronger local statement 00P4 from the same source and Topology 0B7I for the global supremum, while preserving the 00P3 conclusion and hypotheses.
- Mathematical review: scalar extension is faithfully flat; faithful flatness gives surjectivity on spectra; 00P4 gives equality of local dimensions over every point after tensor symmetry; surjectivity makes the contraction map cover all points; 0B7I then gives equality of the two global suprema. Empty spectra give `-infinity` on both sides.
- Dependency review: every proof step names the existing node it invokes, and `proof_deps` is exactly the union of those uses. No statement dependency was removed or added.
- Edge-case review: the zero algebra is included in the item statement and is handled by the empty-spectrum clause; the zero-variable polynomial case is internal to the already accepted 00P4 proof and is not separately assumed here.
- Lead review status: self-reviewed by M1; awaiting lead review and landing.
