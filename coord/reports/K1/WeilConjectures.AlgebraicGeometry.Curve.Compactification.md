## What changed

Filled both sorries of WeilConjectures.AlgebraicGeometry.Curve.Compactification without changing any declaration signature or definition. Added the proof-only import Sheaf.AlgebraicGeometry.DimOneQuasiProjective; import_direction.py permits it. The existing public imports remain used by the other declarations and their proofs.

IsCurve.isQuasiProjective uses the existing dimension-one quasi-projectivity statement, converts the dimension bound, composes the closed and open immersions, and verifies the structure-map identity. IsCurve.exists_projectiveClosure uses the same embedding, takes its Mathlib scheme-theoretic image, proves it irreducible by density and reduced by injectivity on an affine basis, and verifies all requested immersion, density, integrality and commutativity clauses.

Updated the two corresponding nodes to match these proofs. Added the missing lean record on the existing projective-closure node. No new module, node, or unproved statement was created. The unit records sk-thm-br and sk-i-real-compactification have no realized nodes for these items; the existing compactification/normalization proofs and the units' routes are preserved.

## Proved and sorry left

Proved AlgebraicGeometry.IsCurve.exists_projectiveClosure (lem-wf-finite-field-curve-quasi-projective) and AlgebraicGeometry.IsCurve.isQuasiProjective (lem-sc-curves-quasi-projective): 2 of 2 original sorries removed. No sorry remains in the delivered module, and no sorry was added elsewhere.

These are stage-3 reductions from the already stated AlgebraicGeometry.exists_closed_open_immersion_projectiveSpace_of_dim_le_one (lem-sc-dim-one-quasi-projective, Sheaf.AlgebraicGeometry.DimOneQuasiProjective), whose proof remains sorry in the library. The dimension comparison AlgebraicGeometry.Scheme.dim_eq_topologicalKrullDim (lem-pc-scheme-dimension-local-rings, Sheaf.AlgebraicGeometry.Dimension) also remains sorry in the library. Neither dependency is restated or delivered here. The closure's integrality and factorization glue is completely proved in Lean, using existing Mathlib results.

The full module compiles with lcompile.py, without errors or warnings. Edge cases: IsCurve.isQuasiProjective allows the empty scheme, zero-dimensional curves, and disconnected smooth curves, all covered by the generic theorem; no connectedness or dimension-equality hypothesis was added. The closure theorem's existing integrality hypothesis ensures nonemptiness and irreducibility, and works also in dimension zero and over imperfect fields. Its reducedness argument does not assume the ambient projective space or boundary is integral, smooth or normal.

## No longer needed

No original import removed; the single added proof-only import is used by both proofs.

The direct proof dependencies lem-sc-dim0-finite, lem-sc-positive-degree-ample, and lem-chow-segre of lem-sc-curves-quasi-projective are replaced by lem-sc-dim-one-quasi-projective and lem-pc-scheme-dimension-local-rings. Their modules are not newly imported for quasi-projectivity, and the finite-affine-cover gluing/Segre argument is not used. This is pruning of this node's proof, not a claim that those nodes are globally unreachable: RiemannRoch remains needed by the unchanged affine-open theorem.

The direct proof dependency def-weil-pbc-scheme-conventions of the projective-closure node is replaced by the actual dimension-one embedding and scheme-image dependencies listed in its updated proof_deps. The generic Mathlib constructions already provide the factorization and closed immersion; no additional projective-closure theorem is introduced.

## Where the brief, the DAG or earlier work was wrong

The brief's plan via a gluing construction is unnecessary: the library already states the general Stacks 0A25 theorem as lem-sc-dim-one-quasi-projective, with the exact separatedness, finite-type and dimension-bound assumptions supplied by IsCurve. The integral projective-closure statement had a blueprint node but no lean record, so a search only for lean.module would miss its first sorry; its docstring identifies the existing node.

Mathlib search performed with msearch.py leanfinder (dimension-one quasi-projectivity), loogle (IsImmersion), and grep (integral images/ample curves), followed by rg over both library roots and Mathlib. No direct Mathlib curve quasi-projectivity theorem was found. Read the existing generic statement and dimension comparison, and the Mathlib immersion/image, section-injectivity, reduced-scheme, and irreducibility APIs. Checked Stacks Tags 0A25 and 01R8 online because the local Stacks source is absent: https://stacks.math.columbia.edu/tag/0A25 and https://stacks.math.columbia.edu/tag/01R8. These support the chosen existing theorem and the image construction. No source-free unproved lemma was introduced.

## Second reading by K1

1. **Visible declarations:** Compared the delivered module with the repository version. The two theorem signatures and all existing definitions are byte-for-byte unchanged; the only source change is the proof-only import and proof bodies. The node edits change proof metadata and add the missing Lean record, with no statement change.

2. **Compilation and axioms:** Compiled the module with `lcompile.py`; it succeeds without errors or warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations in the delivered module. Compiled a scratch copy with `#print axioms` for all seven theorems in the module. Each reports only `propext`, `Classical.choice`, and `Quot.sound`, with `sorryAx` additionally present exactly in the two new reductions and the existing theorems that depend on open library results. Neither newly filled proof is yet axiom-free transitively: the existing embedding and dimension lemmas remain open.

3. **Statements and split-offs:** No split-off statements or new modules were added. Independently searched with `msearch.py grep "scheme image integral"` and `rg` for image integrality, injectivity, and projective closures; no existing direct integral-image or projective-closure theorem provides a shorter route. The existing node statements are true and unchanged, and the proofs do not restate either target. The generic dimension-one theorem and dimension comparison are used directly.

4. **Pruning and route:** The proof follows the existing dimension-one quasi-projectivity route and preserves both units' routes. The added import is proof-only and used by both proofs. The updated proof dependency lists remove the old direct dependencies that are not referenced by the Lean terms; no public import was removed.

5. **DAG agreement:** The two node `proof` and `proof_deps` fields match the Lean proofs. The projective-closure node now has the Lean record corresponding to its declaration; no new node or change record is needed. Independently read the dimension-one theorem and the scheme-image dependency node, and checked both unit records: their `realized` fields are empty and the existing compactification proofs are unchanged. Empty and zero-dimensional schemes are allowed in quasi-projectivity, whereas integrality supplies the nonempty irreducible source required by the closure proof; no smoothness, perfection, or ambient integrality is smuggled into that proof.

I changed only this report after review; no further Lean repairs were necessary.
