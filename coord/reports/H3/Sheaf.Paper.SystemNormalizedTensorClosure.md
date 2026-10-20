## What changed

Proved `WeilConjectures.SemilinearSections.normalized_tensor_closure` with its existing
signature. Its normalization follows by cancellation from the actual tensor-reduction
formula; its formula and quotient cocycle are retained as the other two conjuncts.
The existing inverse-image closure proof and all existing declaration signatures remain
unchanged.

Four new modules prove the calculation that the old proof plan left implicit:
`SystemOrdinaryTensorReduction`, `SystemCochainTensorReduction`,
`SystemEvaluationFlat`, and `SystemTensorReductionFormula`. Ordinary horizontal
adjoints respect tensor by the pure-section normalization. Applying that identity on
total tensor summands proves the cochain identity. The local finite-relation criterion
proves that evaluation preserves flat terms. K-flat resolutions, the model-derived
squares, naturality of the scalar counit and tensor models, and cancellation then prove
the actual derived formula. Naturality transports it to arbitrary derived objects.
All intermediate results are proved; none is an assumed restatement of the original
formula.

The construction `cochainReduction` is explicitly degreewise. The derived proof keeps
large monoidal and derived-category instances locally irreducible and uses their
comparison APIs. It does not change a definition used by an existing target.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.SemilinearSections.normalized_tensor_closure`.
The already proved `normalized_inverseImage_closure` is preserved.

The new public theorems are `ordinary_tensor_reduction`,
`cochainReduction_eq_transpose`, `cochain_tensor_reduction`,
`evaluation_preserves_flat`, and `tensor_reduction_formula`, all in namespace
`WeilConjectures.SemilinearSections`. Their supporting definitions and all private
helpers are also complete. Holes closed: 1. Holes added: 0. Holes remaining in the
five delivered Lean modules: 0. There is no unfinished split.

Single-file server checks established the ordinary, cochain, flatness and derived
identities. The complete packet is checked together in dependency order before delivery;
the delivery tool performs its own compiler, axiom and packet checks.

## No longer needed

Removed the item's direct private imports of
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` and
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`. The proof uses the
simultaneous calculus's specified model squares rather than applying the separate
canonical tensor-pullback theorem.

Accordingly, the original node no longer has direct proof edges to
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` or
`lem-pur-derived-change-of-rings`. Its statement dependencies are unchanged. These
results and their modules still serve other statements and the calculus; this packet
does not withdraw them. No existing module or declaration is deleted.

The new formula module also drops a redundant direct K-flat-resolution import, since
its public calculus import already supplies that theorem.

## Where the brief, the DAG or earlier work was wrong

The original plan's assertion that the section model identifies the actual tensor
adjoint was a substantive calculation, not an immediately usable field of `Data`.
The available pure-section, summand and derived-square fields suffice, but one must
combine them explicitly. In particular, equality on components cannot be inferred
merely from conservativity of evaluations.

The representative calculation needs flat evaluated terms as well as K-flat evaluated
complexes. The existing evaluation model supplies the latter; the new flatness lemma
supplies the former. The proof uses the local relation criterion, including empty
finite families, so it imposes no extra boundedness or coefficient-flatness hypothesis.
The original statement and the unit route are preserved.

## New nodes

`lem-pur-system-ordinary-tensor-reduction` realizes the ordinary adjunction calculation
in `Sheaf.Paper.SystemOrdinaryTensorReduction`. Its `ordinaryReduction` definition is
the actual adjoint of the horizontal transition; pure tensors prove its tensor formula.

`lem-pur-system-cochain-tensor-reduction` realizes the total-complex calculation in
`Sheaf.Paper.SystemCochainTensorReduction`. It includes the degreewise cochain map,
its equality with the induced adjunction transpose, and the summandwise tensor formula.

`lem-pur-system-evaluation-flat` proves flatness preservation in
`Sheaf.Paper.SystemEvaluationFlat` by pulling covering relation witnesses back along
a vertical inclusion of the sequence site.

`lem-pur-system-tensor-reduction-formula` realizes the actual derived transition
calculation in `Sheaf.Paper.SystemTensorReductionFormula`. It localizes the cochain
identity and combines the specified comparison squares on K-flat representatives,
then descends by naturality. All four new nodes have complete proofs and introduce
zero holes. No definition or statement repair, forced adaptation or change record is
needed.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
