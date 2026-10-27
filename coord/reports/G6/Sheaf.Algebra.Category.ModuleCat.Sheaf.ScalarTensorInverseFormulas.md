## What changed

Completed `SheafOfModules.scalarTensor_inverse_formulas` without changing its statement.
The proof constructs the scalar-multiplying inverse from Mathlib's ordinary base-change
isomorphism, descends its bilinear pairing through both sheafifications, and checks both
inverse identities by sheafification and tensor uniqueness. Private proved helpers expose
the universal property for the exact `siteSheafTensorRight` objects in the statement.
The proof imports `SheafifyBilinearExtUniqueness` directly for the uniqueness argument.
The DAG proof and dependencies now record this direct implementation and the existing
Mathlib base-change leaf.

The command-scope changes requested by static preflight are documented in
`coord/changes/g6-scalar-tensor-inverse-proof-support.md`. The only downstream module,
`Sheaf.SecSmoothPurity.CoefficientComparisonsBalancedConstruction`, has no changed
statement or definition and requires no adaptation.

## Proved and sorry left

Closed the one existing hole: `SheafOfModules.scalarTensor_inverse_formulas`
(`lem-pd-sheaf-scalar-tensor-inverse-formulas`). No holes added, none left. No split-off
statements. The statement is unchanged, including zero rings and arbitrary ring maps.
`lcompile.py` compiled the final module cleanly in 33.8 seconds and the unchanged
downstream importer in 11.8 seconds. `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`; the diagnostic commands were removed.

## No longer needed

The proof does not use the localization-tensor presentation supplied by
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`
(`lem-pc-sites-sheaf-tensor-bilinear-universal`); that proof import is removed.
Instead, proved private `tensorLift`, `tensorLift_apply`, and `tensor_ext` apply the
Mathlib module-sheafification adjunction directly to the exact sectionwise tensor
presheaf appearing in the statement. The underlying tensor universal-property argument
is retained. No module is withdrawn and no other unit route is changed.

## Where the brief, the DAG or earlier work was wrong

The generic sheaf tensor universal property uses the localization tensor, while this
statement uses direct sheafification of `siteTensorPresheaf`. Their equivalence need not
be unfolded or transported: the same universal-property proof works directly for the
latter. The proof is implemented by proved private helpers for the direct sheafification
presentation. Compilation is through the required `lcompile.py` service.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
