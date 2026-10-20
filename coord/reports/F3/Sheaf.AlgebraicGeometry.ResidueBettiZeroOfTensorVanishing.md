## What changed

Restored `lean/Sheaf/AlgebraicGeometry/ResidueBettiZeroOfTensorVanishing.lean` from its
quarantine archive with the complete proof of
`AlgebraicGeometry.Scheme.derivedFiberBetti_eq_zero_of_tensor_vanishes`.
The proof uses the declared tensor-vanishing, exact-stalk, stalk-tensor, tensor-closed,
and K-flat residue-comparison dependencies. No declaration or signature was changed.
The archived text compiles together with the already restored
`Sheaf.AlgebraicGeometry.KFlatStalkResidueCohomology` dependency.

## Proved and sorry left

Zero holes before and zero after. The restored theorem
`AlgebraicGeometry.Scheme.derivedFiberBetti_eq_zero_of_tensor_vanishes` is proved;
no `sorry` was added and no theorem was split off.

## No longer needed

None. Every proof import in the restored module is used, and no DAG node or module was
pruned.

## Where the brief, the DAG or earlier work was wrong

The upstream sync quarantined this module because its dependency's compiled artifact was
missing, even though the dependency was subsequently restored with its corrected
`IsKFlatTensor` predicate. The quarantine archive contains the complete theorem proof
and the current dependency pair compiles cleanly; the repair is therefore restoration of
the archived module, with no mathematical or interface change.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
