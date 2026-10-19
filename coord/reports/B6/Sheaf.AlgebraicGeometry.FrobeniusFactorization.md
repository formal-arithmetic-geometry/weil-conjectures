## What changed

Proved `WeilConjectures.FiniteFieldDatum.absoluteFrobenius_factorization` in
`Sheaf.AlgebraicGeometry.FrobeniusFactorization`, keeping its signature and public imports
unchanged. Four proved private helpers establish naturality, addition, zero, and multiplication
of the absolute Frobenius iteration index. The main proof compares the two pullback projections
to prove both one-step factorizations, then uses `Commute.mul_pow` for arbitrary iterates.
The coefficient-field calculation identifies the inverse geometric field Frobenius with the
arithmetic q-power map. Updated the existing node's proof, proof dependencies, and origin to
this route. No definition or existing statement changed; no consumer adaptations are needed.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.FiniteFieldDatum.absoluteFrobenius_factorization`
(node `prop-trf-frobenius-factorization`). Holes closed: 1; holes added: 0; holes left: 0.
All four private helpers are proved. No split-off statements or new modules.

## No longer needed

Removed the direct proof imports `WeilConjectures.Mathlib.Algebra.CharP.Lemmas`,
`Mathlib.LinearAlgebra.TensorProduct.Defs`, `Mathlib.AlgebraicGeometry.Scheme`, and
`Mathlib.Geometry.RingedSpace.LocallyRingedSpace`. The needed ring, spectrum and scheme
interfaces remain available through the unchanged public imports. No public import was removed.

The old dependency `def-weil-pbc-module-tensor-product` is no longer used by this proof:
pullback uniqueness replaces the tensor generation calculation and affine-cover gluing.
In particular this proof needs neither `TensorProduct.induction_on` nor the affine formula
lemmas `relativeFrobenius_affine` and `galoisMap_affine`. The ring-Frobenius, affine-spectrum,
and locally-ringed-space interfaces remain used by the sectionwise and Spec arguments and
are retained in the node. The existing relative and Galois projection lemmas are recorded
through their own definition nodes. No claim is made that a removed direct import becomes
unreachable from the project's other imports. The unit's realized statement and steps are
unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The planned affine tensor calculation is longer
than using the already constructed maps' projection identities and absolute Frobenius
naturality. The proof handles empty and nonreduced schemes without a nontriviality assumption
on section rings. It actually works for m=0 as well; the original m>=1 hypothesis is retained.
End multiplication reverses categorical composition, and both final conjuncts explicitly
account for this reversal. No blueprint unit route is changed.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
