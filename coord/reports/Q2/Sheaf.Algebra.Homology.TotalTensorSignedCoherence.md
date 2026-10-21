## What changed

Proved `CategoryTheory.RingedDerivedNative.totalTensor_signed_coherence` using private,
proved helpers for the existing tensor summand formulas. The shift formula is obtained
from Mathlib's two integer bifunctor shift comparisons; the associator and braiding
formulas use the proved native source-library summand API. Degreewise coproduct
extensionality proves uniqueness, naturality and both signed coherence squares.
The definitions and existing declaration signatures are unchanged.

Updated the item's DAG proof, proof dependencies and proof origin to this shorter route.
The import-interface change is recorded in
`coord/changes/total-tensor-signed-coherence-imports.md`; current downstream modules: zero.
Replaced the public import of RingedTensorComplexConstraints with its public dependency
RingedDerivedTensorNative, which supplies the native tensor structures used by the
unchanged statements. Added the private proof import Mathlib.Tactic.Ring.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.RingedDerivedNative.totalTensor_signed_coherence`
(node `lem-pur-total-tensor-signed-coherence`).
Added zero holes; zero sorries remain in the delivered module. No decomposition.
The complete module compiled through lcompile.py (17.8 seconds, zero errors);
the final delivery compilation and declaration axiom probe also passed without warnings.
The first preflight requested an import-interface change record, now included.
The additional helper theorems are private and proved.

## No longer needed

Removed direct imports:
- `Sheaf.Algebra.Homology.RingedTensorComplexConstraints`;
- `Sheaf.CategoryTheory.LargeSetSheafification`;
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`;
- `Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`;
- `Mathlib.CategoryTheory.Monoidal.CommGrp_`.

The proof no longer uses these former proof dependencies:
`lem-sf-ringed-tensor-complex-constraints`,
`lem-pc-sites-sheaf-tensor-bilinear-universal`,
`lem-weil-pbc-large-set-sheafification`,
`lem-weil-pbc-sheafification-sets-exact`,
`lem-weil-pbc-adjunction-lifts-abelian-group-objects`,
`def-weil-presheaf-modules-sheafification`, and
`lem-weil-pbc-independent-sheaf-tensor-colimits`.
It also does not need `def-weil-sheaf-of-modules-category` as a proof dependency;
that node remains a statement dependency. The tensor construction's existing instance
proofs still have their own dependencies, which this delivery does not withdraw.
No library declarations or modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned pure-section descent is unnecessary: the native library already proves
formulas on entire tensor summands, and Mathlib supplies double and triple summand
extensionality. This avoids assuming any generation property for global pure sections.
The original statements and shifted-degree sign convention are correct, including
negative shifts. The associativity exponents agree as integers; the symmetry exponents
differ by `2*b*p`. No target or unit route changes.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
