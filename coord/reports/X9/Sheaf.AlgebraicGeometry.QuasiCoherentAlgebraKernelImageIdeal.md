## What changed

Filled both theorem proofs in
`Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraKernelImageIdeal`, preserving their statements.
The proofs follow the current node's five steps and use its existing algebra-image,
generated-ideal tensor, and algebra-quotient cokernel declarations as private proof imports.
The scheme module kernel, cokernel/image, and affine tensor-section results supply the
quasi-coherence and affine calculations.

The proof uses declaration-local elaboration settings and namespaces opened only inside
the theorem bodies. The ideal-image isomorphism is encapsulated to keep its sectionwise
construction out of subsequent elaboration. No definitions or public interfaces change.

The tensor comparison is the sheafification of the identity on sectionwise tensors.
Naturality of the sheafification unit identifies its pure tensors with those in the
statement. Tensor induction proves the affine ideal-span equality. The tensor image's
section ideals form a `RingedSiteIdeal`: restriction and local membership follow from
its identification with the kernel of the module cokernel map. A sectionwise bijective
linear inclusion identifies this ideal's module with the categorical image. The quotient
comparison then transfers quasi-coherence, affine surjectivity and kernels. Finally,
minimality places the generated ideal in the kernel of any algebra map annihilating `e`,
so the existing quotient universal property gives the unique factorization.

The ideal and tensor maps chosen from existing statements are determined by their
specified section ranges and pure-tensor formulas; no arbitrary object is selected
from a mere existence assertion. Empty opens, the zero module, the unit ideal, and
zero section rings require no additional hypotheses.

## Proved and sorry left

Closed the two original holes:

- `AlgebraicGeometry.Scheme.CommAlgebraSheaf.kernel_image_quasiCoherent`.
- `AlgebraicGeometry.Scheme.CommAlgebraSheaf.generated_ideal_quotient_quasiCoherent`.

Validation: `lcompile.py` compiled the complete module without warnings in 32.1 seconds.
Both original theorem signatures remain unchanged, and every Lean line is at most
100 characters.

No holes remain in the item. No holes were added or split off. The existing dependencies
`CategoryTheory.commAlgebraSheaf_image_factorization`,
`AlgebraicGeometry.RingedSpace.exists_generatedIdeal_tensor`, and
`CategoryTheory.algebraSheafQuotient_cokernel` are used as the current DAG prescribes;
this delivery changes no dependency module.

## No longer needed

Removed the redundant private imports `Sheaf.CategoryTheory.RingedSiteModules`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`, and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: their interfaces are
already provided by the general construction modules actually used here. No mathematical
node or module is withdrawn; every declared proof dependency is still used. No unit route
is changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found. The current unit route and the five-step DAG proof
are retained, so no node attachment or dependency update is necessary. The module's older
docstrings describe the constructions inline, while the current DAG has already factored
them into the three existing general ringed-space lemmas. The proofs use those interfaces as requested.
LeanFinder, Loogle and grep searches found quasi-coherence definitions and scheme-morphism
ideal sheaves, but no shorter theorem for these algebra-sheaf assertions.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
