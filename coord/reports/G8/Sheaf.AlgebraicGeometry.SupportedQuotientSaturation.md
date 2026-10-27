## What changed

Filled the sole proof in `Sheaf.AlgebraicGeometry.SupportedQuotientSaturation`.
The statement, universe, binders, visibility, public imports, and definitions are unchanged.
Only the item module and the proof fields of its own DAG node change.

The proof extracts quasi-coherence, the epimorphic quotient projection, the image/kernel
formula, and affine surjectivity from the existing
`AlgebraicGeometry.Scheme.Modules.quasiCoherent_cokernel_image`.
The abelian image factor of the given monomorphism is invertible, so its section maps
identify the sectionwise kernel with the actual range of the supported subsheaf.
On opens contained in V this kernel is zero. Componentwise cancellation proves that the
restricted projection is mono; restriction is a left adjoint, hence preserves its epi,
and the abelian category on V makes it an isomorphism.
For saturation, affine local lifts of a quotient section restrict to zero, lie in the
supported image, and therefore have zero quotient image. Sheaf uniqueness finishes.
The formula for the restriction adjunction unit then proves its monomorphism by
componentwise cancellation on differences.

The proof uses local names for the actual canonical cokernel and projection, avoiding
unnecessary elaboration through repeated colimit constructions. It creates no new data
or helper declarations and uses no transparency override.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.supportedQuotientSaturation`
(node `lem-trf-supported-quotient-saturation`).
No holes are added or split off. The delivered module contains zero sorry tokens.
All seven conclusion clauses are assembled in the original order.

The edge cases V empty, V equal to Y, empty Y, zero modules, and empty section domains
remain valid. Affine neighborhoods are chosen pointwise, with no finite-subcover or
quasi-separatedness hypothesis; no intersection of affine opens is assumed affine.
The prescribed remote single-file compiler succeeded without errors or warnings in 8.5 s.
The final delivery command runs its axiom probe and preflight checks.

## No longer needed

No module, import, node, or declaration is withdrawn. The sole declared proof dependency
`lem-weil-pbc-quasi-coherent-module-cokernel-image` is used. The original public imports
remain as part of the existing exposed interface. No new proof imports are needed.

The local-image/sheaf-gluing argument for identifying the kernel is replaced by the
already available abelian image isomorphism of a mono. The explicit gluing argument for
the isomorphism on V is replaced by restriction preserving epis and the abelian
mono-plus-epi criterion. Neither replacement prunes a separate DAG dependency, and
no unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement or definition defect was found. The original plan is valid but its
sectionwise kernel and restricted-isomorphism steps can be implemented more directly
with the existing abelian-category API. The DAG proof fields now record that route.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
