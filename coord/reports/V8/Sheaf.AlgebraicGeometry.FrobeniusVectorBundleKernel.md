## What changed

Repair of returned head `c46e7fdf10`: removed the private duplicate `lisseOfIso`.
Both callers now use `finiteLocallyConstant_of_iso` from
`Sheaf.AlgebraicGeometry.PullbackFiniteLocallyConstant`. Because this existing theorem
is private, the existing proof-only import is changed to `import all`, following
`ConstructibleEtaleSetPullbackStratum`. No dependency module or public interface changes.

Implemented the Frobenius solution ring explicitly as a multivariate polynomial quotient.
Its identity Jacobian proves étaleness; Lang--Steinberg over algebraically closed residue
fields proves surjectivity. Proved the universal solution property using the Spec/global
sections adjunction. The construction includes singular matrices, rank zero and the zero ring.

Reduced the original theorem to natural scalar-compatible local vector-bundle frames.
The semilinear matrix formula is proved from this interface. From those coordinates,
the delivery proves local surjectivity of F-1, affine étale representability of its kernel,
and the full passage from these models to finite abelian constructible strata. The latter
uses the existing stratified-finiteness, represented inverse-image, finite étale Yoneda,
finite-local-abelian-forget and global refinement declarations. Constant abelian values
are proved finite using a geometric stalk on each nonempty trivializing member.
The joint-surjectivity instance used by this cover argument is local to its proof.

The original theorem statement and all public definitions remain unchanged. No existing
module outside the assigned item is adapted. All six modules passed the single-file compiler in sandbox import order.
After fixing the line length introduced by the longer existing theorem name, the
repaired main module compiled without warnings in 4.9 seconds.

The kernel/restriction comparison is a real irreducible private construction from the
canonical limit comparisons. The finite-model argument is stated over a generic abelian
sheaf internally, avoiding repeated unfolding of the concrete tensor-section sheaf.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.frobenius_vectorBundle_kernel_constructible`.

Added and remaining: `AlgebraicGeometry.Scheme.frobenius_vectorBundle_local_frames`
(node `lem-weil-pbc-frobenius-vector-bundle-local-frames`). This still needs the affine
finite free frame, its tensor-pullback coordinate equivalences, and their scalar compatibility
and naturality with the normalized restriction maps. The semilinear matrix formula and
characteristic-p calculation are proved. The frame docstring and node give the full
remaining argument and identify the existing comparison API.

Original holes: 1. Closed: 1. Added: 1. Remaining in the delivery: 1.
This is a decomposition with net zero holes, not a complete proof free of sorry dependencies.
The polynomial solution-cover, coordinate, local-lift and affine-kernel-model theorems
have no holes.

## No longer needed

Removed proof imports from the item module:
`Sheaf.AlgebraicGeometry.TensorPullback`,
`WeilConjectures.AlgebraicGeometry.TensorPullback`,
`WeilConjectures.Mathlib.RingTheory.Extension.Presentation.Submersive`,
`WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree`,
`WeilConjectures.LinearAlgebra.SemilinearFrobenius`,
`Mathlib.AlgebraicGeometry.Morphisms.Etale`,
`Mathlib.AlgebraicGeometry.Sites.Etale`,
`Sheaf.AlgebraicGeometry.Sites.InverseImageRepresentable`, and
`Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`.
The unused EpiMono import was removed from the new coordinate module and made proof-only
in the new affine-model module. The algebra imports now belong to the polynomial module,
while the two retired Sheaf wrappers are replaced by their existing source-library implementation imports.

The explicit cover-base-change/constant-sheaf argument is supplied by the existing
`pullback_finite_locally_constant` theorem. Its hypotheses are instantiated on the actual
factorization morphisms furnished by the global refinement lemma. The original algebra,
module and pullback dependency nodes remain needed below the new statements or that
existing theorem. The redundant private theorem `lisseOfIso` is removed.
No DAG node or library module is withdrawn; pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The returned duplicate check was correct: `lisseOfIso` and the existing
`finiteLocallyConstant_of_iso` have identical binders and conclusions. The duplicate
has been deleted and both isomorphism transports now use the existing theorem.

No false statement was found. The original plan is mathematically sound. The proof uses
sectionwise preservation of categorical kernels and the Spec/global-sections adjunction,
so the representing correspondence works for every étale test scheme directly; it does
not need a separate affine-cover gluing lemma. Compactness is used only to choose the
finite chart cover, not in the polynomial algebra calculation.

## New nodes

`lem-weil-pbc-frobenius-polynomial-solution-cover`: proved explicit affine solution cover,
including its universal property, étaleness and surjectivity.

`lem-weil-pbc-frobenius-vector-bundle-local-coordinates`: proved semilinear coordinate
formula from natural scalar-compatible frames by expanding finite coordinate tuples.

`lem-weil-pbc-frobenius-vector-bundle-local-frames`: remaining geometric frame
interface, with complete proof in words and three recorded Mathlib search kinds.

`lem-weil-pbc-frobenius-vector-bundle-local-lifts`: proved local lifting from coordinates
and the polynomial solution cover.

`lem-weil-pbc-frobenius-vector-bundle-affine-kernel-models`: proved finite affine models
from the coordinate interface, categorical kernel sections and the quotient universal property.

No definition or statement change record is needed.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
