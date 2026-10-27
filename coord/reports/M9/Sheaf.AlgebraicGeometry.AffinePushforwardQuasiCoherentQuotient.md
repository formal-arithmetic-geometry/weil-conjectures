## What changed

Filled `AlgebraicGeometry.Scheme.Modules.affine_pushforward_quasiCoherent_quotient`
without changing its signature. The proof uses the existing quasi-coherent
cokernel/image theorem, qcqs pushforward theorem, and affine-cover isomorphism
criterion. Added the private proof import
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat` for exactness of module
sections. A proved private helper derives sectionwise kernel/range equality
from categorical exactness and a monomorphic first arrow, using preservation of
kernels by evaluation. The specified quotient is identified with the categorical
cokernel by colimit uniqueness. Pushforward preserves the kernel, and the two
quotient maps have the same kernel and are surjective on affine opens. Their
comparison is therefore an isomorphism. Epimorphism cancellation proves its
uniqueness and naturality. The item's DAG proof follows these constructions.

Validation: the delivered module compiled cleanly through `lcompile.py` in
9.4 seconds. The original theorem signature is unchanged, and every Lean line
is at most 100 characters.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.affine_pushforward_quasiCoherent_quotient`
(node `lem-trf-affine-pushforward-quasi-coherent-quotient`).
No holes added or split off. No `sorry` remains in the item or is added elsewhere.

## No longer needed

The direct proof import `Mathlib.CategoryTheory.Sites.Sheafification` and the
proof dependency `def-weil-pbc-sheafification` are unnecessary: the statement
already specifies a categorical cokernel, whose universal property directly
constructs the comparison. Sheafification may still be used by other modules;
no claim of global unreachability or withdrawal is made. All other stated proof
dependencies remain used. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error was found. The local-image gluing argument
can be replaced by the existing categorical exactness and kernel preservation
APIs. No new nodes or changes to another module are needed. The unit route is
preserved. The conclusions cover the zero subsheaf, the whole sheaf, the empty
scheme, and the identity morphism without any extra hypotheses.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
