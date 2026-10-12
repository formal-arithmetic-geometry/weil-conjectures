## What changed

Proved the body of `AlgebraicGeometry.Scheme.Modules.kernel_image_pullback_of_constantRank`
from a new local block normal-form theorem. The original signature is unchanged.
The new module `Sheaf.AlgebraicGeometry.Modules.ConstantRankMapNormalForm` states
`AlgebraicGeometry.Scheme.Modules.exists_local_normal_form_of_constantRank`, precisely
steps 1–2 of the original plan plus transport of the block bases. It asserts a local
factorization through a finite free pivot summand, not any kernel/image conclusion.

The private, fully proved `kernel_image_of_block_form` works in any abelian category.
It identifies the kernel via kernelIsIsoComp/kernelCompMono/kernelBiprodSndIso, identifies
the image via strong-epi/mono factorization, and constructs its retraction explicitly.
The main proof transports these through exact open restriction, builds a point-indexed
open cover, and applies the existing finite-local-freeness covering criterion twice.
It transports the retraction using the image-preservation compatibility equation.
Choice is used only for proof-local bases and neighbourhoods; no definition chooses
unconstrained data from an unproved existence theorem.

Both modules compile through lcompile.py. The unit's reduced-ring normal-form route is
retained. The empty scheme is covered by the empty point-indexed cover. Rank zero has
empty pivot blocks and the normal-form proof uses the unit empty minor; maximal rank
has the appropriate zero complementary block. At a point, ranks greater than m or n
cannot meet the hypothesis. The zero ring contributes no points.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.kernel_image_pullback_of_constantRank`
(node `lem-pc-constant-rank-map-kernel-image`). No sorry remains in the item.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_local_normal_form_of_constantRank`
(node `lem-pc-constant-rank-map-local-normal-form`), in its own new module.
Its proof is exactly `by sorry`; its docstring contains the full reduced-ring/minor
argument. This is a decomposition: one original hole closed, one strictly intermediate
hole added, net zero. The categorical calculation, restriction transport and covering
argument are complete Lean proofs.

## No longer needed

Removed the item import `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`:
node `lem-weil-pbc-quasi-coherent-module-cokernel-image` is unnecessary for this proof.
The affine tilde/Gamma dependency `lem-weil-pbc-affine-tilde-gamma-adjunction` is also
unnecessary: categorical kernels/images and their preservation suffice directly.
No assertion that these modules leave the entire targets' closure is made; they may
have other users.

The direct item import `Sheaf.LinearAlgebra.MatrixRankFieldExtension` is replaced by
the normal-form import. Its node `lem-weil-matrix-rank-field-extension`, reducedness,
the nilradical argument, matrix rank and open-pullback/restriction comparison remain
needed in the normal-form plan, and are not globally pruned.

Kept `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` for its proved
`preservesLimitsOfSize_restrictFunctor` instance, rather than for its quasi-coherent
kernel theorem. The direct use of `lem-weil-pbc-quasi-coherent-module-kernel` is pruned.
Added the proof import `Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages`.
All existing public imports are unchanged.

## Where the brief, the DAG or earlier work was wrong

The existing dependencies do not supply the actual reduced-ring Schur-complement
normal-form conclusion. Definitions, field-rank invariance and radical equality alone
cannot close that geometric step by applying a stated theorem. The new node exposes
that exact step, and the rest of the planned argument is now implemented in Lean.

The source blueprint files are not materialized in this read-only clone. The source
text read was the unit record and the complete original node proof/docstring; the new
proof follows their normal-form argument. No literature file or repository file was
written directly. The existing unit record has empty realized lists; no unit statement
or route is altered. LeanSearch returned Internal Server Error, recorded as unavailable.
Loogle's Matrix.exists_rank_normal_form is only a square-matrix theorem over a field,
not the needed local rectangular-matrix theorem over a reduced ring.

## New nodes

`lem-pc-constant-rank-map-local-normal-form` in
`dag/nodes/sec-picard-framework/lem-pc-constant-rank-map-local-normal-form.json` states
local finite free block bases for the pullback map, with the exact snd/inl
factorization. It inherits the original chapter/unit and cites the same blueprint
normal-form sentence. Existing node, source-library, Mathlib and blueprint searches
found no matching reduced-ring local normal form. No change record is required:
no existing statement, definition or public import changed.

## Second reading by F1

1. Compared both delivered modules against the repository. The existing target declaration's
signature is byte-for-byte unchanged; the new declaration is recorded by its new DAG node.
The proof-only imports and the new module import match the declarations used.

2. Compiled both modules with `lcompile.py --all`; compilation succeeds. The target proof has
only the explicitly permitted `sorryAx` dependency from the split normal-form theorem; there
are no axioms, unsafe declarations, hollow definitions, or unlisted sorries.

3. Checked the split statement against the original normal-form argument and edge cases. It is
strictly intermediate: it gives local bases and the block factorization, while making no kernel
or image conclusion. Its docstring, source, and DAG node are present, and searches found no
existing equivalent declaration.

4. Read the proof top-down. The private abelian-category block calculation is fully proved,
and restriction preservation and the finite-locally-free covering criterion are applied directly.
The removed imports and pruned dependency edges are listed above; no shorter available library
route was found. The reduced-ring normal-form route required by the unit is retained.

5. Checked the DAG against the Lean declarations and proof dependencies. The new node records
the exact statement, source, proof steps, searches, chapter, and unit; the item's proof and
proof dependencies describe the imports and declarations actually used.

Changed during second reading: no mathematical or signature changes. Added this review section
to satisfy the stage-3 delivery record requirement.
