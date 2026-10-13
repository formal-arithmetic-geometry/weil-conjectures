## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Scheme.Modules.exists_finiteType_affine_enlargement` by a complete
Lean proof of the global extension and image step, preserving its signature and visibility.
The local affine construction and gluing (original node steps 1--3) are separated into
`Sheaf.AlgebraicGeometry.ModuleFiniteTypeAffineUnion`, whose one public theorem constructs
only the finite-type submodule on the union. This is strictly part of the argument: it
provides no module or inclusion on X outside the union.

The main proof establishes compactness of the union, applies the existing quasi-coherent
extension theorem, and constructs the global submodule as the abelian image of the extended
map. Its restricted factor through the image is monic and epic, hence an isomorphism.
The proof transports finite local generators along that isomorphism and uses
`overFunctorMap` to compare restriction to W with further restriction from the union.
It proves that the image inclusion is an isomorphism on W by categorical cancellation.
Quasi-coherence uses the proved source-library kernel and cokernel closure theorems,
without the much stronger affine-section image formula.

The new module has its source, complete natural-language proof, blueprint tag and matching
DAG node. The original node's proof, dependencies and origin describe the actual reduction.
Both modules compile through lcompile.py; the original module's last single-file compile
completed without warnings in 35.8 seconds. No definitions, existing signatures, target
statements, public imports of existing modules, or other held modules were changed.

## Proved and sorry left

Closed original hole:
`AlgebraicGeometry.Scheme.Modules.exists_finiteType_affine_enlargement`
(node `lem-weil-pbc-module-finite-type-affine-enlargement`). There are no sorries left
in the item's module.

Added hole:
`AlgebraicGeometry.Scheme.Modules.exists_finiteType_affine_union`
(node `lem-weil-pbc-module-finite-type-affine-union`), in the new module
`Sheaf.AlgebraicGeometry.ModuleFiniteTypeAffineUnion`. Its whole proof is `:= by sorry`.
It isolates finite numerators, the affine submodule, and gluing on the union, with no global
extension/image step. Empty overlap, empty W and empty V were checked in the mathematical
construction; the empty finite set of numerators gives the zero submodule on V when needed.

This delivery is a decomposition: one upper hole closed, one strictly local hole added,
net zero holes before changes in the import closure. It does not claim an unconditional
sorry-free proof. It also uses the existing, unchanged holed theorem
`AlgebraicGeometry.Scheme.Modules.exists_quasiCoherent_extension_of_quasiCompact_open`.
The kernel and cokernel closure theorems used instead of the image-sections package are
already proved. The data in the global argument are constructed as an abelian image;
no definition chooses arbitrary data from an unproved existence theorem.

## No longer needed

Removed direct proof imports from the item's module:

- `Mathlib.AlgebraicGeometry.Modules.Tilde`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`.
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`.

The first three concern the affine construction, now isolated in the local-union node.
Their mathematical facts remain needed by that new node and are not claimed as globally
pruned. In particular its proof dependencies retain
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-spec-module-tilde-sections`,
`lem-weil-pbc-principal-localization-open-immersion`, and
`lem-weil-pbc-quasi-coherent-finite-type-affine`.

The original route's dependency
`lem-weil-pbc-quasi-coherent-module-cokernel-image` and its module
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage` are not needed anywhere in
this reduction, including the new local-union lemma. Its affine sectionwise image and
cokernel formulas, local-image characterization, and associated Cech-acyclicity machinery
are unnecessary here. Only quasi-coherence of the categorical image is needed; the source
kernel and cokernel closure theorems provide it. No unit-level statement or route is bypassed.
No other original planned dependency is claimed as discarded: the affine ones moved to
the new node, and the restriction, finiteness, compactness and extension facts remain.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The planned cokernel/image dependency provided more than the
proof needs. Its quasi-coherence component has a shorter proved route in the source library.
The existing affine finite-type theorem gives finiteness criteria, but not the actual
finite-numerator submodule and gluing required in steps 1--3; those are explicitly retained
as the new local-union item rather than treated as an automatic consequence of that criterion.
LeanSearch returned an Internal Server Error; the other search kinds and local source
inspection were used. The cited literature file is absent in this clone, so the proof of
Stacks Tag 01PF was read at https://stacks.math.columbia.edu/tag/01PF.

## New nodes

`lem-weil-pbc-module-finite-type-affine-union` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-module-finite-type-affine-union.json`,
realized by `AlgebraicGeometry.Scheme.Modules.exists_finiteType_affine_union` in
`lean/Sheaf/AlgebraicGeometry/ModuleFiniteTypeAffineUnion.lean`. It packages the original
first three steps only: finite numerators on V and gluing with H on W, yielding a
finite-type quasi-coherent submodule on W union V. It retains those steps' dependencies,
source and proof in words, and records the searches and the edge cases.
No change record is needed: every existing interface is unchanged.

## Second reading by S3

1. Compared `ModuleFiniteTypeAffineEnlargement.lean` against the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports and proof text differ. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py`; no errors or warnings. The enlargement proof has no `sorry`; the only remaining `sorry` is the named split theorem `exists_finiteType_affine_union`, and no forbidden declarations or hollow definitions occur. Verdict: pass.
3. Checked the split statement and node against the source argument and searched the local library for duplicates. The union theorem is a strict local reduction, with its own natural-language proof and DAG node; it does not restate the enlargement target. Verdict: pass.
4. Read the proof top-down. It uses the local union construction, compact-open extension, abelian image factorization, and kernel/cokernel quasi-coherence; the affine image-sections dependency was pruned as unnecessary. Verdict: pass.
5. Compared the enlargement and union DAG proof, dependency, origin, unit, and realized records with the Lean proof and imports. The unit route remains represented, and the new union node records the retained affine steps. Verdict: pass.

Changed during second reading: no proof or statement changes were necessary; this report section records the checks. The delivery remains a decomposition: one target hole is closed and one strictly simpler local hole remains.
