## What changed

Replaced the proposed affine/glue decomposition by a direct proof in
`Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelStabilizedSystem`.
The existing signature, visibility, docstring and public import are unchanged.
For each n, construct the image of ker(alpha_(n+c)) -> F_n. Shifted kernel maps
and Mathlib image maps give the transition maps. Cancel the monic inclusions to
check the functor laws and naturality, then use `Abelian.imageIsoImage` to obtain
the specified component isomorphisms. No additional import is needed.

## Proved and sorry left

Closed: `AlgebraicGeometry.coherentFormalModule_kernel_stabilized_system`
(node `new-kernel-stabilized-system`), the only original hole (1 of 1).
Added holes: none. Remaining holes in the delivered module: none.
The proposed holes `coherentFormalModule_kernel_stabilized_system_affine` and
`coherentFormalModule_kernel_stabilized_system_glue` were removed together with
their unlanded modules and nodes. This is a proof, not a decomposition.

## No longer needed

The proposed private import of
`Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelStabilizedSystemGlue` is removed.
The unlanded modules ending `Affine` and `Glue`, and nodes
`new-kernel-stabilized-system-affine` and `new-kernel-stabilized-system-glue`,
are omitted entirely. The repository node's old `proof_deps` was empty: no
previously landed dependency node or module is pruned. The original public
import is required by the statement and retained.

## Where the brief, the DAG or earlier work was wrong

The proposed "affine" statement was already a global existence statement, with
an unrelated natural transformation and no inclusion compatibility; the "glue"
statement repeated the target conclusion with this weak extra premise. Their
docstrings did not describe their Lean statements or a complete reduction.
These were rejected rather than delivered. The original affine/gluing plan is
unnecessary for this auxiliary assertion: images of shifted kernels form a
system for every c, even without stabilization. No coherence, quotient,
stabilization-bound or formal-kernel assertion is bypassed or changed.
Source checked: Stacks 087X, https://stacks.math.columbia.edu/tag/087X,
where K'_(l,m) are the same kernel images. The local cited TeX is not present.

## Second reading by B3

1. PASS after repair. Compared the module against the repository with `diff`;
the existing declaration signature is byte-for-byte unchanged. No definition,
statement, visibility or public import changes; no change record is needed.
2. PASS. Compiled the final module locally through lcompile.py. No sorry,
axiom, unsafe, opaque, implemented_by or extern. The scratch #print axioms
check and delivery probe verify the allowed axiom set; no data is chosen from
an unproved existence statement. The image objects and maps are concrete
Mathlib constructions from universal properties.
3. PASS after removal. No split-off statements or new nodes remain. Independent
Loogle search for image.map and LeanFinder search for commutative squares and
image inclusions found image.map_homMk'_ι; rg searches in the upstream library,
Sheaf and Mathlib found the kernel and image API used here. Edge cases c = 0,
zero alpha, and monic alpha are covered by the same construction: no positivity,
nonzero-image or epimorphy assumption is used.
4. PASS after repair. Direct Mathlib image construction is shorter than affine
construction/gluing and requires no extra imports. All rejected proposed
modules/nodes are listed above; original proof_deps is empty. Read
`dag/units/sk-thm-p1.json`, including its realized statement and steps: this
auxiliary categorical construction changes none of the unit's route.
5. PASS. The existing node's proof and proof_origin now describe the actual
kernel/image-map construction; proof_deps remains empty because there are no
additional project theorem dependencies. Node statement and other fields are
unchanged. No new node needs auditing.

Changes by the second reader: replaced the entire defective reduction with a
complete direct proof, removed both proposed split modules/nodes and their
import, corrected the existing node proof metadata, and rewrote this report.
