## What changed

Proved `AlgebraicGeometry.Scheme.Modules.ideal_tensor_image_comparison` with its
signature and visibility unchanged. Added proof-only imports of
`Sheaf.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage` and
`WeilConjectures.AlgebraicGeometry.Modules.Dual`.

The geometric step specializes `closedSubscheme_baseChange_ideal_image` to
`I.subschemeι`. Pullback symmetry identifies the extended ideal; uniqueness of
left adjoints makes the image comparison independent of the adjunction.
The rest constructs an actual isomorphism of module sheaves using
`imageMonoIsoSource`, tensors the ideal-image isomorphism with the specified
ambient isomorphism, proves its multiplication square, and evaluates on the top
open. No invertibility of the original module N or flatness of f is needed.

Updated the existing node's proof, proof_deps, and proof_origin to this route.
The unit's realized statement and steps are unchanged.

## Proved and sorry left

Closed 1 of 1 holes in the item:
`AlgebraicGeometry.Scheme.Modules.ideal_tensor_image_comparison`
(node `lem-sc-ideal-tensor-image-comparison`). No holes remain in this module;
no holes or statements were added. This is a proof from existing declarations,
not a new decomposition.

The geometric input
`AlgebraicGeometry.closedSubscheme_baseChange_ideal_image`
(node `lem-pc-closed-subscheme-base-change-ideal-image`) already has a `sorry`
in its own module and remains a dependency to be proved. It is not a new hole
in this delivery. Local single-file compilation passed without warnings.

## No longer needed

No original import was removed: the public imports supply the unchanged
statement. Both new proof-only imports are used.

The former direct proof dependencies
`lem-weil-pbc-module-pullback-affine-sections`
(`Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`) and
`lem-pc-ideal-sheaf-comap-affine-extension`
(`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`) are unnecessary
for this proof: the existing base-change ideal-image theorem supplies the whole
geometric identification. They were never imported by the item's original
module, and are not imported by this delivery. This is pruning of the planned
direct dependencies, not a claim that no other target or module needs them.

## Where the brief, the DAG or earlier work was wrong

The original plan proposed a fresh affine computation and gluing argument, but
the library already states the complete geometric image identification in
`closedSubscheme_baseChange_ideal_image`. Specializing it avoids duplicating
that argument. The original statement is preserved. Empty schemes, zero and
unit ideals are covered by the same categorical proof, with no nonemptiness or
injectivity of the pullback of an ideal inclusion assumed.

## Second reading by U3

1. Compared the delivered module with the repository version. The theorem
   signature, visibility, and existing declarations are unchanged; only
   proof-only imports and the proof body differ. Verdict: pass.
2. Compiled the module and sandbox import closure with `lcompile.py`. The
   delivered module has no `sorry`, `axiom`, unsafe declaration, or hollow
   definition. The scratch axiom report's `sorryAx` comes only from the
   imported open base-change theorem. Verdict: pass.
3. Checked the route against the node statement and existing declarations.
   The base-change ideal-image theorem supplies the geometric identification;
   the tensor and evaluation argument proves exactly the displayed additive
   equivalence. No new statement was introduced and the target statement is
   unchanged. Verdict: pass.
4. Checked pruning and imports. Both added imports are proof-only and used;
   the former affine-computation dependencies are absent. The unit's realized
   statement and route are retained. Verdict: pass.
5. Compared the DAG node with the Lean proof. Its proof steps, dependencies,
   and proof origin describe the categorical route and include the existing
   base-change node; no new node or split-off hole is needed. Verdict: pass.

Changed only this report section during second reading; no Lean repair was
needed after compilation.
