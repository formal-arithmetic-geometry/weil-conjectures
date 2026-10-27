## What changed

The existing theorem
`AlgebraicGeometry.ProEtale.CondensedRing.supported_image_mem_bounded_derived_generation`
now has a complete Lean proof from two independent steps of its original argument:
source kernel generation (steps 1--5) and support-path preservation (step 6).
The proof derives qcqs instances for the source by path induction, proves exactness
of the actual path extension by induction, constructs the actual kernel-to-image
short exact sequence using `exact_kernel(u).isColimitImage`, maps that sequence by
extension, and applies `singleTriangle_distinguished` and triangulated third-vertex
closure. The source model is a defining generator. No theorem hypothesis changes.

The two explicit hull definitions move verbatim into
`Sheaf.Paper.SupportedImageGenerationHull`; the original module publicly re-exports
them. Both declaration names, universes, signatures and bodies are identical. All
original public imports remain. No target statement or definition meaning changes.
The change record is `coord/changes/G7-supported-image-hull-extraction.md`.
Its complete downstream inventory records the public re-export's unchanged effect.
The three textual consumers of the definitions need no source edits.

New proof modules are `Sheaf.Paper.SupportedModelKernelGeneration` and
`Sheaf.Paper.SupportedHullPathExtension`. Their statements are two different steps,
not renamed copies of the image assertion: the former has no support extension and
asserts membership of the kernel; the latter has arbitrary input N with known source
membership and no coefficient or finite-model assumption. The concluding image
short exact triangle, generator membership and path exactness are proved here.

## Proved and sorry left

Closed the one original textual hole:
`AlgebraicGeometry.ProEtale.CondensedRing.supported_image_mem_bounded_derived_generation`
(node `lem-sfb-supported-image-bounded-derived-generation`). No `sorry` remains in
the item module. Its three private helper theorems are fully proved.
The item compiled cleanly through lcompile.py in 10.1 seconds; all three new
supporting modules also compiled (42.2, 36.0 and 35.7 seconds).

The complete four-module sandbox compilation passed. In addition, unchanged copies
of SupportedImageRigidityFromModelComparisons, WeakSerreSupportedDerivedGeneration
and ClosedTorsionRigiditySerreTransfer compiled against the extracted definitions.
Those temporary copies were removed before delivery; no consumer source is delivered.

Added two textual holes, each the whole proof of a public theorem with a source,
full argument in words, and its own node:

- `AlgebraicGeometry.ProEtale.CondensedRing.finite_model_kernel_mem_supported_generation`
  (`lem-sfb-finite-model-kernel-generation`), original steps 1--5.
- `AlgebraicGeometry.ProEtale.CondensedRing.supported_hull_path_extension`
  (`lem-sfb-supported-hull-path-extension`), original step 6.

This is a decomposition, not net sorry closure: one upper hole closed and two lower
holes added, net minus one. The two extracted definitions have zero holes; no data
are chosen from an unproved existence result. The image assertion retains the same
five coefficient alternatives, all actual maps and all edge cases.

## No longer needed

No mathematical dependency or module is claimed pruned from the targets' closure.
The original component and support calculations are delegated to the two named
lemmas, whose node proofs retain the corresponding dependencies. The original
public imports are retained to preserve consumers. Removed private proof imports
from the item (the concluding assembly does not use them directly):

- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`.
- `Sheaf.AlgebraicGeometry.ComponentPullbackUnboundedEvaluation`.
- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`.
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`.
- `Sheaf.AlgebraicGeometry.ProEtale.SectionsConservative`.
- `Sheaf.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis`.
- `Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts`.
- `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`.
- `Sheaf.Paper.ComponentRelativeProfiniteSite`.
- `Sheaf.Paper.WContractibleComponentDerivedHom`.

The old top-level `tool_uses` approvals are removed from the item because those
inputs now occur below the two new nodes (or are superseded in the exactness
assembly by the proved `closedSupport_lowerStarExact` API). This is relocation of
the argument, not a claim that their mathematics is unnecessary. Removed approvals:

- `lem-weil-pbc-closed-in-quasi-compact`.
- `lem-weil-pbc-quasi-separated-affine-cover-criterion`.
- `sk-thm-pe-weakly-contractible-basis`.
- `lem-zl-component-relative-profinite-site`.
- `lem-sfb-wcontractible-component-derived-hom`.
- `sk-def-sfb-constructible`.
- `lem-weil-pbc-derived-single-fully-faithful`.
- `det-prop-sfb-module-pullback-exact-main`.
- `lem-sfb-component-pullback-unbounded-evaluation`.
- `det-pe-sections-conservative`.
- `det-pe-products-derived`.
- `lem-weil-pbc-left-adjoint-preserves-colimits`.
- `lem-sf-exact-functor-derived-triangulated`.
- `lem-weil-pbc-ringed-topoi-module-adjunction`.
- `lem-weil-pbc-proetale-ringed-open-closed`.
- `det-sf-open-closed-extension-zero-limits`.
- `lem-weil-pbc-right-adjoint-preserves-limits`.
- `lem-sfb-internal-module-operations-transport`.
- `sk-def-sfb-module-derived-pushpull`.
- `sk-def-sfb-derived-categories`.
- `lem-weil-pbc-complex-ses-triangle`.

The item's new `proof_deps` match the real Lean assembly. Its original unit's
statement and realization steps are unchanged; this item is a supporting node,
not a replacement route around a blueprint unit.

## Where the brief, the DAG or earlier work was wrong

The profinite relation-kernel source was absent when this session started, while its
current node already carried its Lean record. It appeared in the shared snapshot
during this session. I read its full signature and proof plan: it is the expected
`profinite_constant_model_relation_mem_hull`, for exactly the same five coefficient
alternatives and arbitrary actual arrows between scalar models on the profinite
slice. It remains a dependency of the source-kernel step; nothing is withdrawn or
restated. The hull-descent module is named
`Sheaf.Paper.SupportedModelHullProetaleDescent` and uses the equivalent finite-chain
hull. Its comparison with tree paths is an explicit part of the kernel step.

The existing item docstring still mentions full norm-topological algebraic-closure
coefficients even though the human's current coefficient restriction removed that
case from the statement. The actual five-case signature is preserved exactly.
No completeness or constant-rank assumption is used, and neither kernel lemma
claims that actual continuous-map kernels are finite scalar local models.

No false statement or unit-route error was identified. Zero maps give a kernel
isomorphic to the source model and zero image; identity maps give zero kernel and
the source image; the proof's exact sequences include empty sources and zero rings.
Support-path preservation includes the root identity functor and arbitrary N.

## New nodes

`def-sfb-supported-image-generation-hull` attaches the two unchanged hull definitions
to their new common module. This is extraction of existing data, not another hull.

`lem-sfb-finite-model-kernel-generation` records original steps 1--5 before support
extension. The original component inverse-image, profinite-kernel and descent
inputs remain its dependencies, with no unsupported assertion of finite model
closure under kernels.

`lem-sfb-supported-hull-path-extension` records original step 6 for arbitrary modules
already known to belong to the source hull. Its proof in words checks every defining
closure clause through the actual support functors and concatenation of paths.

Change record: `coord/changes/G7-supported-image-hull-extraction.md`.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
