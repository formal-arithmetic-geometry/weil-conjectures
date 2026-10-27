## What changed

Proved `AlgebraicGeometry.ProEtale.LatticeTree.qcqs_lattice_tree_reconstruction` uniformly
for arbitrary coefficient families and then specialized it to both families in the statement.
The item's public signatures and public imports are unchanged. `Reconstruction` now uses
a local abstract-ring `derivedScalar` let whose beta reduction is the original body; see
`coord/changes/R2-qcqs-reconstruction-derived-scalar-let.md`. Private proved root/open/closed
equations keep the existing path definitions folded inside module objects. This avoids costly
recursive normalization without changing `QcqsOpenClosedTree` or splitting the proof.

Branch induction proves preservation of finite constant scalar models and tensor flatness.
The proof reuses existing proved private constructibility, flatness, and flat-single scalar
helpers, introducing no duplicate public statements. For a closed edge, it proves that the actual
canonical `pushHom` is an isomorphism by open/closed restriction and the mate/counit identity.
This establishes the required `scalarComparison`, not merely existence of some comparison.
Flat leaf singles have Tor amplitude [0,0]. The existing flat-single scalar comparison
identifies derived scalar extension on these singles with ordinary scalar extension; the supplied coefficient-flatness hypothesis is
therefore unnecessary for this part of the conclusion.

A second induction first treats replete properties of ordinary module objects under an
exact additive functor into an arbitrary abelian category. Its localization step then
maps the localization triangles and combines the child extension products using `ObjectProperty.extensionProductIter_add`. This keeps all
connecting maps over the fixed root coefficient ring. Updated the node proof and dependencies
to describe this route. The blueprint unit and its realization route are unchanged.

Checked the mathematical edge cases: a root that is already a leaf gives iteration zero;
empty leaves and zero models use rank-zero finite constant models; a split may have an empty
child; branch rank and integral field may vary; the scalar comparison requires no flatness,
and the flat-single derived comparison needs only flatness of the branch model.

Validation: the complete formatted item compiled successfully. The final proof was also
compiled against the original tree definitions. Lean checked
`Reconstruction = OriginalReconstruction` by `rfl` (21.3 seconds). All six original path
equations and the branch isomorphism API compile separately; the equation API reduces branch
kernel checking to 130 milliseconds with the original tree. No tree dependency is changed. The unchanged `PadicAlgClConstructibleScalarRestriction`
consumer proofs `field_reconstruction`, `branch_model_open`, and `branch_model_closed`
also compiled against the completed item (3.1 seconds).

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.LatticeTree.qcqs_lattice_tree_reconstruction`
(node `lem-sfb-qcqs-lattice-tree-reconstruction`).

Holes closed: 1. Holes added: 0. Sorries remaining in the delivery: 0. No decomposition,
new axioms, hollow definitions, or admitted private helpers.

## No longer needed

Removed the original proof-only imports:

- `Mathlib.Topology.Constructible` (available through the stratification API).
- `Sheaf.Paper.CartesianCoefficients`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`.
- `Sheaf.AlgebraicGeometry.ProEtaleClosedUnderivedProjection`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.Algebra.Homology.RingedFlatSingleTensorCohomology`.
- `Sheaf.Paper.FlatSingleScalarConventions`.
- `Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`.

The corresponding old direct proof dependencies are no longer used by this item's route:
`sk-prop-sfb-cartesian-coefficients`,
`lem-pur-proetale-inverse-image-tensor-comparison`,
`lem-exc-open-closed-detection`, `def-pc-flat-sheaf-modules`,
`def-pur-sheaf-tensor-product`, `lem-weil-pbc-ringed-slice-extension-tensor`,
`lem-weil-pbc-proetale-closed-underived-projection`,
`lem-weil-proetale-weakly-etale-localization`,
`lem-fd-ringed-flat-single-tensor-cohomology`,
`lem-sfb-flat-single-scalar-conventions`, and `lem-sf-derived-ses-triangle`.
Normalized module-object tensor/detection APIs, canonical mates, the generic source flat-single
theorem, the existing flat-single scalar comparison, and the existing recollement triangle
replace these ringed-site bridges. The ringed-open/closed node remains a statement dependency through the existing public
imports, even though its theorem is not used in this proof. No module is withdrawn; these are
item-level dependency removals, not claims that other consumers no longer need the modules.
The obsolete entries were removed from the node's `tool_uses`, retaining the others in order.
The reused flatness helpers come through IntegralModelsGenerators, which still imports some
of these modules for its own proofs; no transitive-closure pruning is claimed for them.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. Directly reducing the recursive path functor inside module
objects caused kernel-normalization timeouts; rewriting through proved equations avoids them.
No target statement is changed. The independent reader should confirm the unchanged meaning
through the beta-equivalent local let in `Reconstruction`. The DAG's ringed-site comparisons were a valid
plan, but the library already has normalized condensed-module APIs and generic exact-derived
comparisons that avoid those bridges. Existing public constructibility results often require
Noetherian schemes; their proved private stratification helpers and the flatness kernel test
work with the qcqs tree hypotheses, so no Noetherian hypothesis was added.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
