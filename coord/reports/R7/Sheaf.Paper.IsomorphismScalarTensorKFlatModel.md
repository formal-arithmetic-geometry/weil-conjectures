## What changed

The unchanged theorem `AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.isomorphism_scalar_tensor_kflat_model`
is assembled from two strictly smaller cochain obligations and a proved normalized derived descent.
The private `descend_model` constructs source and target representative counits, proves them invertible
on good complexes, obtains good resolutions from the existing resolution theorem, and applies the
universe-polymorphic categorical descent argument already proved in `IsomorphismScalarKFlatDescent`.
Evaluating its normalization on the identity resolution proves exactly `DerivedModel`.
The cochain counit is formed directly from the existing homotopy counit; a private computation
lemma keeps the K-flat argument separate from the larger model record.

The 21 original model definitions and specification predicates move verbatim to the new
`Sheaf.Paper.IsomorphismScalarCompletedModel`; the original item publicly reexports that module.
All original names, signatures, bodies, visibility, and public imports remain available. The two
statement modules avoid a cycle by putting that unchanged vocabulary below the item's assembly.
No arbitrary witness is chosen from either new holed theorem.

Change record: `coord/changes/R7-isomorphism-scalar-model-vocabulary.md`.

Validation: both new modules compile (reported elapsed 53.8 s and 53.2 s); the final item
compiles without errors or warnings (reported elapsed 45.8 s). All five direct importers
compile unchanged against this overlay: ExplicitScalarConeWordCoordinates,
PointRestrictionOrdinaryTensorSquare, PointInverseImageCoefficientTower,
IsomorphismScalarAugmentationCone, and PodReindexingGoodComplex. The compile service accepts
each within its separate 60 s Lean-runtime check; reported elapsed times also include
overlay/cache preparation. Their unchanged temporary source copies have been removed.

## Proved and sorry left

One original hole is closed in the item's theorem:
`AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.isomorphism_scalar_tensor_kflat_model`
(node `lem-weil-isomorphism-scalar-tensor-kflat-model`). The item itself has zero remaining holes.
The normalized derived descent in the private `descend_model` is fully proved.

Two holes are added, each as a whole public theorem proof in its own module:

- `AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.scalar_completed_model`
  (`lem-weil-isomorphism-scalar-completed-model`): completed comparison and preservation,
  with no finite quotient or derived assertion.
- `AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.scalar_finite_model`
  (`lem-weil-isomorphism-scalar-finite-model`): finite comparisons and quotient/transition
  squares for a supplied completed comparison, with no preservation or derived assertion.

This is a decomposition: one original hole closed, two strictly smaller holes added;
the textual net is minus one. Neither new theorem is the original statement under another name.
The lowest quotient index, zero complexes, empty sites, ramified extensions and nonflat
coefficient maps require no extra hypotheses; the balanced tensor rules and exact inverse-image
argument apply in those cases as described in the theorem docstrings.

## No longer needed

Removed the item's four old proof imports:
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`Sheaf.Algebra.Homology.ChangeOfRingsKFlat`, `Sheaf.Paper.PurInverseImageTensorHom`,
and `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
The actual derived assembly uses the existing categorical normalized resolving-class descent,
not a separate two-variable tensor descent. Its direct proof dependencies are the two specialized
cochain statements, K-flat resolution, derived change of rings, and the existing scalar descent
module's generic proved categorical helpers.

The original generic limit-chain and quotient-chain lemmas remain needed by the new specialized
obligations; they are not pruned. Likewise inverse-image coefficient naturality and scalar-extension
coefficient maps remain needed there. The new completed specialization uses the direct ringed-topos
K-flat pullback interface, not the much larger canonical two-variable derived tensor theorem.
The original direct uses of `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-pur-kflat-change-of-rings`, `lem-pur-isomorphism-inverse-image-tensor-hom`, and
`lem-weil-pbc-site-derived-tensor-descent` are replaced by that route; their corresponding obsolete
item `tool_uses` entries are removed. The inverse-image tool approval also leaves the item and is
used within the specialized obligations. No module is withdrawn, and no source-library declaration
is removed or changed.

## Where the brief, the DAG or earlier work was wrong

The advertised generic declarations exist, but do not apply by definitional equality to this item.
`LimitScalarChainComparison` and `IsomorphismScalarQuotientChainSquares` use their own ordinary
extension functors. This item uses independent chosen tensor presentations, whose object/map
normalizations require explicit natural presentation identifications. The finite scalar reduction
also uses a different coefficient-map presentation. Those identifications and their tensor-generator
rules are the precise remaining cochain obligations, documented with the existing generic lemmas
as dependencies. The published geometric `scalar_kflat_descent` additionally fixes the coefficient
universe to the site universe, while this item keeps them independent. Its existing private
categorical descent construction is universe polymorphic and supplies the proved descent here.

The current rework row concerns the quarantined false-tail import closure. The current item source
is present and its baseline compiles; it is preserved, with no deletion or quarantine workaround.

## New nodes

`lem-weil-isomorphism-scalar-completed-model` records the original completed-coefficient
compatibility, normalized chain comparison, and K-flat preservation steps in the actual tensor
presentations. Its sources are Stacks 03EL/0G7E, the specified coefficient-limit calculation,
and the original completed comparison argument.
The existing auxiliary definitions are attached here and remain publicly reexported by the item.

`lem-weil-isomorphism-scalar-finite-model` records the original balanced finite reassociation,
quotient maps, transitions, and their squares for a supplied normalized completed comparison.
Its source is Stacks 03EK/03EL and the original Steps 4-5. LeanSearch, Loogle, LeanFinder and local
source/blueprint searches found generic tools but no duplicate with these presentations.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
