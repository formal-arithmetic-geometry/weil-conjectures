## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorRoute_descend`
without changing its statement. Private helpers package the target comparison and
the model map as natural transformations, accepting the typed derived pullback
and its named counit directly. A private generic descent theorem takes
an actual K-flat left resolution `w : R ⟶ P`, uses the hypothesis at `R`, and
cancels the invertible image of `Qh.map w` in the naturality equations.

The concrete residue specialization retains the supplied monoidal structure `m`
and the original canonical ordinary monoidal structure in the model map. No
coefficient flatness or K-flatness of the given `P` is assumed. No inverse of the
tensor-model target is used. The argument also covers zero complexes and empty
schemes: the left-resolution construction and functorial cancellation do not
require nonzero objects or points.

Updated the existing DAG node's proof, proof dependencies and proof origin to
record the resolution-arrow argument. The proof uses the stated model,
presentation, ordinary-monoidal and derived-monoidal interfaces. No existing
public signature was changed. The two concrete definitions in
`Sheaf.Paper.IntegralResidueTensorModel` now retain the existing named derived
pullback and counits in their bodies, preserving their explicit constructions.
The old expanded bodies caused concrete type conversions to hit the server's
60-second limit. `Functor.tensorModelMapWith` now constructs the same common
map from named data, paralleling `tensorModelTargetWith`; the legacy generic
map and the concrete map specialize it. The complete sandbox compiles: model
14.5 seconds, descent 45.5 seconds, and the three adapted consumers 47.6,
58.3 and 51.3 seconds through the required `lcompile.py` server tool.
All Lean lines are at most 100 characters.

Three unclaimed consumers require only proof changes:
`Sheaf.Paper.IntegralResidueTensorGeometry`,
`Sheaf.Paper.IntegralResidueScalarGeometryBridge`, and
`Sheaf.Paper.IntegralResidueScalarCounitModel`. The other five direct consumers
compile unchanged against the new model.

Change record: `coord/changes/A2-residue-tensor-model-named-data.md`.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorRoute_descend`
(node `new-integral-residue-tensor-route-descent`). The item's module now has zero
`sorry`s. The adapted tensor-model and all three adapted consumer modules also have
zero holes. Added zero holes and zero new nodes. The new explicit factory
`CategoryTheory.Functor.tensorModelMapWith` is attached to the existing
`new-integral-residue-tensor-model` node. Every private helper is fully
proved or explicitly constructed. This is a proof, not a decomposition.

## No longer needed

Removed these redundant direct imports, whose declarations are already publicly
imported by `Sheaf.Paper.IntegralResidueTensorModel`:

- `Sheaf.Paper.IntegralResidueDerivedMonoidal`
- `Sheaf.Paper.IntegralResidueOrdinaryMonoidal`
- `Sheaf.Paper.IntegralResidueTensorPresentation`

Their declarations remain needed through the model interface, so no module or DAG
node is claimed as pruned. The old essential-surjectivity helper
`Functor.residue_exists_kFlatMap_iso` is not used: descent uses an actual
homotopy resolution arrow. Its module remains needed for the derived monoidal
and left-derivability interfaces. No new dependency on tensor-route K-flat calculation,
scalar-route calculation, or tensor geometry was introduced.

## Where the brief, the DAG or earlier work was wrong

Delivery tooling is blocked after successful compilation and axiom probes.
On resuming at 07:08 on 2026-10-18, the worker retained the previous work,
checked its changes against the current shared sources, and began with the
required fresh dry run. It again reached preflight and failed for exactly one
reason: `uncommitted changes in the working tree`. The prescribed
`deliver3.py` commits the delivery, then its lines 299--304 rewrite the tracked
`tools/stage3_gate.py` before invoking preflight; the replacement still matches
the current tool text. Preflight rejects that resulting dirty tree. This is a
launcher-tool defect, independent of the Lean delivery. No tool was edited or
gate bypassed by this worker, and nothing was pushed. The complete compiling
proof, consumer adaptations, nodes and change record remain in this sandbox.
The fresh diagnostic output is `scratchpad/delivery-dry-run-3.log`; the previous
failure remains recorded in `scratchpad/delivery-dry-run-2.log`.

The original plan said to transport both model maps along an arbitrary derived
isomorphism. The ordinary tensor-model target has not been shown to factor
through the derived category, and no such assertion is needed. Instead take the
actual quasi-isomorphism `w : R ⟶ P` supplied by the `kFlatMap` left derivability
structure. Both transformations are natural on the homotopy category. Their
common source functor factors through `Qh`, so its image of `w` is invertible and
can be cancelled. The DAG now records this precise argument.

The original proof dependency list named only the derived-monoidal node. The
completed naturality calculation also uses the existing tensor-model,
tensor-presentation and ordinary-monoidal declarations; these are now recorded.

## Forced adaptations

The three adapted consumer modules are unclaimed. Their existing signatures,
visibility, and all other proofs are retained.

- `Sheaf.Paper.IntegralResidueTensorGeometry`: the original line 108 fails with
  `Type mismatch`, because `tensorModelTarget_isIso` concludes `IsIso
  (tensorModelTarget ...)` while the unfolded goal contains
  `tensorModelTargetWith ... (residueExchangeUpperStarCounit ...)`. The existing
  `delta` retains the concrete target unfolding. The same generic isomorphism
  theorem is applied with `with_unfolding_all` confined to its type conversion.
- `Sheaf.Paper.IntegralResidueScalarGeometryBridge`: the original line 93 fails
  with the same mismatch. Its identical local isomorphism proof receives the
  same local unfolding adjustment.
- `Sheaf.Paper.IntegralResidueScalarCounitModel`: the original line 287 fails
  with `Tactic unfold failed to unfold Functor.tensorModelMap`. Replace that
  name in the existing unfold command by `Functor.tensorModelMapWith` and
  `residueExchangeTensorCounit`, whose bodies now construct the common map.
  The last naturality rewrite
  closes the goal, so the two old trailing unfolding/simplification commands
  are removed; keeping them gives `No goals to be solved`.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
