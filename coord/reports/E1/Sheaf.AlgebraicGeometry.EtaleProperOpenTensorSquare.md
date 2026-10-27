## What changed

Completed `AlgebraicGeometry.Etale.etaleProperOpenTensorSquare` with its exact original
statement. Its invertibility conjunct applies the proved source torsion-ring interchange
theorem with `isAddTorsion_of_finite`. The tensor conjunct imports and applies the existing generic
`AlgebraicGeometry.Etale.mixed_projection` theorem in
`Sheaf.AlgebraicGeometry.CompactificationProjectionComposition`, with symmetry.

Repair of return at `7cc2beb7a`: removed all five duplicate private declarations from the
item: `mixed_projection`, `open_exchange_mate`, `fixed_tensor_mate`, `mate_ofNatIsoLeft`
and `right_projection_mate`. The item uses Lean's `import all` to access the existing
private `mixed_projection` by name. Its original module and all five original proofs are
unchanged. No declaration is copied, renamed or made public. All source-tree modules stay
untouched.

The item's only private proof import is now
`import all Sheaf.AlgebraicGeometry.CompactificationProjectionComposition`.
Updated the node proof, proof dependencies and origin to this implemented argument, and
removed obsolete tool approvals while retaining the surviving ones in their original order.
The unit route, node statement, statement dependencies and theorem signature are unchanged.

The public import removal is recorded in
`coord/changes/etale-proper-open-tensor-square-imports.md`; there are no downstream Lean
importers of the item to adapt. The item remains needed by its DAG parents.
No other module is delivered and no forced adaptations are needed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Etale.etaleProperOpenTensorSquare`
(node `lem-sf-etale-proper-open-tensor-square`). Added zero holes and split off zero statements.
There are zero textual `sorry`s in the delivered Lean module.

The existing private mixed-square theorem is fully proved and remains unchanged.
Reusing it closes no additional hole and adds none. `lcompile.py --all` accepted the repaired
item (exit 0, 16.1 seconds, no diagnostics), against the unchanged original module.
`tools/import_prune_check.py` accepted the duplicate-free repair; import-direction checking
confirms no cycle. The delivery command performs final compilation, axiom checks and preflight.

## No longer needed

Removed these private imports; the two conjuncts use the source invertibility theorem
and the existing mixed projection theorem instead:

- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.SixFunctors.OpenTensorNormalizationData`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`
- `Sheaf.AlgebraicGeometry.EtaleModuleStalkCohomologyTest`
- `Sheaf.AlgebraicGeometry.OpenImmersionExtensionZeroBaseChange`
- `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`
- `Sheaf.AlgebraicGeometry.GeometricStalkAsPullback`
- `Sheaf.CategoryTheory.FullyFaithfulMate`
- `Mathlib.CategoryTheory.Adjunction.Mates` (available through the imported theorem module)
- `Sheaf.AlgebraicGeometry.EtaleOpenProjectionExchange` (the imported theorem already uses
  its underlying source identity for arbitrary Cartesian squares)
- `Sheaf.CategoryTheory.Adjunction.TensorSquareMateTransfer` (the fixed-input mate
  calculation is already proved in the imported module)

Removed the unused public import `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`.
The statement retains the canonical source `derivedSquareUpperStarIso`; no generic
ringed-site comparison system is needed to identify these actual constant-coefficient maps.

Removed these dependencies from the item's proof plan:

- `lem-pur-site-restriction-module-adjunction-exact`
- `def-weil-exact-derived-adjunction`
- `lem-weil-pbc-extension-by-zero-stalks`
- `lem-sf-etale-module-stalk-cohomology-test`
- `sbc-prop-extension-by-zero-and-arbitrary-base-change`
- `lem-kun-stalk-as-pullback`
- `lem-weil-pbc-fully-faithful-mate-image`
- `lem-sfb-ringed-derived-monoidal-comparisons`
- `lem-sf-tensor-square-mate-transfer`

The source interchange theorem already proves the invertibility conjunct, so no separate
stalk/cone/full-faithfulness proof is required here. Proper unbounded base change remains a
mathematical dependency through that source theorem. The ordinary open projection exchange
remains as the source identity that supplies the tensor square; the stronger uncurried mate
transfer theorem is unnecessary. These modules/nodes may still be used elsewhere; this
packet neither deletes them nor claims global unreachability.

Compared with the returned packet, also removed its direct private imports of
`WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange`
and `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat`: the item
no longer repeats any mate calculation. All five copied private helpers are removed;
all five originals remain proved in their existing module.

## Where the brief, the DAG or earlier work was wrong

The original plan was valid but longer than necessary: the source library already proves
the exact invertibility conjunct, and the private `mixed_projection` calculation in
`CompactificationProjectionComposition` proves the exact tensor equation (also noted by
the stage-2 reviewer). Importing that existing theorem avoids the unfinished generic tensor-square
lemma and the ringed-site realization machinery. No mathematical statement repair is needed.
The earlier packet copied five private helpers even though their existing statements
were already present; this was the defect named by the return. The repair uses
`import all` to access the existing private theorem, as supported by Lean and already used
in this library. It repeats none of the five helper statements or proofs. The old
docstring proof remains an alternative valid argument; the DAG describes the actual reuse.

The source statements were checked for arbitrary schemes, arbitrary opens and unbounded
complexes. Finiteness is used only to obtain additive torsion for invertibility; the tensor
calculation uses neither properness nor finiteness. Empty opens, identity maps and the zero
coefficient ring require no extra hypotheses, and no projection map is inverted.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
