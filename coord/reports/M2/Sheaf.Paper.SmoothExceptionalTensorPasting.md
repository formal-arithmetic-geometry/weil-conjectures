## What changed

Filled the five theorem proofs in `lean/Sheaf/Paper/SmoothExceptionalTensorPasting.lean`.
All existing theorem signatures and public imports are unchanged. The chain-coherence
predicate groups its four tensor laws through the new generic `tensorComparisonCoherence`
definition, then conjoins the unchanged threefold-pullback equation through the generic
`complexThreefoldComparisonCoherence`. This shares the whole complex comparison
family before specialization to the six actual pullbacks and four compositors. The induced oplax
delta and eta are exactly the original chain comparison and inverse unit isomorphism.
The canonical complex braided instance gives the same Koszul braiding. The four fixed-object derived tensor laws share
`tensorComparisonCoherenceAt`, with the source whiskering conversions proved
generically. The derived localization square writes its same two
counit maps explicitly to use the proved specialized source theorem; its other three
clauses are unchanged.
Private proved helpers reuse the proved horizontal exchange and identity normalization calculations,
and implement vertical mate pasting, the unit specialization and naturality of the specified theta.
The final coherence proof works over a general coefficient category before specialization.
Generic helpers check both tensor coherence and the threefold complex comparison
before specializing to the actual sheaf pullbacks. Canonical coefficient braiding
instances match the generic calculation at specialization.

Updated `lem-pur-smooth-exceptional-tensor-pasting` to describe the actual proof route.
No other Lean module is changed. The equivalent predicate representation is recorded in
`coord/changes/M2-chain-reassociation-expression.md` and
`coord/changes/M2-derived-reassociation-expression.md`. Consumer scans found no external
textual use of either predicate; downstream consumers require no adaptation.
The proof imports existing private calculations through `import all` of
`SectionExceptionalFibreCoherence` and `UnboundedEtaleCompactSupportComparisons`.
Theta naturality is proved here from `projectionTensorMap_naturality_right` and
`leftUnitor_naturality`, via a generic coefficient-category calculation before specialization.
Canonical cached sheaf and cochain instances avoid repeated expansion; the local attributes
and elaboration options do not change the public constructions.

## Proved and sorry left

Closed the five original holes, in namespace
`AlgebraicGeometry.ProEtale.SmoothExceptionalPasting`:

- `smoothExceptionalTensorPasting`.
- `smoothExceptionalBasePasting`.
- `smoothExceptionalIdentityPasting`.
- `smoothExceptionalTowerPasting`.
- `smoothExceptionalReassociationPasting`.

The item contains zero remaining `sorry`. Added zero holes and split off zero statements.
The proof uses existing named dependencies, including `tensorMateBaseChange`; their
existing holes are not new holes or claims of this delivery.

## No longer needed

Removed private proof imports:

- `Sheaf.Paper.ProEtaleConstructibleOrigin`.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`.
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`.
- `Sheaf.Paper.SmoothExceptionalBaseChangeStatement`.
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`.
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`.
- `Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence` (the proved helper imports it).

The following old proof dependencies are unnecessary for this item's proof:
`lem-kun-dimension-finite-type`, `lem-sf-proetale-constructible-origin`,
`thm-weil-pbc-site-comparison`, `def-weil-exceptional-inverse-image`,
`thm-sf-ambient-adjoint-class`, `lem-sf-class-compact-support-comparison`,
`lem-weil-pbc-comparison-pullback`, `thm-pur-cohomological-smoothness`,
`lem-weil-finite-compact-projection-formula`,
`lem-weil-pbc-proetale-derived-pullback-composition`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, and
`lem-pur-cochain-pullback-tensor-coherence`.

The statements already use etale coordinates and map them through the specified
comparison functor. Thus no ambient adjunction transport or dimension bound is needed.
Smooth exceptional invertibility comes from the proved source-library smooth base-change
theorem. The tensor equation is precisely the existing tensor-mate dependency.
Theta naturality uses naturality of the source projection map and its adjunction
transpose. This avoids importing `Sheaf.Paper.SmoothPurityMap` solely for its private
helper; that import brought 750 additional modules into this file's transitive imports.
`def-pur-smooth-purity-map` is therefore unnecessary as a proof dependency. The reassociation equations are already proved for the actual
source pullback, tensor and cochain functors, so the planned additional coherence modules
are unnecessary. Statement dependencies and public imports are retained. These removals
do not assert that the modules have no other consumers. No module is withdrawn.

Removed the corresponding obsolete top-level `tool_uses` entries for the dimension,
origin, comparison, ambient adjunction, cohomological smoothness, pullback/tensor
coherence and finite projection formula inputs. Retained approvals stay in their
original order. The unit's own statement and proof steps are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement was found false. The planned transport through a class-restricted
pro-etale adjunction was unnecessary for the published coordinate statements.
Horizontal pasting reuses the proved private calculation in
`SectionExceptionalFibreCoherence`, which uses the specified `affineLinearExchange_paste`
equation. Its existing node is recorded as a proof dependency. Vertical pasting uses the actual specified
unbounded compact-support compositor, rather than an arbitrary choice of compositor.
The coefficient-unit specialization is proved here and does not import another
unproved exceptional dualizing-pasting theorem. The generic two-variable localization
statement and its counit expansions were costly to instantiate. The predicate now
writes the same maps explicitly, matching the proved specialized source equation.

The equivalent predicate repairs have change records
`coord/changes/M2-chain-reassociation-expression.md` and
`coord/changes/M2-derived-reassociation-expression.md`. The mathematical node statement
and unit route are unchanged; no new node or hole is introduced.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
