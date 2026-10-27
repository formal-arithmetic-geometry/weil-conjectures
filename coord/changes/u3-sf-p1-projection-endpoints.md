# AlgebraicGeometry.Etale.SfP1Transport.projectionComparison

## Reason

The delivery path of this record is `coord/changes/u3-sf-p1-projection-endpoints.md`.
If the reviewer supplies a replacement through `--apply-fixes`, its flat
filename must be `u3-sf-p1-projection-endpoints.change.md`, as required by
`tools/batch_land.py` (the repository record itself keeps its `.md` name).
The C-d31b0 return was a failure to match that reviewer replacement filename;
the record is included in this packet.

The unclaimed Sheaf module mixed the raw derived-functor endpoint of proper
forget-supports with the recorded ordinary direct-image functor. They represent
the same functor, but matching their component composites repeatedly expanded
large localization constructions and exceeded the compile limit. Record the
ordinary endpoint through ordinaryProperForgetComparison, which is constructed
from the original canonical isomorphism itself. No morphism is selected from an
undetermined existence theorem. All existing declaration signatures and public
attributes are preserved.
The current main imports stay in their original order; one public import supplies
ordinaryProperForgetComparison. Main's already-landed SfP1SupportedExtMapData
continues to own and re-export supportedMap. The duplicate unlanded U3 constructor
module, node and relocation change record were removed as requested in the return.

The mathematical node statement is unchanged; its statement dependencies gain
the canonical endpoint wrapper used to implement that same construction.
This definition is in the targets' dependency closure, so the independent
statement review must recheck any target whose definition closure uses it under
stages/2-statements.md section 4. No target signature is changed. The construction
is the same proper forget-supports map, coefficient inverse and exchange as before.

A local section marks ordinaryFinitePushforward irreducible only while checking
these two bodies. This prevents endpoint unfolding during elaboration; the
attribute ends before the next declaration and is not exported to consumers.

Declaration checking is sequential within this module (`Elab.async false`).
This is a file-local scheduling option, with no resource limit or exported
instance change. The local stored-instance setup already present in current
main is retained in place. E1's traceComposite, presentationTrace,
presentationTrace_assoc and factored trace body are kept verbatim. No further
data body is changed. Main's node proof, proof_deps, proof_origin and reviewed_proof
are also preserved; only the endpoint wrapper is added to stmt_deps.

Reviewer correction (cc reviews of d31b0807c07b and 8afc056a0460, 2026-10-27):
ordinaryProperForgetComparison is a plain (not irreducible) definition whose body is
the canonical isomorphism itself. With the delivered @[irreducible] wrapper, the
unclaimed transitive user Sheaf.AlgebraicGeometry.SfP1ExchangeIsoTransport
(projection_factor, line 362-363: `unfold projectionComparison; rfl` against the
original body) fails to compile. With the plain wrapper it compiles again, together
with the whole delivered set.

## Old

```lean
@[irreducible]
def projectionComparison (a : Bool) :
    ordinaryFinitePullback A (productMap f i hi) ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f a) ≅
    ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a) ⋙
      ordinaryFinitePullback A i.hom :=
  Functor.isoWhiskerLeft _
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A)
        (projection f a)) ≪≫
    (properExchange A (projectionSquare f i hi a)).symm
```

## New

```lean
@[irreducible]
def projectionComparison (a : Bool) :
    ordinaryFinitePullback A (productMap f i hi) ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f a) ≅
    ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a) ⋙
      ordinaryFinitePullback A i.hom :=
  Functor.isoWhiskerLeft _ (ordinaryProperForgetComparison A (projection f a)) ≪≫
    (properExchange A (projectionSquare f i hi a)).symm
```

## Users

The table includes all basename hits returned by tools/downstream.py with
--uses diagonalLift projectionComparison, all fifteen other current direct importers,
and the new consumers in this packet. The three unrelated basename hits refer to
different declarations. Current main has restored the four previously quarantined
consumers, so all fifteen are checked from their live source paths. Validation-only
source copies are removed from the packet after compilation if unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SfP1IntegralTransportData | unclaimed | Primary implementation repair; signatures and mathematical constructions preserved. |
| Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison | U3 | Uses the fixed ordinary endpoints in the proved categorical pasting calculation. |
| Sheaf.AlgebraicGeometry.SfP1IntegralTransport | unclaimed | Uses both maps through their unchanged signatures; canonical maps preserved. |
| Sheaf.AlgebraicGeometry.SfP1ChartExchange | unclaimed | Direct importer; uses unchanged properExchange, not the modified bodies; compile unchanged. |
| Sheaf.AlgebraicGeometry.SfP1IntegralTraceComparison | unclaimed | Direct importer; unchanged signature and canonical middle comparison; compile unchanged. |
| Sheaf.AlgebraicGeometry.SfP1ChartMapComposition | unclaimed | Direct importer; unchanged statement and proof body; compile unchanged. |
| Sheaf.Paper.CompactificationProjectionInverse | unclaimed | Textual basename hit refers to Adjunction.projectionComparison, a different declaration; unaffected. |
| Sheaf.Paper.SfExceptionalReductionTransitions | unclaimed | Textual basename hit is its own scalar projectionComparison, a different declaration; unaffected. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Textual basename hits are Adjunction.projectionComparison, a different declaration; unaffected. |
| Sheaf.AlgebraicGeometry.SfDiagonalSectionForgetSupports | U3, new | Uses the same canonical proper comparison with recorded ordinary endpoints. |
| Sheaf.AlgebraicGeometry.SfP1DiagonalLiftProperForget | U3, new | Proved defining equality for diagonalLift. |
| Sheaf.AlgebraicGeometry.SfP1ProjectionProperForget | U3, new | Proved defining equality for projectionComparison. |
| Sheaf.AlgebraicGeometry.OrdinaryProperUnitInverseExchange | U3, new | Uses unchanged properExchange to prove inverse constant-object unit transport. |
| Sheaf.AlgebraicGeometry.SfP1OrdinarySectionExchange | U3, new | Uses unchanged properExchange and projectiveLineDiagonalAlpha for ordinary unit pasting. |
| Sheaf.AlgebraicGeometry.SfIsoPushPullUnitNormalization | unclaimed | Current direct importer; compile unchanged. |
| Sheaf.SixFunctors.ProjectiveLineTraceNormalization | unclaimed | Current direct importer; compile unchanged. |
| Sheaf.SixFunctors.ProjectiveLinePresentedIntegrals | unclaimed | Current direct importer; compile unchanged. |
| Sheaf.SixFunctors.ProjectiveLinePresentedKernelIntegrals | unclaimed | Current direct importer; compile unchanged. |
| Sheaf.SixFunctors.ProjectiveLinePresentedKernelAdjunction | unclaimed | Current direct importer; compile unchanged. |
| Sheaf.SixFunctors.ProjectiveLineTraceRawAdjustment | unclaimed | Current direct importer; compile unchanged. |
| Sheaf.AlgebraicGeometry.SfP1CachedRightUnitNormalization | unclaimed | Current direct importer; compile unchanged. |
| Sheaf.AlgebraicGeometry.SfP1ConstantUnitHom | unclaimed | Current direct importer; compile unchanged. |
| Sheaf.AlgebraicGeometry.SfP1ConstantUnitNormalization | unclaimed | Current direct importer; compile unchanged. |
| Sheaf.AlgebraicGeometry.SfP1ConstantUnitPullback | unclaimed | Current direct importer; compile unchanged. |
| Sheaf.AlgebraicGeometry.SfP1CoordinateLineComparison | unclaimed | Current direct importer; compile unchanged. |
| Sheaf.AlgebraicGeometry.SfP1TraceTransportPasting | unclaimed | Current direct importer; compile unchanged. |
| Sheaf.AlgebraicGeometry.SfP1ExchangeIsoTransport | unclaimed | Transitive user; projection_factor unfolds projectionComparison and closes by rfl against the original body, so the wrapper must stay transparent (compiled OK against the corrected set). |

## Status

landed 20261027T135443-L-3709832 2026-10-27 (merge of deliver/U3/Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison)
