# AlgebraicGeometry.Etale.unbounded_abelian_exchange_comparison

## Reason

Restore the assigned quarantined zero-hole module after the upstream sync.
Its private ordinary-exchange proof import introduced duplicate coefficient-comparison
constants from the upstream and retained Sheaf modules. A successful compile now requires
only the retained interface. No public signature, definition body, or public import changes.
No upstream source file is edited. No target statement or definition it uses is changed.

## Old

The archived module had this private proof import:

```lean
import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
```

It used that module's public `moduleAbelianUnderivedExchange_compatibility` theorem.
There were no local `moduleAbelianUpperStarIso_unit` or
`moduleAbelianUnderivedExchange_compatibility` helpers.
The original public theorem and both public comparison definitions are retained verbatim.

## New

Remove that private import. Add proved private helpers
`moduleAbelianUpperStarIso_unit` and `moduleAbelianUnderivedExchange_compatibility`
with exactly the statements and proofs of their upstream counterparts, except that the
latter is private. They elaborate against the existing Sheaf coefficient declarations.
The existing derived proof now resolves the ordinary exchange invocation to the private helper.
All public declarations and public imports are identical to the archived source.

## Users

The source-only downstream scan finds no live importers: this module is quarantined.
The archived sources have the following direct consumers. Their exported types and
comparison definitions remain identical; this import-only repair requires no consumer edits.
No live claim for these archived modules was found in the shared claim snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison` | C4 (assigned item) | Restored with proved private ordinary-exchange helpers. |
| `Sheaf.AlgebraicGeometry.EtaleGenericDirectImageExchange` | quarantined; no live claim found | Identical public interface; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed` | quarantined; no live claim found | Identical public interface; no adaptation. |
| `Sheaf.AlgebraicGeometry.OpenProductExchange` | quarantined; no live claim found | Identical public interface; no adaptation. |
| `Sheaf.AlgebraicGeometry.PunctualTensorBaseChange` | quarantined; no live claim found | Identical public interface; no adaptation. |
| `Sheaf.AlgebraicGeometry.UnboundedCoefficientForgetfulAux` | quarantined; no live claim found | Identical public interface; no adaptation. |
| `Sheaf.Paper.NearbySpecializationSlice` | quarantined; no live claim found | Identical public interface; no adaptation. |
| `Sheaf.Targets.BaseChangeTowardsFields` | quarantined; no live claim found | Identical public interface; no adaptation. |
| `Sheaf.TraceFormula.SmoothSourceConstructibleLocalAcyclicity` | quarantined; no live claim found | Identical public interface; no adaptation. |

## Status

landed 20261020T145455-L-2399170 2026-10-20 (merge of deliver/C4/Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison)
