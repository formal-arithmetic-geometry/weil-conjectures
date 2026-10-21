# FiniteConstantModel resolution restoration

## Reason

The assigned row of coord/rework.tsv records that
Sheaf.Paper.FiniteConstantModelResolution was quarantined after a cluster restore
and reverted batch (2026-10-20). Its original Lean path is absent. Restore the
complete archived module, rather than withdraw its still-needed declarations.
The archived module already contains complete proofs and compiles against the
current published library without adaptation.

## Old

lean/Sheaf/Paper/FiniteConstantModelResolution.lean is absent.
The original source is preserved at
quarantine/Sheaf/Paper/FiniteConstantModelResolution.lean, with zero sorry bodies.
Both existing DAG attachments still refer to the original Lean module.

## New

Restore lean/Sheaf/Paper/FiniteConstantModelResolution.lean byte for byte from
its quarantine source. All original declaration signatures, definition bodies,
proofs, instance attributes, visibility, and public and private imports are
preserved. In particular scalarModules, scalarToContinuous, modelFunctor,
HasResolution, integralModel, rationalModel, and
finite_constant_model_two_term_free_resolution retain their original meanings.
No definition or theorem statement is repaired or weakened.

## Users

Direct importers were found by searching both lean/ and quarantine/.
Their unmodified archived sources were compiled in a separate scratch overlay
against the restored module, in import order. Both compile cleanly.
No consumer source is included in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteConstantModelResolution | W3 | Restore missing complete module; compiled in 9.3 s and 10.5 s. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | quarantined; not adapted | Original compiles in 5.4 s against restoration. |
| Sheaf.Paper.InternalHomDualConstructibleModels | quarantined; not adapted | Original compiles in 9.0 s against restoration. |

The two attached nodes remain unchanged:
def-sfb-finite-constant-model-data and
lem-sfb-finite-constant-model-two-term-free-resolution. Their statements, Lean
attachments, proof routes, and dependencies are preserved. The unit routes and
all target statement meanings are unchanged.

## Status

landed 20261021T021927-L-2794430 2026-10-21 (merge of deliver/W3/Sheaf.Paper.FiniteConstantModelResolution)
