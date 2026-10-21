# integralConstructible_exchange_target_adjunct

## Reason

The assigned row of coord/rework.tsv preserves this module in quarantine after a
cluster restoration was reverted by the merge queue. Its live source is missing,
but its DAG attachment, dependencies and exchange-equality parent remain. Restore
the actual archived proof at the original path; an empty module would lose the
obligation. The archive already has zero sorry proofs.

## Old

The live file lean/Sheaf/Paper/ContinuousIntegralExchangeTargetAdjunct.lean is absent.
Its authoritative source is
quarantine/Sheaf/Paper/ContinuousIntegralExchangeTargetAdjunct.lean, including the
public theorem AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_exchange_target_adjunct
and its private mate, counit, naturality and pullback-square helpers.

## New

Restore the archived module at its original live path, preserving every declaration
signature, visibility, definition body, public import, hypothesis, universe and
docstring. Wrap long lines at 100 characters. In private bounded_counit_hom replace
the broad simp by simp only with the same compatibility rewrites and explicit
OverClass.asOver_left, Functor.comp_obj, ObjectProperty.ι_obj, Functor.id_obj,
OverClass.asOverHom_left and Iso.symm_inv rewrites, eliminating the flexible-tactic
linter warning. Every proof is complete. No definition, mathematical statement,
target meaning, DAG attachment, dependency or unit route changes.

## Users

tools/downstream.py with --allow-missing --uses integralConstructible_exchange_target_adjunct
finds zero live consumers. An import/name scan of both live library roots and both
quarantine roots finds the two archived consumers below. A scan of DAG statement
and proof dependencies and proof-step uses finds the exchange-equality parent.
Neither consumer has a claim file in the current shared snapshot. No adaptation
is needed because the complete archived interface, including private helpers used
through import all, is restored unchanged. The exchange-equality consumer is also
compiled against the restored module in the sandbox as a temporary probe.
The Qbar consumer was tested too; it fails on its unavailable
finiteCoefficientDerivedToAlgCl declaration and a kernel Mod.monoidalClosed
instance mismatch, independently of the unchanged target-adjunct helper API.
These temporary probes are not delivered; see report.md for the compiler details.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed in shared snapshot | Archived direct consumer and DAG parent; original theorem application preserved. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed in shared snapshot | Archived import-all consumer of private diagram helpers; signatures and bodies preserved. |

## Status

landed 20261021T061108-L-1700660 2026-10-21 (merge of deliver/F4/Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct)
