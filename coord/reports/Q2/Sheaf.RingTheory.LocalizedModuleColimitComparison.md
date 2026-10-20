## What changed

Withdraw the unused `Sheaf.RingTheory.LocalizedModuleColimitComparison` under brief step 8d.
The adopted upstream module already proves exactly the same result as
`Algebra.exists_colimit_addEquiv_localizedModule`. Redirect the Lean attachment of
`lem-pc-localized-module-colimit-comparison` to that existing theorem; retain the node's
statement and fraction-proof plan unchanged. No upstream file is edited.

The signatures compare identically after changing the theorem name. A temporary sandbox
copy of the old statement compiles by applying the upstream theorem to every old argument.
This also checks the independent universes, semilinearity hypotheses, contracted primes,
transition fraction formula, and coprojection conclusion. The upstream proof uses the same
representative and zero-detection argument recorded in the node, including universe lifting.

Change record: `coord/changes/Q2-localized-module-colimit-upstream-duplicate.md`.

## Proved and sorry left

Original item: zero holes. Closed: zero. Added: zero. Split off: zero. Remaining: none.
`Algebra.localizedModuleColimitComparison` was already proved and is retired as an unused
duplicate, not counted as a newly closed hole. Its statement is provided by the existing
proved `Algebra.exists_colimit_addEquiv_localizedModule`.

A temporary exact-statement wrapper compiled through `lcompile.py`; both it and the upstream
theorem were checked with `#print axioms`. Only `propext`, `Classical.choice`, and `Quot.sound`
are reported. No new theorem or definition is introduced.

## No longer needed

Pruned module: `Sheaf.RingTheory.LocalizedModuleColimitComparison`, including its duplicate
private helpers `additive_colimit_rep` and `additive_colimit_zero` and public theorem
`Algebra.localizedModuleColimitComparison`. There are zero downstream modules and no current
uses of the retired name. No consumers need adaptation: both former consumers already use
the upstream replacement.

The withdrawn module's imports are removed with it:

- `Mathlib.Algebra.Category.Ring.Colimits`
- `Mathlib.Algebra.Category.Grp.Colimits`
- `Mathlib.CategoryTheory.Category.Preorder`
- `Mathlib.CategoryTheory.Limits.HasLimits`
- `Mathlib.RingTheory.Localization.AtPrime.Basic`
- `Mathlib.Algebra.Module.LocalizedModule.Basic`
- `Mathlib.Algebra.Category.Ring.FilteredColimits`
- `Mathlib.Algebra.Category.Grp.FilteredColimits`
- `Mathlib.Algebra.Category.Grp.Ulift`

The node and its declared dependencies remain needed by the upstream proof and are retained.
No further node or module is claimed pruned. The unit realization is unchanged.

## Where the brief, the DAG or earlier work was wrong

The brief describes an open proof obligation, but the assigned module has no textual `sorry`
and has no users. The DAG still points to the old Sheaf declaration after both consumers
migrated to `Algebra.exists_colimit_addEquiv_localizedModule`. The retirement inventory's
historical reason for keeping this duplicate (the former consumers used its old name) is
no longer true in the current source tree. The repair is withdrawal and attachment to the
existing complete proof, rather than a no-op or an additional split.

LeanFinder was run for localization commuting with filtered semilinear colimits; its
Mathlib matches cover localization and ordinary fixed-scalar module colimits, not the exact
varying-scalar statement. The adopted source theorem is the exact match.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
