# AlgebraicGeometry.ProEtale.exists_condensedConstructible_extension_tower

## Reason

Restore the assigned missing module from the archive named in coord/rework.tsv,
following the cluster rollback at 5f7b33eac. The archive already contains a complete
proof and two proved private helpers. The repair reinstates that source at its
library path; it does not replace a theorem, weaken its statement, change a
coefficient construction, or claim a new proof-hole closure.

## Old

The live path lean/Sheaf/Paper/CondensedConstructibleExtensionTower.lean is absent.
The preserved source is quarantine/Sheaf/Paper/CondensedConstructibleExtensionTower.lean.
Its public declaration has the following signature:

```lean
theorem exists_condensedConstructible_extension_tower
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.val) T))
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E.val) T) M) :
    ∃ r : ℕ, (condensedConstructiblePiece T ℓ E).extensionProductIter r
      ((DerivedCategory.singleFunctor _ 0).obj M)
```

## New

The same archived module is restored verbatim at
lean/Sheaf/Paper/CondensedConstructibleExtensionTower.lean, including the signature
above, the complete noetherian-induction proof, the two private pushforward
helpers, and both original imports. There are no definition or interface changes.
The source compiles against the current library through lcompile.py (9.6 seconds,
exit code 0). The one-step dependency was independently restored by D4 before this
repair. The existing DAG attachment and every proof dependency are preserved.

## Users

The required downstream.py query with --allow-missing and
--uses exists_condensedConstructible_extension_tower reports zero current library
importers and zero declaration users, since the parent is itself quarantined.
A separate search of the archive and DAG identifies the retained parent below.
Absence from the current import graph is not used to withdraw either obligation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedSheafExtContinuity | Not queried; not edited | Quarantined direct importer; its line 156 uses the identical theorem. No adaptation. |

The parent's node lem-weil-pbc-condensed-sheaf-ext-continuity still cites this
item. Its import and application in the archived parent match the restored
module and unchanged signature. All further consumers retain the same interface.
No target definition, target type, unit statement, or unit proof step changes.

## Status

landed 20261021T023300-L-2944239 2026-10-21 (merge of deliver/B4/Sheaf.Paper.CondensedConstructibleExtensionTower)
