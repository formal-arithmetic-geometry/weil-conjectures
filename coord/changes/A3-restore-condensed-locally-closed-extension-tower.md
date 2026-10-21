# AlgebraicGeometry.ProEtale.exists_condensedLocallyClosed_extension_tower

## Reason

The assigned row of coord/rework.tsv preserves the module at
quarantine/Sheaf/Paper/CondensedLocallyClosedExtensionTower.lean following a reverted
cluster restore. Its live Lean path is absent. Restore that archived complete module,
including its theorem, both proved private helpers and all imports. This reinstates the
actual finite-extension-tower argument used by the archived consumers; it is a source
restoration, not a proof-hole closure or a withdrawal.

## Old

The live module is absent. The authoritative archive has zero holes and this signature:

```lean
theorem exists_condensedLocallyClosed_extension_tower
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))
    (hM : IsConstructibleModuleObject
      (condensedRingObj Λ T) M) :
    ∃ r : ℕ, (condensedLocallyClosedPiece Λ T).extensionProductIter r
      ((DerivedCategory.singleFunctor _ 0).obj M)
```

## New

Restore the archived file verbatim at its recorded live path. The signature above, public
import of CondensedLocallyClosedPiece, private import of CondensedLocallyClosedOneStep,
and all proof bodies are preserved. The proof first pushes pieces and towers through exact
closed pushforward, then applies noetherian induction on closed supports and prepends the
one-step triangle. The zero-iterate case uses the piece predicate itself. No definition or
target meaning changes. Preserve the existing DAG attachment and proof dependencies and
append only a restoration note to proof_origin.

## Users

A direct import and declaration-use scan of lean/Sheaf, lean/WeilConjectures and quarantine/
finds the following two archived consumers. They apply the identical restored signature,
so neither requires source adaptation. The same two nodes are the DAG parents. The item's
node is not a unit statement or realized unit step; the unit route is preserved.
The downstream.py source query cannot index the absent module, so this inventory uses
both the live and quarantined sources and the DAG instead.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralConstructibleSheafHom | not queried; untouched | Archived consumer and DAG parent; restored signature is unchanged. |
| Sheaf.Paper.IntegralTensorShriek | not queried; untouched | Archived consumer and DAG parent; restored signature is unchanged. |

## Status

landed 20261021T023250-L-2941837 2026-10-21 (merge of deliver/A3/Sheaf.Paper.CondensedLocallyClosedExtensionTower)

Validation: the restored item compiled alone in 3.5 seconds. An import-order consumer
check compiled it in 5.1 seconds, IntegralConstructibleSheafHom in 8.0 seconds and
IntegralTensorShriek in 19.7 seconds, all without errors or warnings. Unchanged consumer
source copies remain only under scratchpad/, outside the delivered lean/ tree.
