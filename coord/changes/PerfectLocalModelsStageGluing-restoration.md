# AlgebraicGeometry.perfect_local_models_stage_gluing

## Reason

Restore the module recorded in coord/rework.tsv at its original Lean attachment.
The archive still publicly imports the withdrawn Sheaf derived-pullback module,
which now contains no declarations. Replace this stale dependency with a direct
public import of the source library that provides the pullback used in the public
signature, instead of relying on unrelated transitive imports. Use the source Hom
Mayer–Vietoris module directly instead of its retired re-export wrapper.
Turn off automatic implicit binders explicitly, as required for Sheaf modules.
The restored proof, its helpers, the theorem signature and all definitions are
unchanged. The archived theorem already has zero holes; this is a restoration
and import repair, not a new proof or a withdrawal.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.Paper.DerivedHomMayerVietoris
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
```

Also add `set_option autoImplicit false`. The former public import is an empty
withdrawn module. Its replacement exposes the existing source declaration,
without changing any mathematical object or theorem type. The second replacement
only changes a private proof import. No target semantic review is reopened.

## Users

`tools/downstream.py` with `--allow-missing --uses
perfect_local_models_stage_gluing` reports zero current library consumers,
since this module and its parent are quarantined. Searching both lean/ and
quarantine/ finds the parent below. Its existing import and application remain
unchanged. The DAG parent, proof dependencies and unit route are preserved.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageGluing | R6 | Restore archive with current imports. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsEventuallyCompatible | quarantined | Same signature and proof interface; no adaptation. |

## Status

landed 20261023T151957-L-428449 2026-10-23 (merge of deliver/R6/Sheaf.AlgebraicGeometry.PerfectLocalModelsStageGluing)
