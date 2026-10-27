# ellAdic_localizing_rightAdjoint_obj_homology_constructible

## Reason

The proof reuses established coefficient/hull comparisons and transports the geometric
adjunction. Local irreducibility attributes prevent elaboration from unfolding the large
ambient functors. The static interface classifier requires a record for file commands,
although these attributes are explicitly local and no declaration signature changes.

## Old

No file-level elaboration options or local reducibility commands before the theorem.
The theorem signature and existing variable/open commands remain verbatim.

## New

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [local irreducible] upperStarFromPoint openImmersionLowerShriek lowerStar
  Functor.rightAdjoint
```

These commands affect elaboration in this module. They add no exported instances,
notations, definitions or global attributes. The original public import remains verbatim;
all additional imports are private proof imports. The theorem's statement and meaning
are identical, so no target definition or target statement review is reopened.

## Users

`tools/downstream.py` lists the following 21 consumers. None needs adaptation: the
public declaration and its type are unchanged, and local commands are not exported.
No consumer is modified or claimed by this packet.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | Identical signature and public imports; no adaptation. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | Identical signature and public imports; no adaptation. |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | Identical signature and public imports; no adaptation. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | Identical signature and public imports; no adaptation. |
| `TargetsCheck` | unclaimed | Identical signature and public imports; no adaptation. |
| `WeilConjectures` | unclaimed | Identical signature and public imports; no adaptation. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | Identical signature and public imports; no adaptation. |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed | Identical signature and public imports; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | Identical signature and public imports; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | Identical signature and public imports; no adaptation. |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | Identical signature and public imports; no adaptation. |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | Identical signature and public imports; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Basic` | unclaimed | Identical signature and public imports; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | Identical signature and public imports; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | Identical signature and public imports; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | Identical signature and public imports; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | unclaimed | Identical signature and public imports; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | unclaimed | Identical signature and public imports; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | Identical signature and public imports; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Stalk` | unclaimed | Identical signature and public imports; no adaptation. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | Identical signature and public imports; no adaptation. |

## Status

landed 20261022T143602-L-1185631 2026-10-22 (merge of deliver/F5/Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology)
