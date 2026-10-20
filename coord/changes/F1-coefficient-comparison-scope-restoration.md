# AlgebraicGeometry.ProEtale.CondensedRing comparison endpoint scope restoration

## Reason

Restore the quarantined change-of-coefficients helper module after the scheduled
upstream extraction left four dangling scoped omission commands. The rework failure
was `Unexpected name CoefficientMap after end: The current section is unnamed`.
The endpoint constructions and public interface remain identical to the archive.

## Old

The `CoefficientMap` section contained these commands after its variable declarations:

```lean
omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in
omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in
omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in
end CoefficientMap
```

## New

The same section now ends with:

```lean
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

end CoefficientMap
```

All four subsequent definitions and their contexts are verbatim preserved.
Only the extraction comment is also wrapped to the line-width limit.
No target definition or statement changes meaning; no target re-review is triggered.

## Users

The live Lean roots have no current importers of this quarantined module. Searching
both the live roots and quarantine finds the following preserved consumer. No consumer
is edited, and no new or changed interface is introduced.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.ProperBaseChangeRational` | quarantined, not adapted | Existing import and local irreducibility attributes still refer to the same endpoint definitions. |

## Status

landed 20261020T145504-L-2401126 2026-10-20 (merge of deliver/F1/Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients)
