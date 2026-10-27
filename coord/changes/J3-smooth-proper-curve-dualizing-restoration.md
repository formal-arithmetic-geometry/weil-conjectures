# AlgebraicGeometry.smoothProperCurve_dualizing

## Reason

Restore the assigned quarantined module. Its rework row and current build error report
an unknown `Scheme.Modules.exteriorSheaf_one_iso`: the old Sheaf proof import is now an
empty withdrawn module. The adopted source theorem has the same name but concludes with
`exteriorPower`, whereas `smoothProper_dualizing` still concludes with `exteriorSheaf`.
The existing proved comparison supplies the required identification.

## Old

The quarantine archive uses this proof import and final transport:

```lean
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafOneIso

  let j := Functor.mapIso
    (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings C.toRingedSpace)) 0) e
```

Here `e` was obtained from `Scheme.Modules.exteriorSheaf_one_iso`.

## New

```lean
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafOneIso
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafComparison

  let j := Functor.mapIso
    (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings C.toRingedSpace)) 0)
    (eqToIso (Scheme.Modules.exteriorSheaf_eq_exteriorPower g.relativeDifferentials 1) ≪≫ e)
```

The theorem signature, universes, visibility, docstrings and all public imports are
preserved verbatim from quarantine. All mathematical dependencies are retained. The
existing node already records exactly this repaired argument and its three dependencies;
no node edit or new node is necessary. The quarantine archive remains untouched.
There is no shared definition, statement, instance or attribute change and no target
semantic review is reopened. This completes the consumer repair recorded in
`retire-exterior-sheaf-one-iso-20261020.md`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | J3, assigned rework | Restored with repaired proof; zero direct holes before and after. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | quarantined rework | Calls the unchanged theorem twice; no source adaptation required. |

The direct-import scan of the live library finds no importers. The quarantine scan
finds the consumer above. Its proof import remains private, and its two applications
continue to use the identical signature. No consumer file is included in this delivery.
The restored item compiled in 3.6 seconds. A two-file check compiled the item in
15.8 seconds and the unchanged quarantined consumer in 32.8 seconds. The consumer's
temporary sandbox source was then removed. All compiles used `lcompile.py` and passed.

## Status

landed 20261026T111902-L-1764606 2026-10-26 (merge of deliver/J3/Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing)
