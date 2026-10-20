# AlgebraicGeometry.Scheme.Modules.exteriorSheaf_one_iso

## Reason

Retire the duplicate Sheaf theorem under the human's 2026-10-20 retirement instruction.
The official theorem concludes with `exteriorPower`, while the legacy consumer concludes
with `exteriorSheaf`. The proved comparison `exteriorSheaf_eq_exteriorPower` identifies
these constructions. The quarantined consumer is left in its quarantine archive; its exact
adaptation is recorded below and is not included in this delivery.

## Old

```lean
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafOneIso
import Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing
```

The consumer used the Sheaf theorem directly and its proof used the separately quarantined
relative-duality theorem.

## New

```lean
import Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafOneIso
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafComparison

by
  have h := smoothProper_dualizing (X := C) (S := Spec (.of k)) g 1 R comparison a adj O hO
  obtain ⟨e⟩ := Scheme.Modules.exteriorSheaf_one_iso g.relativeDifferentials
  obtain ⟨i⟩ := h
  let j := Functor.mapIso
    (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings C.toRingedSpace)) 0)
    (eqToIso (Scheme.Modules.exteriorSheaf_eq_exteriorPower g.relativeDifferentials 1) ≪≫ e)
  exact ⟨i ≪≫ (shiftFunctor _ (1 : ℤ)).mapIso j⟩
```

This exact adaptation is recorded for the quarantined consumer but is omitted from this
delivery so that its proved quarantine body is preserved. The Sheaf copy is withdrawn in
`deleted.txt`; target statements and public source signatures are unchanged. The same delivery
fills the existing proof of `Compactification.exists_overRefinement` in
`WeilConjectures.Compactification.Refinement` using `CommonRefinement.inf`; this is a theorem-
proof change permitted by the source-library boundary.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed; quarantined rework | Quarantine copy is preserved unchanged; the exact adaptation above is recorded but omitted from this delivery. |
| WeilConjectures.Compactification.Refinement | unclaimed source module | Existing `exists_overRefinement` proof filled from the common-refinement construction; signature unchanged. |

## Status

landed 20261020T211642-L-3483773 2026-10-20 (merge of deliver/C3/Sheaf.AlgebraicGeometry.Modules.ExteriorSheafOneIso)
