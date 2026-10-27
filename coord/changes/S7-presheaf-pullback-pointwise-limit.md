# AlgebraicGeometry.AlgebraicSpace.explicitPullbackLimit (private)

## Reason

Use Mathlib's pointwise limit theorem for the directly constructed
sheafPullbackCone. The existing module compiles and contains zero holes;
this is a proof simplification accompanying the assigned historical rework,
not a claim that the earlier proof failed or that its theorem was unproved.

## Old

```lean
private def explicitPullbackLimit {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (g : G ⟶ H) : IsLimit (sheafPullbackCone f g)
```

Its body manually constructs a natural transformation with compatible-pair
components, and verifies naturality, the projection equations and uniqueness.

## New

The exact same private signature, with body:

```lean
by
  apply evaluationJointlyReflectsLimits
  intro T
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_
    (Types.pullbackLimitCone (f.app T) (g.app T)).isLimit
  · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · refine Cone.ext (Iso.refl _) ?_
    rintro (_ | _ | _)
    all_goals rfl
```

No public declaration, import, signature, definition or target meaning changes.
The module compiles cleanly in 4.2 seconds with zero holes.

## Users

The helper is private; its only consumer is the private explicitPullbackSquare
in the same file. A full live/quarantined Lean search for the public module and
presheafPullback_etale_point_lifting found only the item and its archive, besides
reports. The existing DAG attachment and dependencies are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PresheafPullbackEtalePointLifting | S7 | Same limit witness type, complete shorter proof; no consumer adaptation. |

## Status

landed 20261023T152001-L-428684 2026-10-23 (merge of deliver/S7/Sheaf.AlgebraicGeometry.PresheafPullbackEtalePointLifting)
