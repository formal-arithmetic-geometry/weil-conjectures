# AlgebraicGeometry.ProEtale.isIso_constantSupportProjection

## Reason

The assignment began with this module and node present, introduced by the V7 delivery
of `Sheaf.Paper.ExceptionalAdjointAdmissibility`, landing
`20261020T211845-L-3511121`. During this session the repository took out dependencies
of batch `20261020T211611`; the assigned module, its node and that parent adaptation
were absent from the current snapshot by delivery time. No matching rework entry or
quarantine path was listed for this item. The first delivery preflight consequently
classified the packet as a new module and node and required this record.

Restore the assigned interface with a complete proof. The declaration names, signatures,
node id, Lean attachment, source, unit and two mathematical proof dependencies are
preserved. The node creation/authorship metadata records this restoration by M3, and
stale review stamps from the removed landing are omitted. No target statement changes.

## Old

The module and node are absent from the current delivery base. At the start of the
assignment the module contained the two signatures below, with one hole in
`isIso_constantSupportProjection`; the exactness instance was already proved.

## New

Restore precisely those signatures, both with complete proofs:

```lean
noncomputable instance preservesFiniteLimits_constantSheaf_proetale
    (Y : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :
    PreservesFiniteLimits
      (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))

theorem isIso_constantSupportProjection
    (R₀ : Type (u + 1)) [CommRing R₀] [IsNoetherianRing R₀]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R₀) c)]
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R₀)))
    (M : DerivedCategory (ModuleCat.{u + 1} R₀)) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R₀) c.g).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} R₀) c.i).mapDerivedCategory.obj K)).app
        ((constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} R₀)).mapDerivedCategory.obj M))
```

The full proofs are in the delivered module. Added supporting declarations are private
and proved. Their data are explicit canonical constructions and definitional interfaces;
none is chosen from an unproved existence statement.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleConstantSupportProjection | M3 | Restore the assigned interface with zero holes. |

A name/import search of the current shared Lean tree finds no consumers of either
restored declaration or module. The original parent adaptation was removed by the batch
take-out. No consumer needs adaptation because the assigned signatures are unchanged.
The original node dependency attachment is retained; this delivery does not withdraw
any node, declaration, or source-library module.

## Status

landed 20261020T230808-L-613545 2026-10-20 (merge of deliver/M3/Sheaf.AlgebraicGeometry.ProEtaleConstantSupportProjection)
