# constantModSheaf_iso_constantSheaf

## Reason

The returned delivery asserted literal equality of the quotient coefficient sheaf
and the constant R-module sheaf. Quotient-by-zero yields a canonical isomorphism;
the parent proof must transport assertions through it.

## Old

```lean
theorem constantModSheaf_eq_constantSheaf {U : Scheme.{u}} (r : ℕ) [Fact r.Prime] :
    Etale.constantModSheaf (ULift.{u + 1} (ZMod r)) U r =
      (constantSheaf U.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))).obj
        (ModuleCat.of _ (ULift.{u + 1} (ZMod r)))
```

## New

```lean
theorem constantModSheaf_iso_constantSheaf {U : Scheme.{u}} (r : ℕ) [Fact r.Prime] :
    Nonempty (Etale.constantModSheaf (ULift.{u + 1} (ZMod r)) U r ≅
      (constantSheaf U.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))).obj
        (ModuleCat.of _ (ULift.{u + 1} (ZMod r))))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | U1 | Replace equality rewrite by isomorphism transport; statement unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | U1 | Correct newly delivered coefficient theorem to an isomorphism. |

The old coefficient declaration exists only in this unlanded delivery. Source search
finds no other users. No target signature or definition used by a target changes.

## Status

landed 20261012T030604-L-1299228 2026-10-12 (merge of deliver/U1/Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions)
