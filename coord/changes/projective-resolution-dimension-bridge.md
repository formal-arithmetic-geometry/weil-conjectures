# ModuleCat.projective_resolution_ext_degree

## Reason

Repair upstream review #1428's duplicate Ext criterion. Mathlib already implements
Ext vanishing and dimension shifting. The necessary project-specific theorem is
agreement of the explicit bounded-resolution predicate with Mathlib's dimension
predicate. Keep the existing declaration name and node attachment, but replace its
Ext criterion by this bridge. Its reverse direction still constructs a concrete
resolution; no arbitrary data are chosen from an unproved existence statement.

## Old

```lean
theorem projective_resolution_ext_degree
    {R : Type u} [CommRing R] (X : ModuleCat.{max u v} R) (n : ℕ) :
    (HasProjectiveResolutionLE X n ↔
      ∀ Y : ModuleCat.{max u v} R,
        Subsingleton
          (@Abelian.Ext _ _ _ (HasExt.standard (ModuleCat.{max u v} R)) X Y (Nat.succ n)))
```

## New

```lean
theorem projective_resolution_ext_degree
    {R : Type u} [CommRing R] (X : ModuleCat.{max u v} R) (n : ℕ) :
    HasProjectiveResolutionLE X n ↔ HasProjectiveDimensionLE X n
```

Mathlib.CategoryTheory.Abelian.Projective.Dimension becomes a public import because
HasProjectiveDimensionLE now occurs in the statement. Existing public imports stay.
No definition or Challenge target changes. At n=0 the bridge agrees with Mathlib's
projectivity criterion; at the zero module both predicates hold for every bound.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.ProjectiveResolutionExtDegree | X2 | Replace the duplicate Ext criterion with the resolution/dimension bridge. |
| Sheaf.RingTheory.ProjectiveResolutionExtAllDegrees | unclaimed | Forced proof adaptation: apply the bridge and Mathlib subsingleton/mk rather than the retired single-degree conclusion. Statement unchanged. |
| Sheaf.RingTheory.ProjectiveResolutionExtCharacterization | unclaimed | Forced proof adaptation: Mathlib enough-injectives criterion recovers the original single-degree conjunct. Statement unchanged. |
| Sheaf.AlgebraicGeometry.AffinePolynomialResolutionOfStalkwise | unclaimed | Forced argument adaptation: pass hd directly to the bridge instead of converting it to Ext vanishing. Statement unchanged. |

The all-degrees caller's proof body changes because its old `.mp hle Y` and
`.mpr (fun Y => ...)` no longer typecheck. Its private Dimension import provides
the replacement Mathlib API. The characterization caller's first conjunct no
longer matches the bridge; its private Dimension and EnoughInjectives imports
provide the original criterion without duplicating its proof. The affine caller
changes only the argument of `.mpr`, from Ext vanishing to the already available hd.
The original compiler errors are recorded under Forced adaptations in report.md.
No other use of this declaration occurs in either library root.

## Status

landed 20261013T201812-L-3978380 2026-10-13 (merge of deliver/X2/Sheaf.RingTheory.ProjectiveResolutionExtDegree)
