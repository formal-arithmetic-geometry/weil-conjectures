# AlgebraicGeometry.local_finite_free_homology_natural

## Reason

The natural-isomorphism proof needs local exact-composition instances and local
irreducibility annotations for functor reassociations. Without the irreducibility
annotations, unification expands the homology functors into kernel/cokernel proofs
and the single-file compile exceeds its fixed limit. With them it compiles.
The increased heartbeat budget is scoped to this declaration, and the single-file
wall-clock limit stays unchanged. The static interface checker classifies newly
written `attribute` commands as an interface change, hence this record.

Every attribute is explicitly `local`. The theorem signature and visibility, all
public imports, and the exported instance/attribute environment are unchanged.
The two new modules add only their documented public theorem interfaces. No existing
module requires adaptation.

## Old

```lean
theorem local_finite_free_homology_natural
    {Y : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (U : Y.Opens) (B : Y.Modules)
    (E : CochainComplex U.toScheme.Modules ℤ)
    (hbounded : ∃ N : ℤ, ∀ p : ℤ, N < p → IsZero (E.X p))
    (hbelow : ∃ M : ℤ, ∀ p : ℤ, p < M → IsZero (E.X p))
    (hfree : ∀ p : ℤ, ∃ r : ℕ, Nonempty (E.X p ≅
      SheafOfModules.free (R := moduleRings U.toScheme.toRingedSpace)
        (ULift.{u} (Fin r))))
    (ε : E ⟶ (CochainComplex.singleFunctor U.toScheme.Modules 0).obj
      ((Scheme.Modules.restrictFunctor U.ι).obj B)) [QuasiIso ε] (q : ℤ) :
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    Nonempty (S ⋙ (Functor.curry.obj H).obj (op (S.obj B)) ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) q ⋙
        Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙
        CochainComplex.singleFunctor U.toScheme.Modules 0 ⋙
        (homComplexFunctor (R := U.toScheme.toRingedSpace.sheaf)).obj (op E) ⋙
        HomologicalComplex.homologyFunctor U.toScheme.Modules (ComplexShape.up ℤ) q)
```

There were no local elaboration attributes preceding this theorem; its proof was sorry.

## New

```lean
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Scheme.Modules.overEquiv Scheme.Modules.restrictFunctor
  homComplexFunctor derivedInternalHom HomologicalComplex.homologyFunctor
  DerivedCategory.homologyFunctor Functor.mapHomologicalComplex

set_option maxHeartbeats 800000 in
-- The functor-level comparisons require more elaboration steps than objectwise comparisons.
theorem local_finite_free_homology_natural
    {Y : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (U : Y.Opens) (B : Y.Modules)
    (E : CochainComplex U.toScheme.Modules ℤ)
    (hbounded : ∃ N : ℤ, ∀ p : ℤ, N < p → IsZero (E.X p))
    (hbelow : ∃ M : ℤ, ∀ p : ℤ, p < M → IsZero (E.X p))
    (hfree : ∀ p : ℤ, ∃ r : ℕ, Nonempty (E.X p ≅
      SheafOfModules.free (R := moduleRings U.toScheme.toRingedSpace)
        (ULift.{u} (Fin r))))
    (ε : E ⟶ (CochainComplex.singleFunctor U.toScheme.Modules 0).obj
      ((Scheme.Modules.restrictFunctor U.ι).obj B)) [QuasiIso ε] (q : ℤ) :
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    Nonempty (S ⋙ (Functor.curry.obj H).obj (op (S.obj B)) ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) q ⋙
        Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙
        CochainComplex.singleFunctor U.toScheme.Modules 0 ⋙
        (homComplexFunctor (R := U.toScheme.toRingedSpace.sheaf)).obj (op E) ⋙
        HomologicalComplex.homologyFunctor U.toScheme.Modules (ComplexShape.up ℤ) q)
```

The signature is identical. The proof now constructs the natural isomorphism from
functorial derived-Hom comparison and the two new ordinary-complex statements.
The original theorem docstring is unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.LocalFiniteFreeHomologyNatural | T2 | Uses both new theorem interfaces in its proof; existing signature unchanged. |
| Sheaf.AlgebraicGeometry.KoszulExtCoefficientAffineModel | unclaimed | Its invocation of local_finite_free_homology_natural has the identical signature; no adaptation required. |

The declaration-use scan found only the existing user above and the declaration's
own module. All further downstream modules inherit the same public interface.
The new modules have no other pre-existing users.

## Status

landed 20261013T142905-L-500939 2026-10-13 (merge of deliver/T2/Sheaf.AlgebraicGeometry.LocalFiniteFreeHomologyNatural)
