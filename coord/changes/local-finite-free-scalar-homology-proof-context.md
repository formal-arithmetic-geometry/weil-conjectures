# AlgebraicGeometry.local_finite_free_scalar_homology proof context

## Reason

The proof needs exactness instances for a composite functor and controlled unfolding
of the scheme restriction equivalence and the internal Hom functors. The static
interface checker flags any new attribute command, including local attributes.
This record documents those proof-elaboration commands. All attributes are local;
the transparency option applies only to the original theorem. No global attribute,
instance, definition, public import, theorem signature or visibility changes.
The new ordinary-complex theorem is separately documented by its DAG node.

## Old

Before the original theorem, the namespace header was:

```lean
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
```

The original theorem signature, verbatim, was:

```lean
theorem local_finite_free_scalar_homology
    {Y : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (U : Y.Opens) (K : Y.Modules)
    (E : CochainComplex U.toScheme.Modules ℤ)
    (hbounded : ∃ N : ℤ, ∀ p : ℤ, N < p → IsZero (E.X p))
    (hfree : ∀ p : ℤ, ∃ r : ℕ, Nonempty (E.X p ≅
      SheafOfModules.free (R := moduleRings U.toScheme.toRingedSpace)
        (ULift.{u} (Fin r))))
    (ε : E ⟶ (CochainComplex.singleFunctor U.toScheme.Modules 0).obj
      ((Scheme.Modules.restrictFunctor U.ι).obj K)) [QuasiIso ε] (q : ℤ) :
    let F : Y.Modules := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) q).obj
        ((derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj K),
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                (SheafOfModules.unit Y.ringCatSheaf)))
    Nonempty (F.over U ≅ (Scheme.Modules.overEquiv U).inverse.obj
      ((homComplex (R := U.toScheme.toRingedSpace.sheaf) E
        ((CochainComplex.singleFunctor U.toScheme.Modules 0).obj
          (SheafOfModules.unit U.toScheme.ringCatSheaf))).homology q))
```

Its proof was `by sorry`.

## New

The proof-elaboration header adds these commands, verbatim:

```lean
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Scheme.Modules.overEquiv Scheme.Modules.restrictFunctor
  homComplexFunctor derivedInternalHom

set_option backward.isDefEq.respectTransparency true in
```

The theorem retains exactly the old signature shown above. Its complete proof
computes through a common injective resolution and composes the existing derived
Hom and homology comparisons, using the new ordinary scheme-restriction comparison.
The extra imports are proof-only. The new public theorem is
`AlgebraicGeometry.homComplex_restrict_scheme` in
`Sheaf.AlgebraicGeometry.HomComplexRestrictScheme`; its exact signature and complete
proof plan are in node `lem-sc-hom-complex-restrict-scheme`.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.LocalFiniteFreeScalarHomology --uses
local_finite_free_scalar_homology` finds one caller outside the item itself.
No original consumer needs adaptation: the theorem and all definitions it uses
retain their signatures and meanings. Local attributes do not affect importers.
The new module has no pre-existing consumers.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineKoszulScalarExtComparison | unclaimed | Calls the identical theorem; no adaptation. |
| Sheaf.AlgebraicGeometry.LocalFiniteFreeScalarHomology | N3 | Complete proof with local elaboration settings; signature unchanged. |
| Sheaf.AlgebraicGeometry.HomComplexRestrictScheme | new, unclaimed | New strict subproblem with one named sorry and its own node. |

## Status

landed 20261013T130750-L-3986356 2026-10-13 (merge of deliver/N3/Sheaf.AlgebraicGeometry.LocalFiniteFreeScalarHomology)
