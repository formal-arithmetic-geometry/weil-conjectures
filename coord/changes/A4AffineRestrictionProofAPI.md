# AlgebraicGeometry.ProEtale.CondensedRing.affine_restriction_boundedConstructible

## Reason

The delivery adds a proved public affine-restriction helper to
`Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` and private
proof helpers. Preflight classifies the surrounding proof commands (`omit` and the scoped
transparency option on a private theorem) as changed module commands and requires this record.
The transparency option is scoped to that private theorem. No existing statement, definition,
instance or notation changes meaning. Every existing theorem signature stays identical.
No target or definition used by a target changes.

## Old

There was no declaration named `affine_restriction_boundedConstructible`. The existing
public theorem, in the unchanged coefficient and geometric variable context, was:

```lean
theorem ellAdic_localizing_rightAdjoint_obj_homology_constructible
    (G : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
    (adj : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣ G)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ∀ n : ℤ, IsConstructibleModuleObject (condensedRingObj Λ Z.left)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj))
```

## New

The existing theorem has exactly the same signature. The added helper, in that same
coefficient/geometric context, is:

```lean
theorem affine_restriction_boundedConstructible
    (G : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
    (adj : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣ G)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory)
    {U : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [IsAffine U.left] (j : U ⟶ Z) [IsOpenImmersion j.left] :
    boundedConstructible (condensedRingObj Λ U.left)
      (D((j.left)^*⟦Λ⟧).obj
        (G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj)
```

The original theorem and all private helpers are proved. The helper states the bounded
constructible affine restriction used inside the new proof; it is also available to the
independent boundedness worker. It adds no hypothesis to the original theorem.

## Users

`tools/downstream.py` lists the following transitive consumers. Its declaration-use scan
finds no existing user of the new helper. No consumer is edited. The unchanged immediate
constructibility parent compiled as a consumer probe; the maintainer's global build verifies
the full set. In particular, H3's separately held boundedness module is not adapted.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | A4 | Adds and uses the proved helper; original signature unchanged. |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| `TargetsCheck` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| `WeilConjectures` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Basic` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Stalk` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Statement` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | Existing signatures and definitions unchanged; no adaptation. |

## Status

landed 20261018T103526-L-17111 2026-10-18 (merge of deliver/A4/Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology)
