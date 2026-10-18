# AlgebraicGeometry.ProEtale.CondensedRing.affine_restriction_boundedConstructible

## Reason

Repair the duplicate declaration identified in the H3 return at dd86fa917. The boundedness
module now imports and reuses the declaration in its original cohomology module. The
standalone duplicate module is omitted: it never landed and is absent from current main.

The original cohomology proof and its six supporting modules were removed from main by
batch take-out be47c38950. To avoid relying on stale compiled outputs, this delivery restores
the A4 source proofs from the returned base at their original paths. The cohomology module
is unclaimed. Its existing theorem statement and visibility are unchanged. All six new
supporting modules were also absent and unclaimed. A4 retains authorship of these proofs;
H3 repairs their reuse and records their restoration. No existing definition changes.

## Old

The existing cohomology theorem has this signature:

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

No affine restriction declaration is present in the current main source after take-out.
The returned delivery duplicated it in a standalone helper module.

## New

The existing signature above is identical and its proof is restored. The original public
helper is restored in the same cohomology module, with this signature:

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

The boundedness module imports the cohomology module privately and uses this helper.
There is one declaration of this fact. The supporting affine-line adjunction theorem is
an explicit geometric proof obligation, not a definition or an axiom. All other restored
supporting modules have complete proofs. No target statement or defining data changes.

## Users

`tools/downstream.py` reports 21 transitive consumers of the cohomology module and zero
existing textual uses of the helper on main. The item becomes its additional consumer.
The cohomology module itself is the only adapted existing module.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Restored proof and affine helper; existing signature unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| TargetsCheck | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| WeilConjectures | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Existing statements, definitions and visibility unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | H3 | Proof imports the restored affine helper; existing signatures unchanged. |

## Status

landed 20261018T112416-L-632061 2026-10-18 (merge of deliver/H3/Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded)
