# AlgebraicGeometry.Scheme.strictHenselization_baseRingMap_naturality

## Reason

Expose the proved naturality calculation for the pointed affine representative diagram
as a separate theorem. The existing `pointed_etale_ring_colimit` signature, definitions,
and public imports are unchanged. No existing module other than the item is edited.

## Old

No standalone `strictHenselization_baseRingMap_naturality` declaration existed.
The existing item theorem had its original signature and an unproved body.

## New

The new theorem is fully proved from the over-category equation and
`Scheme.Hom.comp_appTop`:

```lean
theorem strictHenselization_baseRingMap_naturality
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    {j k : (SmallModel.{u} (strictHenselizationNeighbourhoods barY))ᵒᵖ}
    (f : j ⟶ k) :
    (ΓSpecIso R).inv ≫ Scheme.Γ.map
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse.obj
          k.unop).1.hom.op =
      ((ΓSpecIso R).inv ≫ Scheme.Γ.map
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse.obj
          j.unop).1.hom.op) ≫
        (smallStrictHenselizationDiagram barY).map f
```

The item imports this helper with a proof-only `import` and proves its original statement.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootLimitCone | J2 | Uses the new theorem in the natural transformation's naturality proof; existing signature unchanged. |

The new declaration has no pre-existing users. No target statement or definition changes,
and no module held by another group is adapted.

## Status

landed 20261017T003422-L-3315188 2026-10-17 (merge of deliver/J2/Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootLimitCone)
