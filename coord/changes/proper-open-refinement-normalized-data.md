# AlgebraicGeometry.Etale.unboundedProperOpenRefinementComparison

## Reason

The original comparison repeatedly projects through the full existential statement of
`unboundedProperOpenInterchange`. An isolated compile took 37.5 seconds, with about
35 seconds spent type checking. The full proof exceeded the per-file limit.

Store the specialized sheaf and derived comparisons and their two normalizations in
`ProperOpenRefinementData`. Its existence theorem specializes the existing interchange;
`properOpenRefinementData` selects this normalized record. The public comparison now reads
the derived field. The normalization fixes both maps: the sheaf normalization cancels the
monic extension-to-direct-image comparison; the derived normalization determines the map
on every K-injective representative after cancellation of invertible resolution maps.
Thus this selects the same normalized mathematical comparison, with no arbitrary
unnormalized isomorphism. The definition's signature and the main theorem's signature
are unchanged. No locked Challenge statement mentions this definition.

The record and the extraction theorem implement the existing node's comparison
normalization, rather than introducing an additional mathematical hypothesis or proof hole.
The sheaf definitions and component proofs together compiled in 7.7 seconds after this repair.

## Old

```lean
def unboundedProperOpenRefinementComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V₁ V₂ : Scheme.{u}} [IsNoetherian U] [IsNoetherian V₁] [IsNoetherian V₂]
    (p : V₁ ⟶ V₂) [IsProper p] (j₁ : U ⟶ V₁) (j₂ : U ⟶ V₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂) :
    D((j₂)_!open[ModuleCat.{u + 1} A]) ≅
      D((j₁)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      ((((𝟙 U)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) U) ≪≫
        Functor.mapDerivedCategoryIdIso _).symm) _ ≪≫
    (unboundedProperOpenInterchange A).choose_spec.choose j₁ (𝟙 U) p j₂
      ⟨h.trans (Category.id_comp j₂).symm⟩
```

## New

```lean
def unboundedProperOpenRefinementComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V₁ V₂ : Scheme.{u}} [IsNoetherian U] [IsNoetherian V₁] [IsNoetherian V₂]
    (p : V₁ ⟶ V₂) [IsProper p] (j₁ : U ⟶ V₁) (j₂ : U ⟶ V₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂) :
    D((j₂)_!open[ModuleCat.{u + 1} A]) ≅
      D((j₁)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      ((((𝟙 U)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) U) ≪≫
        Functor.mapDerivedCategoryIdIso _).symm) _ ≪≫
    (properOpenRefinementData A p j₁ j₂ h).derivedIso
```

The supporting public declarations in the same module are `ProperOpenRefinementData`,
`nonempty_properOpenRefinementData`, and `properOpenRefinementData`; the existence theorem
has a complete proof and the definition uses its named normalization statement.

## Users

`tools/downstream.py --uses AlgebraicGeometry.Etale.unboundedProperOpenRefinementComparison`
finds only the item's own theorem as a declaration user. There is one direct importer.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProperOpenRefinementAdjointProjection | G6 | Same comparison signature and normalized meaning; complete proof supplied. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphCoherence | E8 | Direct proof importer; no declaration mentions the changed definition, so no adaptation is required. |

The byte-identical direct consumer was compiled successfully against the changed item
in a two-module overlay compile (exit code 0, no compiler warnings). It is not delivered.
The original main theorem signature was also checked verbatim.

## Status

landed 20261022T202023-L-1249825 2026-10-22 (merge of deliver/G6/Sheaf.Paper.ProperOpenRefinementAdjointProjection)
