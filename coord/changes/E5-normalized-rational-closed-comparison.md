# WeilConjectures.sfNormalizedRationalRecollement_closed_comparison

## Reason

Expose the coefficient normalization of the closed unit separately from its Frobenius
mate. This is a new comparison theorem, needed to connect the existing presentation
normalizations to the published actual rational proper adjunction. No existing signature,
definition, instance, attribute, or public import is changed.

## Old

No declaration: this closed-unit comparison was a prose step of
`lem-sf-normalized-rational-recollement-weil-squares`.

## New

```lean
theorem sfNormalizedRationalRecollement_closed_comparison
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X₀ Z₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (i₀ : Z₀ ⟶ X₀) [IsClosedImmersion i₀.left]
    (i : (D.geometricFiber Z₀).left ⟶ (D.geometricFiber X₀).left)
    [IsClosedImmersion i]
    (_hi : i = ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map i₀).left)
    (P : SfRecollementPresentation
      (sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left))
    (Q : SfRecollementPresentation
      (sfRationalConstructibleCategory l E (D.geometricFiber X₀).left))
    (_hP : SfIntegralRecollementNormalization l E i (sfRecollementGeometricNoetherian D X₀) P)
    (_hQ : SfRationalRecollementNormalization l E (D.geometricFiber X₀).left P Q) :
    ∃ c : Q.closedTerm ≅ fieldWeilPull D l hl E i₀ ⋙ fieldWeilProper D l hl E i₀,
      ∀ K, Q.unit.app K ≫ c.hom.app K = (fieldWeilProperAdj D l hl E i₀).unit.app K
```

The new theorem is stated with one named sorry. Its module publicly imports the two
existing modules required by its signature. The item imports it only for its proof.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SfNormalizedRationalWeilSquares | E5 | New private proof import; uses the closed comparison to transport the proper mate square. Existing statement unchanged. |

This is a new declaration; there are no pre-existing consumers to adapt. The item’s
existing public signature and all definitions used by targets remain unchanged.

## Status

landed 20261025T122810-L-1807992 2026-10-25 (merge of deliver/E5/Sheaf.Paper.SfNormalizedRationalWeilSquares)
