# AlgebraicGeometry.completedIdeal and AlgebraicGeometry.completedResidueMap

## Reason

Use the maximal ideal of the localization as the definition of its completion ideal.
It equals the image of p by `IsLocalization.AtPrime.map_eq_maximalIdeal`, so this
normalizes the existing construction without changing its mathematical meaning.
The canonical residue map then needs no quotient-equivalence transport. This makes
the existing completion comparison apply without unfolding equality transports.
No target statement or theorem signature changes.

## Old

```lean
abbrev completedIdeal (S : Type v) [CommRing S] (p : Ideal S) [p.IsPrime] :=
  Ideal.map (algebraMap S (completedLocalRing S p)) p
```

```lean
noncomputable def completedResidueMap
    {S : Type v} [CommRing S]
    (p : Ideal S) [p.IsMaximal] [p.IsPrime] :
    completedRing S p →+* (S ⧸ p) :=
  ((IsLocalization.AtPrime.equivQuotMaximalIdeal p (completedLocalRing S p)).symm.toRingHom).comp
    ((Ideal.quotEquivOfEq
      (IsLocalization.AtPrime.map_eq_maximalIdeal p (completedLocalRing S p))).toRingHom.comp
      (AdicCompletion.evalOneₐ (completedIdeal S p)).toRingHom)
```

## New

```lean
abbrev completedIdeal (S : Type v) [CommRing S] (p : Ideal S) [p.IsPrime] :=
  IsLocalRing.maximalIdeal (completedLocalRing S p)
```

```lean
noncomputable def completedResidueMap
    {S : Type v} [CommRing S]
    (p : Ideal S) [p.IsMaximal] [p.IsPrime] :
    completedRing S p →+* (S ⧸ p) :=
  ((IsLocalization.AtPrime.equivQuotMaximalIdeal p (completedLocalRing S p)).symm.toRingHom).comp
    (AdicCompletion.evalOneₐ (completedIdeal S p)).toRingHom
```

## Users

`tools/downstream.py --uses` finds only the item module mentioning either changed
name (rechecked 2026-10-24). There are three direct importers and 88 transitive importers;
the direct importers use the named API and require no source adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.CompletedJacobianDifferentials | X5 | normalize the ideal and residue map; prove the existing theorem |

## Status

landed 20261024T191714-L-470873 2026-10-24 (merge of deliver/X5/Sheaf.TraceFormula.CompletedJacobianDifferentials)
