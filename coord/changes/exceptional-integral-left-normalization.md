# Exceptional integral-left normalization

## Reason

The assigned normalization existence theorem treats `TransportCoreData.integralLeft`
as an arbitrary isomorphism while asserting an equation that determines it uniquely.
The item now flags this defect and supplies the concrete lift, its uniqueness, and
a proved obstruction for nonidentity twists. This is a partial delivery with the
original hole retained; no existing declaration is weakened or removed.

## Old

The existing integral-left field of `TransportCoreData` remains verbatim:

```lean
  integralLeft (E : FieldStage.{u} l) :
    (operation (.integral E)).F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
      PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier
```

There was no `normalizedIntegralLeft` constructor, no corresponding uniqueness theorem,
and no obstruction theorem. The existing normalization theorem's complete signature
and its `sorry` body are preserved.

## New

No existing signature, definition body, attribute, instance, or import changes.
The item adds the concrete fully faithful lift `normalizedIntegralLeft`, its component
and uniqueness theorems, the structure update `TransportCoreData.normalizeIntegralLeft`
and its component theorem, and the three obstruction theorems plus the normalization
package's uniqueness consequence. See the two new DAG nodes and the item source for
the exact signatures. The `STATEMENT-DISPUTED` comment precedes the original theorem.

The construction uses a fully faithful preimage of a specified isomorphism, rather
than an arbitrary choice of transport data from a holed existence theorem.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ExceptionalRingTransportCoreLawsNormalization | E1 | New proved API and dispute annotation; original signatures preserved. |
| Sheaf.Paper.ExceptionalRingTransportCoreLaws | unclaimed when checked | Sole direct importer; no existing name or signature changes; compiles unchanged. |

All added declaration names were searched in the library and had no previous users.
Other transitive importers retain the same existing interface. The delivery tool checks
related modules against the added interface. No target statement or definition changes.

## Status

landed 20261028T020315-L-2493787 2026-10-28 (merge of deliver/E1/Sheaf.Paper.ExceptionalRingTransportCoreLawsNormalization)
