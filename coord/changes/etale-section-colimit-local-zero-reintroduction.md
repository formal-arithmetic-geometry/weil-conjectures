# AlgebraicGeometry.etale_section_colimit_local_zero_sieve

## Reason

The assigned module and node were present when the worker started, then removed from the
server base during the session. Reintroduce the exact originally assigned signature with
a complete proof and no sorry. No existing declaration or target is changed.

## Old

Absent on the refreshed base. At worker start the signature below existed with proof `by sorry`.

## New

```lean
theorem etale_section_colimit_local_zero_sieve
    (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    (U : X.Etale) [CompactSpace U.left]
    (I : Type w) [SmallCategory I] [IsFiltered I]
    (G : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{max v w} Λ))
    (c : Cocone G) (hc : IsColimit c) (i : I)
    (s : (G.obj i).obj.obj (Opposite.op U))
    (hs : ((c.ι.app i).hom.app (Opposite.op U)).hom s = 0) :
    ∃ S : Sieve U, S ∈ X.smallEtaleTopology U ∧
      ∀ (V : X.Etale) (q : V ⟶ U), S q →
        ∃ (j : I) (f : i ⟶ j),
          ((G.map f).hom.app (Opposite.op V)).hom
            (((G.obj i).obj.map q.op).hom s) = 0
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| none on refreshed base | none | new proved interface; no adaptation needed |

The downstream tool reports an unknown module on the refreshed base, confirming its absence.
A source search found no current import of this module. The originally planned user
EtaleSectionColimitEventualZeroAux no longer imports this module on that base.

## Status

landed 20261012T085333-L-37102 2026-10-12 (merge of deliver/S1/Sheaf.AlgebraicGeometry.EtaleSectionColimitLocalZero)
