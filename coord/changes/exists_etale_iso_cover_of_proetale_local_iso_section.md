# AlgebraicGeometry.Scheme.exists_etale_iso_cover_of_proetale_local_iso_section

## Reason

The former generic statements allowed unbounded target complexes. Their proposed
sheafification argument does not supply an etale refinement of a pro-etale cover;
the input is already an actual section of the derived Isom presheaf. The existing
proved comparison API instead gives a Hom bijection with bounded-below target
(Stacks Project, proetale.tex, Tag 09B1, lemma-compare-derived). Add that explicit
hypothesis to these two intermediate statements. The finite-level consumer already
assumes a two-sided cohomology bound on D, so its statement is preserved verbatim.
This is an intermediate statement correction, not a proof of the former unrestricted
statement. No definition or target statement changes.

The proof identifies the pro-etale slice at V with the small site of V.left, derives
the canonical comparison/pullback square, and lifts the hom component by the existing
Hom bijection. Exact underived comparison is fully faithful, so cohomology comparison
shows that derived comparison reflects isomorphisms. Thus the lift is an isomorphism
on V itself, and the singleton identity cover suffices. The construction works for
zero objects and empty schemes as well.

Both adapted modules were unclaimed on the server when checked on 2026-10-28.

## Old

```lean
theorem exists_etale_iso_cover_of_proetale_local_iso_section
    (X : Scheme.{u}) (V : X.Etale)
    {B : Type (u + 1)} [CommRing B]
    (A D : DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (s : (derivedLocalIsoPresheaf (ProEt.topology X) B
      ((derivedComparison X B).obj A)
      ((derivedComparison X B).obj D)).obj
        (op ((toProEt X).obj V))) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage V.left,
      ∀ i : 𝒰.I₀,
        Nonempty ((localIsomorphismRestriction X B
          (Etale.mk (𝒰.f i ≫ V.hom))).obj A ≅
          (localIsomorphismRestriction X B
            (Etale.mk (𝒰.f i ≫ V.hom))).obj D)
```

## New

```lean
theorem exists_etale_iso_cover_of_proetale_local_iso_section
    (X : Scheme.{u}) (V : X.Etale)
    {B : Type (u + 1)} [CommRing B]
    (A D : DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (hD : DerivedCategory.TStructure.t.plus D)
    (s : (derivedLocalIsoPresheaf (ProEt.topology X) B
      ((derivedComparison X B).obj A)
      ((derivedComparison X B).obj D)).obj
        (op ((toProEt X).obj V))) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage V.left,
      ∀ i : 𝒰.I₀,
        Nonempty ((localIsomorphismRestriction X B
          (Etale.mk (𝒰.f i ≫ V.hom))).obj A ≅
          (localIsomorphismRestriction X B
            (Etale.mk (𝒰.f i ≫ V.hom))).obj D)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LisseFiniteLevelEtaleLocalRepresentative | unclaimed | Adds the same lower-bound hypothesis and passes it to the cover theorem. |
| Sheaf.Paper.LisseFiniteLevelEtaleLocalIsomorphisms | unclaimed | Signature unchanged; extracts the lower bound of D from hDbounded and supplies it. |

`tools/downstream.py --uses` finds only the declaration's own module and its
immediate caller. The table also includes the adapted finite-level consumer.
All direct importers are included and compiled together in import order.
The finite-level consumer's direct importer has no statement change to adapt.

The cover module replaces its public imports of
`Sheaf.Paper.LisseTowerEtaleDescentData` and
`Sheaf.Paper.DerivedIsomSheafComparisonFromHom` with the two actual statement
imports, `Sheaf.Paper.DerivedLocalIsomorphismSheaf` and
`Sheaf.AlgebraicGeometry.DerivedMorphismSheafComparison`. Its only direct importer
already publicly imports the descent-data module. New comparison and localization
imports are private proof imports.

## Status

landed 20261028T072410-L-1943052 2026-10-28 (merge of deliver/F5/Sheaf.Paper.EtaleLocalIsoCoverFromProEtaleSection)
