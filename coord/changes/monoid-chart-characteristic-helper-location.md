# AlgebraicGeometry.EtaleLogStructure.globalChartUnitFace and characteristic helpers

## Reason

The characteristic-stalk and fan-map subarguments require the three existing helper
constructions. Move them together into the new characteristic-stalk module to avoid
an import cycle. Their names, universes, signatures, attributes and bodies are unchanged.
The item publicly imports that module, so every existing public name remains available.
No mathematical statement or target meaning changes.

## Old

In `Sheaf.AlgebraicGeometry.MonoidChartCharacteristicFan`:

```lean
/-- The face of chart elements whose structural germ is a unit in the ordinary local
ring. The top-open section is transported by the canonical ring isomorphism `topIso`.
Source: ILO VIII 3.1.2, 3.3.2 (blueprint: lem-trf-monoid-chart-characteristic-fan). -/
noncomputable def EtaleLogStructure.globalChartUnitFace {X : Scheme.{u}} (M : EtaleLogStructure X)
    {Q : Type u} [CommMonoid Q]
    (c : Q →* M.monoidSheaf.obj.obj (op (Scheme.Etale.mk (⊤ : X.Opens).ι)))
    (x : X) : Submonoid Q :=
  (IsUnit.submonoid (X.presheaf.stalk x)).comap
    (((X.presheaf.germ ⊤ x (by trivial)).hom.toMonoidHom.comp
      (⊤ : X.Opens).topIso.hom.hom.toMonoidHom).comp
      ((M.alpha.app (op (Scheme.Etale.mk (⊤ : X.Opens).ι))).hom.comp c))

/-- The monoidal space of the characteristic sheaf of a Zariski log structure.
Its sheaf is the existing sheafification of the quotient by units, not a new quotient.
Source: ILO VIII 3.1.1, 3.3.12 (blueprint: lem-trf-monoid-chart-characteristic-fan). -/
noncomputable def ZariskiLogStructure.characteristicMonoidalSpace {X : Scheme.{u}}
    (Z : ZariskiLogStructure X) : SheafedSpace CommMonCat.{u} where
  carrier := X.carrier
  presheaf := (FineFan.sharpSheaf Z.monoidSheaf.obj).obj
  IsSheaf := (FineFan.sharpSheaf Z.monoidSheaf.obj).property

/-- The actual characteristic class of a log section, using the unit quotient and
its sheafification unit. Source: ILO VIII 3.1.1, 3.3.12
(blueprint: lem-trf-monoid-chart-characteristic-fan). -/
noncomputable def ZariskiLogStructure.characteristicSection {X : Scheme.{u}}
    (Z : ZariskiLogStructure X) (V : X.Opens) :
    Z.monoidSheaf.obj.obj (op V) →*
      Z.characteristicMonoidalSpace.presheaf.obj (op V) :=
  (((toSheafify (Opens.grothendieckTopology X.carrier)
    (FineFan.sharpPresheaf Z.monoidSheaf.obj)).app (op V)).hom).comp
      Associates.mkMonoidHom

```

## New

The identical declarations in `Sheaf.AlgebraicGeometry.MonoidChartCharacteristicStalks`:

```lean
/-- The face of chart elements whose structural germ is a unit in the ordinary local
ring. The top-open section is transported by the canonical ring isomorphism `topIso`.
Source: ILO VIII 3.1.2, 3.3.2 (blueprint: lem-trf-monoid-chart-characteristic-fan). -/
noncomputable def EtaleLogStructure.globalChartUnitFace {X : Scheme.{u}} (M : EtaleLogStructure X)
    {Q : Type u} [CommMonoid Q]
    (c : Q →* M.monoidSheaf.obj.obj (op (Scheme.Etale.mk (⊤ : X.Opens).ι)))
    (x : X) : Submonoid Q :=
  (IsUnit.submonoid (X.presheaf.stalk x)).comap
    (((X.presheaf.germ ⊤ x (by trivial)).hom.toMonoidHom.comp
      (⊤ : X.Opens).topIso.hom.hom.toMonoidHom).comp
      ((M.alpha.app (op (Scheme.Etale.mk (⊤ : X.Opens).ι))).hom.comp c))

/-- The monoidal space of the characteristic sheaf of a Zariski log structure.
Its sheaf is the existing sheafification of the quotient by units, not a new quotient.
Source: ILO VIII 3.1.1, 3.3.12 (blueprint: lem-trf-monoid-chart-characteristic-fan). -/
noncomputable def ZariskiLogStructure.characteristicMonoidalSpace {X : Scheme.{u}}
    (Z : ZariskiLogStructure X) : SheafedSpace CommMonCat.{u} where
  carrier := X.carrier
  presheaf := (FineFan.sharpSheaf Z.monoidSheaf.obj).obj
  IsSheaf := (FineFan.sharpSheaf Z.monoidSheaf.obj).property

/-- The actual characteristic class of a log section, using the unit quotient and
its sheafification unit. Source: ILO VIII 3.1.1, 3.3.12
(blueprint: lem-trf-monoid-chart-characteristic-fan). -/
noncomputable def ZariskiLogStructure.characteristicSection {X : Scheme.{u}}
    (Z : ZariskiLogStructure X) (V : X.Opens) :
    Z.monoidSheaf.obj.obj (op V) →*
      Z.characteristicMonoidalSpace.presheaf.obj (op V) :=
  (((toSheafify (Opens.grothendieckTopology X.carrier)
    (FineFan.sharpPresheaf Z.monoidSheaf.obj)).app (op V)).hom).comp
      Associates.mkMonoidHom

```

The original module adds:

```lean
public import Sheaf.AlgebraicGeometry.MonoidChartCharacteristicStalks
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.MonoidChartCharacteristicFan | C9 | Same helper definitions, now publicly imported; theorem signature unchanged. |
| Sheaf.AlgebraicGeometry.MonoidChartCharacteristicFanMap | new in C9 delivery | Uses the original names and constructions. |

A source search found no other direct Lean importers of the item, and no uses of
these names outside its source file. The unfinished DAG parents remain supported:
no declaration is removed, renamed, or weakened. All three delivered modules are
compiled together against the same sandbox. No external existing module is adapted.

## Status

landed 20261026T091329-L-3333494 2026-10-26 (merge of deliver/C9/Sheaf.AlgebraicGeometry.MonoidChartCharacteristicFan)
