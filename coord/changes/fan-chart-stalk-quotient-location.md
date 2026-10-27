# AlgebraicGeometry.LogFanChart.stalkQuotient

## Reason

Move the three existing canonical stalk-quotient constructions to the new
Sheaf.AlgebraicGeometry.FanChartStalkModel module so that the three strict intermediate
statements can use the canonical maps without an import cycle. The item publicly imports
the new module. Names, signatures, visibility, attributes and definition bodies stay identical;
this is relocation, with no mathematical definition change. No existing module besides the
assigned item is changed. The item has no current direct Lean importers.

## Old

In lean/Sheaf/AlgebraicGeometry/FanChartLocalMonoidLift.lean:

```lean
noncomputable def EtaleLogStructure.zariskiSharpening {X : Scheme.{u}}
    (M : EtaleLogStructure X) : M.zariskiPresheaf ⟶ M.sharpSpace.presheaf :=
  { app := fun _ ↦ CommMonCat.ofHom Associates.mkMonoidHom
    naturality := by
      intro U V f
      ext m
      rfl } ≫
    toSheafify (Opens.grothendieckTopology X.carrier) (FineFan.sharpPresheaf M.zariskiPresheaf)

/-- The canonical quotient of the ordinary log stalk, with its characteristic identified
with the fan stalk by the given chart. Source: ILO VI 3.7(a), VIII 3.3.12
(blueprint: lem-trf-fan-chart-local-monoid-lift). -/
noncomputable def LogFanChart.stalkQuotient {X : FineSaturatedLogScheme.{u}}
    {F : FineFan.Fan.{u}} (c : LogFanChart X F) (x : X.scheme) :
    FineFan.stalk X.logStructure.zariskiPresheaf x →*
      FineFan.stalk F.space.presheaf (c.map.hom.base x) :=
  (MulEquiv.ofBijective (FineFan.stalkMap c.map x).hom
    (c.stalkBijective x)).symm.toMonoidHom.comp
      (colim.map (whiskerLeft (OpenNhds.inclusion x).op
        X.logStructure.zariskiSharpening)).hom

/-- Groupification of the canonical quotient, constructed by the group-completion
universal property. Source: ILO VI 3.7(a), exact sequence (3.a)
(blueprint: lem-trf-fan-chart-local-monoid-lift). -/
noncomputable def LogFanChart.stalkGroupQuotient {X : FineSaturatedLogScheme.{u}}
    {F : FineFan.Fan.{u}} (c : LogFanChart X F) (x : X.scheme) :
    Algebra.GrothendieckGroup (FineFan.stalk X.logStructure.zariskiPresheaf x) →*
      Algebra.GrothendieckGroup (FineFan.stalk F.space.presheaf (c.map.hom.base x)) :=
  Algebra.GrothendieckGroup.lift (Algebra.GrothendieckGroup.of.comp (c.stalkQuotient x))
```

## New

In lean/Sheaf/AlgebraicGeometry/FanChartStalkModel.lean, reexported by the item's new
`public import Sheaf.AlgebraicGeometry.FanChartStalkModel`:

```lean
noncomputable def EtaleLogStructure.zariskiSharpening {X : Scheme.{u}}
    (M : EtaleLogStructure X) : M.zariskiPresheaf ⟶ M.sharpSpace.presheaf :=
  { app := fun _ ↦ CommMonCat.ofHom Associates.mkMonoidHom
    naturality := by
      intro U V f
      ext m
      rfl } ≫
    toSheafify (Opens.grothendieckTopology X.carrier) (FineFan.sharpPresheaf M.zariskiPresheaf)

/-- The canonical quotient of the ordinary log stalk, with its characteristic identified
with the fan stalk by the given chart. Source: ILO VI 3.7(a), VIII 3.3.12
(blueprint: lem-trf-fan-chart-local-monoid-lift). -/
noncomputable def LogFanChart.stalkQuotient {X : FineSaturatedLogScheme.{u}}
    {F : FineFan.Fan.{u}} (c : LogFanChart X F) (x : X.scheme) :
    FineFan.stalk X.logStructure.zariskiPresheaf x →*
      FineFan.stalk F.space.presheaf (c.map.hom.base x) :=
  (MulEquiv.ofBijective (FineFan.stalkMap c.map x).hom
    (c.stalkBijective x)).symm.toMonoidHom.comp
      (colim.map (whiskerLeft (OpenNhds.inclusion x).op
        X.logStructure.zariskiSharpening)).hom

/-- Groupification of the canonical quotient, constructed by the group-completion
universal property. Source: ILO VI 3.7(a), exact sequence (3.a)
(blueprint: lem-trf-fan-chart-local-monoid-lift). -/
noncomputable def LogFanChart.stalkGroupQuotient {X : FineSaturatedLogScheme.{u}}
    {F : FineFan.Fan.{u}} (c : LogFanChart X F) (x : X.scheme) :
    Algebra.GrothendieckGroup (FineFan.stalk X.logStructure.zariskiPresheaf x) →*
      Algebra.GrothendieckGroup (FineFan.stalk F.space.presheaf (c.map.hom.base x)) :=
  Algebra.GrothendieckGroup.lift (Algebra.GrothendieckGroup.of.comp (c.stalkQuotient x))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FanChartLocalMonoidLift | F8 | Same three definitions through the public import; theorem proof replaced. |
| Sheaf.AlgebraicGeometry.FanChartStalkModel | F8 (new) | Defines the same canonical maps and states the normalized stalk comparison. |
| Sheaf.AlgebraicGeometry.FanChartGermSpreading | F8 (new) | Uses the canonical stalk quotient in the monoid-section hypothesis. |
| Sheaf.AlgebraicGeometry.FanChartSectionIsChart | F8 (new) | Imports the shared stalk model and states the characteristic criterion. |

`tools/downstream.py` reports zero downstream modules of the item; declaration searches
find no external consumers of the three names. No consumer adaptation is necessary.
The new modules contain no replacement definition of any old notion. No target's meaning changes.

## Status

landed 20261026T081837-L-2086505 2026-10-26 (merge of deliver/F8/Sheaf.AlgebraicGeometry.FanChartLocalMonoidLift)
