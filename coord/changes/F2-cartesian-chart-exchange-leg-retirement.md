# cartesianChartPullbackLeg and cartesianChartCone_leg_eq_pullback

## Reason

Retire the duplicate Sheaf.AlgebraicGeometry.CartesianChartExchangeLeg, as explicitly
assigned by coord/retire-items.tsv and the human retirement instruction in
coord/changes/retire-sheaf-twins-20261020.md. The upstream twin contains the same two
private declarations, with identical signatures, construction and proof after stripping
comments and whitespace. Its additional linter setting permits the intentional private
helper sharing. No upstream file is changed.

The manifest's historical consumer Sheaf.AlgebraicGeometry.CartesianChartExchangeNaturality
is already absent. Its replacement WeilConjectures.AlgebraicGeometry.CartesianChartExchangeNaturality
imports all of the upstream leg module and uses the upstream equality in its two projection
calculations. No current Lean module imports the assigned Sheaf copy, and no DAG node names
it or attaches a declaration to it. Thus no parent argument or unit route is withdrawn:
the same chart-exchange proof remains in the adopted source library.

## Old

```lean
module

public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true

private noncomputable def cartesianChartPullbackLeg
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (i : I) (j : Over i) :
    pullback (c.π.app i).left (pullback.snd f (D.obj i).hom) ⟶
      pullback (D.map j.hom).left (pullback.snd f (D.obj i).hom) :=
  pullback.lift
    (pullback.fst (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
      (c.π.app j.left).left)
    (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))
    (by
      rw [Category.assoc]
      rw [← pullback.condition]
      congr 1
      exact congrArg (fun t ↦ t.left) (c.w j.hom))

set_option maxHeartbeats 1000000 in
private lemma cartesianChartCone_leg_eq_pullback
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (i : I) (j : Over i) :
    ((cartesianChartCone f D c i).π.app j).left =
      cartesianChartPullbackLeg f D c i j := by
  change pullback.lift _ _ _ = cartesianChartPullbackLeg f D c i j
  change cartesianChartPullbackLeg f D c i j = cartesianChartPullbackLeg f D c i j
  rfl

end AlgebraicGeometry.Etale
```

## New

The assigned file is withdrawn through deleted.txt; the delivery tool produces:

```lean
module

/-! Withdrawn: no declarations remain. -/
```

The implementation remains verbatim in
WeilConjectures.AlgebraicGeometry.CartesianChartExchangeLeg. No mathematical definition,
statement, target type or target meaning changes. There is no DAG attachment to repoint.

## Users

The full-library import scan and tools/downstream.py with
--uses cartesianChartCone_leg_eq_pullback return no current users.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeLeg | F2 | Withdrawn duplicate; upstream implementation retained. |

The historical Sheaf consumer is already retired, so no consumer adaptation is part of
this delivery. The upstream consumer already imports the upstream twin; it is checked
without editing or delivering it. No target or upstream file is edited.

Validation: lcompile.py successfully compiled the withdrawal stub, the unchanged
upstream leg module and the unchanged upstream naturality consumer, individually
within 60 seconds, without warnings.

## Status

landed 20261020T160106-L-3325517 2026-10-20 (merge of deliver/F2/Sheaf.AlgebraicGeometry.CartesianChartExchangeLeg)
