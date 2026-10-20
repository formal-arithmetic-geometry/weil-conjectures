# AlgebraicGeometry.selfTor_conormal_dual_chart_iso

## Reason

The current archived source receives an `exteriorPower` source from the
upstream affine-map theorem, whereas its own statement uses `exteriorSheaf`.
A proved private equality repairs this mismatch without changing either
definition. Local irreducibility prevents expensive unfolding of concrete
sheafification choices while the proof compares the constructions through
restriction-map uniqueness and the pure-wedge equation.

The returned delivery placed these local settings before the public functor
definition. This repair narrows them to a proof section after that definition.
They are not exported. No public declaration, theorem signature, definition
body, instance, or import changes. The final file compiled cleanly in 20.4
seconds within the existing limit. This record is required because the
delivery check conservatively flags attribute commands.

## Old

The current archived source defines the public functor as follows:

```lean
noncomputable def selfTorAffineComparisonFunctor {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    (U : Y.affineOpens) : ModuleCat.{u} (Γ(Y, U.1) : Type u) ⥤ Z.Modules :=
  tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
    Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
```

It proceeds directly to `selfTor_conormal_dual_chart_iso`, with no local
irreducibility settings or equality between the exterior constructions.

## New

The same public definition is followed by a proof section:

```lean
section

-- Keep concrete sheafification choices behind the API while comparing the constructions.
attribute [local irreducible] Scheme.Modules.exteriorSheafRestriction
  Scheme.Modules.exteriorSheaf Scheme.Modules.exteriorPower
```

The section contains the proved private equality and the existing public
theorem, whose proof rewrites the existential affine-map family before
unpacking it. The section ends immediately after that theorem, restoring the
original transparency settings. All public signatures and data remain as in
the archived source.

## Users

`tools/downstream.py` with `--allow-missing --uses` reports no live downstream
modules. Searching the quarantined sources identifies the direct consumer
below. The unchanged public interface requires no adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SelfTorConormalDualChartIso | C5 | Restored and repaired; proof settings confined to a local section after the data definition. |
| Sheaf.AlgebraicGeometry.SelfTorConormalDualChart | unclaimed | Quarantined direct consumer; no interface or proof adaptation needed. |

Further consumers and target meanings are unchanged. There is no forced
adaptation.

## Status

landed 20261020T145457-L-2399731 2026-10-20 (merge of deliver/C5/Sheaf.AlgebraicGeometry.SelfTorConormalDualChartIso)
