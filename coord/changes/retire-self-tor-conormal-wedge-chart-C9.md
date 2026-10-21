# AlgebraicGeometry.exists_selfTor_conormal_wedge_chart

## Reason

The human-approved retirement inventory lists
`Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChart` as a `PROOFDIFF_UNSAFE`
duplicate of the adopted upstream module
`WeilConjectures.AlgebraicGeometry.SelfTorConormalWedgeChart`. The upstream
theorem is complete, but its public chart is encoded with `exteriorPower` and
`wedge`, while the one direct consumer's public statement uses `exteriorSheaf`
and `exteriorSheafSection`. The duplicate can therefore be withdrawn after the
consumer transports the upstream chart through the canonical comparison.

## Old

The withdrawn Sheaf declaration was:

```lean
theorem exists_selfTor_conormal_wedge_chart
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (n : ℕ) (U : Y.affineOpens) :
    let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
    let E := Scheme.Modules.exteriorSheaf N n
    let M := conormalExteriorModule (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
      Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    ∃ s : E.over (i ⁻¹ᵁ U.1) ≅ (T.obj M).over (i ⁻¹ᵁ U.1),
      ∀ b : Fin n → i.ker.toModules.val.obj (op U.1),
        s.hom.val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1))))
            (Scheme.Modules.exteriorSheafSection N n (i ⁻¹ᵁ U.1)
              (fun j ↦ ((Classical.choose
                (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
                  i.ker.toModules).val.app (op U.1) (b j))) =
          selfTorAffineSection i U M (selfTorIdealWedge i U n b)
```

Its sole direct consumer imported the duplicate:

```lean
import Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChart
```

and selected its chart family directly:

```lean
choose s hs using fun U ↦ exists_selfTor_conormal_wedge_chart i n U
```

## New

`lean/Sheaf/AlgebraicGeometry/SelfTorConormalWedgeChart.lean` is withdrawn
through `deleted.txt`. The existing DAG node
`new-t2-self-tor-conormal-wedge-chart` is attached to the unchanged upstream
declaration in
`lean/WeilConjectures/AlgebraicGeometry/SelfTorConormalWedgeChart.lean`.

The unchanged upstream declaration is:

```lean
theorem exists_selfTor_conormal_wedge_chart
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (n : ℕ) (U : Y.affineOpens) :
    let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
    let E := Scheme.Modules.exteriorPower N n
    let M := conormalExteriorModule (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
      Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    ∃ s : E.over (i ⁻¹ᵁ U.1) ≅ (T.obj M).over (i ⁻¹ᵁ U.1),
      ∀ b : Fin n → i.ker.toModules.val.obj (op U.1),
        s.hom.val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1))))
            (Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ U.1))
              (fun j ↦ ((Classical.choose
                (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
                  i.ker.toModules).val.app (op U.1) (b j))) =
          selfTorAffineSection i U M (selfTorIdealWedge i U n b)
```

The direct consumer imports the upstream theorem and the proved comparison:

```lean
import WeilConjectures.AlgebraicGeometry.SelfTorConormalWedgeChart
import Sheaf.AlgebraicGeometry.ExteriorSheafComparison
```

For each affine chart it composes the over-site map induced by
`exteriorSheafIsoExteriorPower` with the upstream isomorphism. The equation
`exteriorSheafIsoExteriorPower_hom_wedge` rewrites the transported
`exteriorSheafSection` to the upstream `wedge`, after which the upstream
normalization is applied. The consumer's public statement and all definitions
are unchanged.

## Users

`tools/downstream.py` lists five modules downstream of the withdrawn module;
only `SelfTorBasicIdealWedgeCoordinates` directly imports it and uses its
public theorem. The other four remain unchanged and receive the upstream
node through the adapted consumer.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SelfTorBasicIdealWedgeCoordinates | unclaimed | Replace the withdrawn import and transport the upstream chart through the canonical exterior comparison; public theorem unchanged. |
| Sheaf.AlgebraicGeometry.SelfTorCompatibleAffineMaps | unclaimed | Transitive consumer; no source change. |
| Sheaf.AlgebraicGeometry.SelfTorIdealWedgeCoordinates | unclaimed | Transitive consumer; no source change. |
| Sheaf.AlgebraicGeometry.SelfTorLocalWedgeCoordinates | unclaimed | Transitive consumer; no source change. |
| Sheaf.AlgebraicGeometry.SelfTorNestedAffineCoordinates | unclaimed | Transitive consumer; no source change. |

The node's unit and mathematical route are preserved. No upstream declaration,
target statement, or public import is changed. The comparison is canonical and
works in degree zero, on empty charts, and over zero quotient rings.

## Status

landed 20261021T004824-L-1791176 2026-10-21 (merge of deliver/C9/Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChart)
