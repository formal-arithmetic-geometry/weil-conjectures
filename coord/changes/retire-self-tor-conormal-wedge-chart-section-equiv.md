# AlgebraicGeometry.exists_selfTor_conormal_wedge_chart_section_equiv

## Reason

The human-authorized retirement list coord/retire-items.tsv identifies
Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChartSectionEquiv as a duplicate of its
existing upstream twin. Both files are already proved. The local statement uses
exteriorSheaf and exteriorSheafSection, whereas upstream uses exteriorPower and wedge.
The direct consumer must transport the section equivalence along the canonical identity-on-objects isomorphism of
these exterior constructions before the duplicate can be withdrawn.

## Old

```lean
theorem exists_selfTor_conormal_wedge_chart_section_equiv
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (n : ℕ) (U : Y.affineOpens) :
    let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
    let E := Scheme.Modules.exteriorSheaf N n
    let M := conormalExteriorModule (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
      Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    ∃ e : ((E.over (i ⁻¹ᵁ U.1)).val.obj
          (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1))))) ≃ₗ[Z.presheaf.obj (op (i ⁻¹ᵁ U.1))]
        ((T.obj M).over (i ⁻¹ᵁ U.1)).val.obj
          (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1)))),
      ∀ b : Fin n → i.ker.toModules.val.obj (op U.1),
        e (Scheme.Modules.exteriorSheafSection N n (i ⁻¹ᵁ U.1)
          (fun j ↦ ((Classical.choose
            (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
              i.ker.toModules).val.app (op U.1) (b j))) =
          selfTorAffineSection i U M (selfTorIdealWedge i U n b)
```

## New

Withdraw the duplicate through deleted.txt and attach its existing DAG node to
WeilConjectures.AlgebraicGeometry.SelfTorConormalWedgeChartSectionEquiv. The exact
upstream signature follows. The source file is unchanged.

```lean
theorem exists_selfTor_conormal_wedge_chart_section_equiv
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (n : ℕ) (U : Y.affineOpens) :
    let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
    let E := Scheme.Modules.exteriorPower N n
    let M := conormalExteriorModule (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
      Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    ∃ e : ((E.over (i ⁻¹ᵁ U.1)).val.obj
          (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1))))) ≃ₗ[Z.presheaf.obj (op (i ⁻¹ᵁ U.1))]
        ((T.obj M).over (i ⁻¹ᵁ U.1)).val.obj
          (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1)))),
      ∀ b : Fin n → i.ker.toModules.val.obj (op U.1),
        e (Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ U.1))
          (fun j ↦ ((Classical.choose
            (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
              i.ker.toModules).val.app (op U.1) (b j))) =
          selfTorAffineSection i U M (selfTorIdealWedge i U n b)
```

The sole direct consumer replaces its private import, adds the private import
Sheaf.AlgebraicGeometry.ExteriorSheafComparison, and evaluates the existing canonical
comparison Scheme.Modules.exteriorSheafIsoExteriorPower N n on the chart to get a linear
equivalence e0; Scheme.Modules.exteriorSheafIsoExteriorPower_hom_wedge proves
e0(exteriorSheafSection a) = wedge a (reviewer fix: the delivery had re-built this
comparison as a private isomorphism). Compose e0 with the upstream
section equivalence and use the existing reconstruction theorem. Every public
signature, definition, and public import of the consumer stays verbatim.

## Users

tools/downstream.py with --uses exists_selfTor_conormal_wedge_chart_section_equiv
lists six downstream modules. Only SelfTorConormalWedgeChart imports the duplicate
and uses its declaration. The local claim snapshot contains no active claim record
for these consumers. The assigned retirement item belongs to R6.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SelfTorBasicIdealWedgeCoordinates | unclaimed | Indirect consumer; unchanged public interface requires no edit. |
| Sheaf.AlgebraicGeometry.SelfTorCompatibleAffineMaps | unclaimed | Indirect consumer; unchanged public interface requires no edit. |
| Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChart | unclaimed | Replace private import and transport upstream section equivalence; existing public signature stays verbatim. |
| Sheaf.AlgebraicGeometry.SelfTorIdealWedgeCoordinates | unclaimed | Indirect consumer; unchanged public interface requires no edit. |
| Sheaf.AlgebraicGeometry.SelfTorLocalWedgeCoordinates | unclaimed | Indirect consumer; unchanged public interface requires no edit. |
| Sheaf.AlgebraicGeometry.SelfTorNestedAffineCoordinates | unclaimed | Indirect consumer; unchanged public interface requires no edit. |

The node's mathematical statement and the unit route are preserved. No target or
definition is changed. The comparison uses no nonemptiness or positive-degree
assumption, so zero rings, empty charts, and degree zero are included.

The adapted consumer compiles without warnings. Its public signature and public
imports compare byte-for-byte equal to the originals, and its overlaid import closure
has no withdrawn import or Sheaf/upstream module pair. An explicit `#print axioms`
of exists_selfTor_conormal_wedge_chart returns only propext, Classical.choice, and
Quot.sound. The delivery dry run passes; its auxiliary automatic axiom probe timed
out, so this explicit successful check also records the axiom validation.

## Status

landed 20261020T221337-L-4176246 2026-10-20 (merge of deliver/R6/Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChartSectionEquiv)
