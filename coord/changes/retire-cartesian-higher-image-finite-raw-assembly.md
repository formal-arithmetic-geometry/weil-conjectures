# AlgebraicGeometry.Etale.exists_cartesianHigherImage_finite_raw_assembly

## Reason

The queue assigns Sheaf.AlgebraicGeometry.CartesianHigherImageFiniteRawAssembly as
`retire`, with zero holes. Its only direct importer is the unclaimed module
Sheaf.AlgebraicGeometry.CartesianRawClassChartNaturality. That importer has no importers
and its theorem is used only in its own declaration. Both Sheaf modules duplicate existing
fully proved upstream modules. Withdraw both unused copies in this delivery.

No upstream file, declaration, attribute or public import is changed. No target statement
or definition changes. The upstream assembly and naturality theorems omit only the unused
limit witness hc of their Sheaf counterparts. The raw transition helpers are identical.
The upstream parent proofs already use the upstream copies, so the route is preserved.

## Old

The complete public signatures being retired, verbatim:

```lean
theorem exists_cartesianHigherImage_finite_raw_assembly
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (i : I) (J : Type u) [Finite J]
    (V : J → c.pt.left.Etale) [∀ t, IsAffine (V t).left]
    (z : ∀ t, (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((abelianComparisonFree c.pt.left).obj (V t)) ⟶
        ((D+(((c.π.app i).left)^*[AddCommGrpCat.{u + 1}])).obj
          (cartesianDerivedImage f (D.obj i).hom
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))⟦(q : ℤ)⟧)
    (hkill : ∀ t, ∃ (j : I) (a : j ⟶ i),
      z t ≫ (shiftFunctor _ (q : ℤ)).map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
          (c.π.app j).left (D.map a).left (c.π.app i).left
          (congrArg (fun b ↦ b.left) (c.w a)).symm).hom.app _ ≫
          (D+(((c.π.app j).left)^*[AddCommGrpCat.{u + 1}])).map
            (cartesianDerivedImageMap f (D.obj i).hom (D.obj j).hom
              (D.map a).left (Over.w (D.map a)).symm
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) = 0) :
    ∃ (j : I) (a : j ⟶ i), ∀ t,
      z t ≫ (shiftFunctor _ (q : ℤ)).map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
          (c.π.app j).left (D.map a).left (c.π.app i).left
          (congrArg (fun b ↦ b.left) (c.w a)).symm).hom.app _ ≫
          (D+(((c.π.app j).left)^*[AddCommGrpCat.{u + 1}])).map
            (cartesianDerivedImageMap f (D.obj i).hom (D.obj j).hom
              (D.map a).left (Over.w (D.map a)).symm
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) = 0
```

```lean
theorem cartesianRawClass_chart_naturality
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (i j : I) (V : c.pt.left.Etale) [IsAffine V.left]
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((abelianComparisonFree c.pt.left).obj V) ⟶
        ((D+(((c.π.app i).left)^*[AddCommGrpCat.{u + 1}])).obj
          (cartesianDerivedImage f (D.obj i).hom
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))⟦(q : ℤ)⟧)
    (W : (D.obj j).left.Etale) (_ : IsAffine W.left)
    (r : V.left ⟶ W.left)
    (hr : IsPullback r V.hom W.hom (c.π.app j).left)
    (l : Over j) (b : l.left ⟶ i)
    (x : restrictedOverCohomology (pullback.snd f (D.obj j).hom)
      (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D j).obj l) W)
    (hbase :
      z ≫ (shiftFunctor _ (q : ℤ)).map
          ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
            (c.π.app l.left).left (D.map b).left (c.π.app i).left
            (congrArg (fun t ↦ t.left) (c.w b)).symm).hom.app _ ≫
            (D+(((c.π.app l.left).left)^*[AddCommGrpCat.{u + 1}])).map
              (cartesianDerivedImageMap f (D.obj i).hom (D.obj l.left).hom
                (D.map b).left (Over.w (D.map b)).symm
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) =
        cartesianChartCohomologyLift f D c F q j W V r hr l x) :
      ∀ (m : Over j) (a : m ⟶ l),
        z ≫ (shiftFunctor _ (q : ℤ)).map
          ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
            (c.π.app m.left).left (D.map (a.left ≫ b)).left (c.π.app i).left
            (congrArg (fun t ↦ t.left) (c.w (a.left ≫ b))).symm).hom.app _ ≫
            (D+(((c.π.app m.left).left)^*[AddCommGrpCat.{u + 1}])).map
              (cartesianDerivedImageMap f (D.obj i).hom (D.obj m.left).hom
                (D.map (a.left ≫ b)).left (Over.w (D.map (a.left ≫ b))).symm
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) =
          cartesianChartCohomologyLift f D c F q j W V r hr m
            (restrictedOverCohomologyMap (pullback.snd f (D.obj j).hom)
              (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
              (q : ℤ) ((cartesianChartDiagram f D j).map a) W x)
```

The assembly module also contains the six proved private helpers cartesian_map_eq,
cartesian_map_comp, pulled_cartesian_map_comp, pulled_cartesian_map_congr, rawTransition
and rawTransition_comp. All have identical existing upstream counterparts.

## New

No replacement declaration is introduced. Both paths are listed in deleted.txt; the
delivery tool leaves empty modules. The existing replacement declarations are
AlgebraicGeometry.Etale.exists_cartesianHigherImage_finite_raw_assembly in
WeilConjectures.AlgebraicGeometry.CartesianHigherImageFiniteRawAssembly and
AlgebraicGeometry.Etale.cartesianRawClass_chart_naturality in
WeilConjectures.AlgebraicGeometry.CartesianRawClassChartNaturality. Their signatures are
exactly the respective old signatures above with the binder
`(hc : IsLimit ((Over.forget _).mapCone c))` removed. Their proofs are exactly the old
proofs with the unused line `have _ := hc` removed. No upstream edit is delivered.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartesianHigherImageFiniteRawAssembly | V3 | Withdraw redundant copy; 0 holes. |
| Sheaf.AlgebraicGeometry.CartesianRawClassChartNaturality | unclaimed | Withdraw redundant sole importer, which itself has no importers; 0 holes. |
| WeilConjectures.AlgebraicGeometry.CartesianHigherImageFiniteRawAssembly | unchanged | Existing proved assembly and private helpers retained verbatim. |
| WeilConjectures.AlgebraicGeometry.CartesianRawClassChartNaturality | unchanged | Existing proved naturality theorem retained verbatim. |
| WeilConjectures.AlgebraicGeometry.CartesianHigherImageFiniteRawClassVanishing | unchanged | Already imports and applies the upstream assembly. |
| WeilConjectures.AlgebraicGeometry.CartesianRawClassChartRepresentative | unchanged | Already imports and applies the upstream naturality theorem. |

The downstream tool lists exactly the Sheaf chart-naturality module as an importer of
Sheaf assembly and zero importers of Sheaf chart-naturality. Textual uses of either public
theorem in the Sheaf tree consist only of their declarations. No claim file exists for
the retired consumer. Neither module has a DAG lean attachment. No existing node or unit
route needs modification.

## Status

landed 20261020T132051-L-1408849 2026-10-20 (merge of deliver/V3/Sheaf.AlgebraicGeometry.CartesianHigherImageFiniteRawAssembly)
