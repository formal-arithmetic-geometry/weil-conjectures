# CategoryTheory.siteCohomology_zero_section and its properties

## Reason

Retire the duplicate listed in `coord/retire-items.tsv`. The adopted source library
already defines `Sheaf.objectCohomologyEval₀` by the same universal-generator formula
and proves `siteCohomology_zero_section_properties`. The sole direct consumer can use
them without changing its statement. No source-library file is changed.

## Old

```lean
noncomputable def siteCohomology_zero_section
    {C : Type u} [SmallCategory C] (T : GrothendieckTopology C)
    [HasSheafify T AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf T AddCommGrpCat.{u})]
    (A : Sheaf T AddCommGrpCat.{u}) (X : C) (x : Sheaf.H' A 0 X) :
    A.obj.obj (op X) :=
  ((Abelian.Ext.addEquiv₀ x).hom.app (op X)).hom
    (((toSheafify T (yoneda.obj X ⋙ AddCommGrpCat.free)).app (op X)).hom
      (FreeAbelianGroup.of (𝟙 X)))

theorem siteCohomology_zero_section_properties_sheaf
    {C : Type u} [SmallCategory C] (T : GrothendieckTopology C)
    [HasSheafify T AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf T AddCommGrpCat.{u})] :
    (∀ (A : Sheaf T AddCommGrpCat.{u}) (X : C),
      Function.Injective (siteCohomology_zero_section T A X)) ∧
    (∀ (A : Sheaf T AddCommGrpCat.{u}) (X : C),
      siteCohomology_zero_section T A X 0 = 0) ∧
    (∀ (A B : Sheaf T AddCommGrpCat.{u}) (f : A ⟶ B) (X : C)
      (x : Sheaf.H' A 0 X),
      siteCohomology_zero_section T B X
          ((((Sheaf.cohomologyPresheafFunctor T 0).map f).app (op X)).hom x) =
        (f.hom.app (op X)).hom (siteCohomology_zero_section T A X x))
```

## New

The Sheaf module is withdrawn. Its consumer uses these existing upstream declarations:

```lean
noncomputable abbrev objectCohomologyEval₀ {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (V : C) (A : Sheaf J AddCommGrpCat.{u})
    [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] (x : Sheaf.H' A 0 V) : A.obj.obj (op V) :=
  ((Abelian.Ext.addEquiv₀ x).hom.app (op V)).hom
    (((toSheafify J (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
      (FreeAbelianGroup.of (𝟙 V)))

theorem siteCohomology_zero_section_properties
    {C : Type u} [SmallCategory C] (T : GrothendieckTopology C)
    [HasExt.{u} (Sheaf T AddCommGrpCat.{u})] :
    (∀ (A : Sheaf T AddCommGrpCat.{u}) (X : C),
      Function.Injective (Sheaf.objectCohomologyEval₀ T X A)) ∧
    (∀ (A : Sheaf T AddCommGrpCat.{u}) (X : C),
      Sheaf.objectCohomologyEval₀ T X A 0 = 0) ∧
    (∀ (A B : Sheaf T AddCommGrpCat.{u}) (f : A ⟶ B) (X : C)
      (x : Sheaf.H' A 0 X),
      Sheaf.objectCohomologyEval₀ T X B
          ((((Sheaf.cohomologyPresheafFunctor T 0).map f).app (op X)).hom x) =
        (f.hom.app (op X)).hom (Sheaf.objectCohomologyEval₀ T X A x))
```

The upstream definition takes the object before the coefficient sheaf. The consumer
uses canonical small-site abelian sheafification throughout, so its evaluation formula
is definitionally the original one; the normalization equations still close directly.
No choice of an arbitrary unproved witness is introduced.

The consumer's long statement elaborates pullback/Ext expressions. Its final compile
uses these declaration-scoped elaboration options, placed before its docstring:

```lean
set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
```

A 20,000-heartbeat diagnostic stopped at the pullback/Ext compatibility hypothesis;
unscoped default attempts then exceeded the 60-second limit. The scoped settings,
also used in related category-theory files, preserve the elaborated proposition and
bring the consumer's compile to 25 seconds. They do not affect importing modules.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SiteCohomologyZeroSections | D2 | Withdraw the duplicate module. |
| Sheaf.CategoryTheory.CohomologyColimitSitesZeroComparison | unclaimed | Replace its private proof import and references; signature unchanged. |
| Sheaf.CategoryTheory.CohomologyColimitSitesEventualVanishing | unclaimed | Transitive importer; no mention of either retired name, no change. |
| Sheaf.CategoryTheory.CohomologyColimitSites | unclaimed | Transitive importer; no mention of either retired name, no change. |
| Sheaf.AlgebraicGeometry.RelativeHigherDirectImageContinuity | unclaimed | Transitive importer; no mention of either retired name, no change. |

Both `tools/downstream.py --uses` searches list just the withdrawn module and the
direct consumer as textual users. The direct consumer's original and replacement
were compiled separately. Its public imports, declarations and theorem signatures
stay identical; its proof-only import hides the upstream names from its importers.
The DAG node is reattached to the existing upstream theorem, preserving its mathematical
statement and proof dependencies. Target statements and definitions are unchanged.

## Status

landed 20261020T141306-L-2032555 2026-10-20 (merge of deliver/D2/Sheaf.CategoryTheory.SiteCohomologyZeroSections)
