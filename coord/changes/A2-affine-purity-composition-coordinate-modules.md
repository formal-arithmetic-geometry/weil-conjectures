# AlgebraicGeometry.ProEtale.AffineSpacePurity.transportedComparison

## Reason

The composition theorem contains two independent arguments: ordered regrouping and
permutation invariance of the actual comparisons. Each remaining theorem needs the
existing concrete coordinate maps. Move these existing declarations into
`Sheaf.Paper.AffineSpacePurityCompositionMaps`, and publicly reexport them from their
original module, to allow both new theorem modules to import the constructions
without an import cycle. This is an ownership/layout change, not a new notion or
an altered definition. It is not a compile-time split.

All existing names, signatures, attributes and bodies are retained verbatim, except
that moved docstrings cite their new construction-owner node. The original four
public imports remain verbatim in the item module. Its new public Maps import
reexports all moved declarations and the same instances. Its sole theorem retains
its exact statement. No source-library file changes.

The complete moved set is:

- `AlgebraicGeometry.ProEtale.AffineSpacePurity.actionAddIso`
- `AlgebraicGeometry.ProEtale.AffineSpacePurity.projectionSource`
- `AlgebraicGeometry.ProEtale.AffineSpacePurity.twistPullbackIso`
- `AlgebraicGeometry.ProEtale.AffineSpacePurity.blockSourceIso`
- `AlgebraicGeometry.ProEtale.AffineSpacePurity.isoExceptional`
- `AlgebraicGeometry.ProEtale.AffineSpacePurity.blockSchemeEq`
- `AlgebraicGeometry.ProEtale.AffineSpacePurity.blockProjection`
- `AlgebraicGeometry.ProEtale.AffineSpacePurity.coordinateMap`
- `AlgebraicGeometry.ProEtale.AffineSpacePurity.coordinateMap_isIso`
- `AlgebraicGeometry.ProEtale.AffineSpacePurity.coordinateIso`
- `AlgebraicGeometry.ProEtale.AffineSpacePurity.coordinateProjection`
- `AlgebraicGeometry.ProEtale.AffineSpacePurity.blockPermutation`
- `AlgebraicGeometry.ProEtale.AffineSpacePurity.purityProjectionCompactification`
- `AlgebraicGeometry.ProEtale.AffineSpacePurity.exceptionalPositive_obj_eq`
- `AlgebraicGeometry.ProEtale.AffineSpacePurity.positiveComparison_existsUnique`
- `AlgebraicGeometry.ProEtale.AffineSpacePurity.positiveComparison`
- `AlgebraicGeometry.ProEtale.AffineSpacePurity.coordinateSourceIso`
- `AlgebraicGeometry.ProEtale.AffineSpacePurity.transportedComparison`
- `AlgebraicGeometry.ProEtale.AffineSpacePurity.blockProjectionCompactification`
- `AlgebraicGeometry.ProEtale.AffineSpacePurity.blockComposite`

## Old

Owner: `Sheaf.Paper.AffineSpacePurityComposition`. The principal transport construction
is, verbatim:

```lean
def transportedComparison (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) (n : ℕ)
    {X : Scheme.{u}} (i : X ≅ iteratedAffineLine Y (n + 1)) (g' : X ⟶ Y)
    [hg' : HasCompactification g'] (h : i.hom ≫ iteratedAffineLineProj Y (n + 1) = g') :
    (projectionSource P g' (n + 1)).obj K.obj ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} (Ring P)) g').obj K.obj :=
  letI : IsNoetherian Y := tower_noetherian P Y aY 0
  letI : IsNoetherian (iteratedAffineLine Y (n + 1)) := tower_noetherian P Y aY (n + 1)
  letI : HasCompactification (i.hom ≫ iteratedAffineLineProj Y (n + 1)) :=
    HasCompactification.comp_of_isOpenImmersion
      (iteratedAffineLineProj Y (n + 1)) i.hom
  (coordinateSourceIso P i (iteratedAffineLineProj Y (n + 1)) g' h
    (towerBase aY (n + 1)) K.obj (n + 1)).hom ≫
    (inverseImage (Ring P) i.hom).map (positiveComparison P Y aY K Ke hKe eK n) ≫
    (isoExceptional (Ring P) i
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} (Ring P))
        (iteratedAffineLineProj Y (n + 1))).obj K.obj)
      (exceptionalEtale P Y n K.obj)
      (Etale.plus_rightDerivedUpperShriek_obj (ModuleCat.{u + 1} (Ring P))
        (iteratedAffineLineProj Y (n + 1)) _
        (plus_rightDerivedFunctor_comparisonLowerStar_obj K.property))
      (eqToIso ((exceptionalEtale_eq P Y n K.obj).trans
        (exceptionalPositive_obj_eq P Y n K.obj)))).hom ≫
    compositionInverse (Ring P) i.hom (iteratedAffineLineProj Y (n + 1)) K ≫
    (rightDerivedUpperShriekCongr (ModuleCat.{u + 1} (Ring P)) h).hom.app K.obj
```

Every other moved declaration is exactly the corresponding declaration preceding
`affineSpacePurityComposition` in that module; the delivery diff records the full
unchanged declaration bodies.

## New

Owner: `Sheaf.Paper.AffineSpacePurityCompositionMaps`. The principal construction is
identical:

```lean
def transportedComparison (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) (n : ℕ)
    {X : Scheme.{u}} (i : X ≅ iteratedAffineLine Y (n + 1)) (g' : X ⟶ Y)
    [hg' : HasCompactification g'] (h : i.hom ≫ iteratedAffineLineProj Y (n + 1) = g') :
    (projectionSource P g' (n + 1)).obj K.obj ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} (Ring P)) g').obj K.obj :=
  letI : IsNoetherian Y := tower_noetherian P Y aY 0
  letI : IsNoetherian (iteratedAffineLine Y (n + 1)) := tower_noetherian P Y aY (n + 1)
  letI : HasCompactification (i.hom ≫ iteratedAffineLineProj Y (n + 1)) :=
    HasCompactification.comp_of_isOpenImmersion
      (iteratedAffineLineProj Y (n + 1)) i.hom
  (coordinateSourceIso P i (iteratedAffineLineProj Y (n + 1)) g' h
    (towerBase aY (n + 1)) K.obj (n + 1)).hom ≫
    (inverseImage (Ring P) i.hom).map (positiveComparison P Y aY K Ke hKe eK n) ≫
    (isoExceptional (Ring P) i
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} (Ring P))
        (iteratedAffineLineProj Y (n + 1))).obj K.obj)
      (exceptionalEtale P Y n K.obj)
      (Etale.plus_rightDerivedUpperShriek_obj (ModuleCat.{u + 1} (Ring P))
        (iteratedAffineLineProj Y (n + 1)) _
        (plus_rightDerivedFunctor_comparisonLowerStar_obj K.property))
      (eqToIso ((exceptionalEtale_eq P Y n K.obj).trans
        (exceptionalPositive_obj_eq P Y n K.obj)))).hom ≫
    compositionInverse (Ring P) i.hom (iteratedAffineLineProj Y (n + 1)) K ≫
    (rightDerivedUpperShriekCongr (ModuleCat.{u + 1} (Ring P)) h).hom.app K.obj
```

The original module adds:

```lean
public import Sheaf.Paper.AffineSpacePurityCompositionMaps
```

The maps module publicly imports the same four original public prerequisites. All
its data definitions and existing proof bodies are unchanged; no hollow data or
new choice operation is introduced. The two new theorem modules state the genuinely
separate remaining ordered-regrouping and permutation arguments, and the item proves
the even sign and assembles the three clauses.

## Users

`tools/downstream.py Sheaf.Paper.AffineSpacePurityComposition` reports zero downstream
modules. With `--uses AlgebraicGeometry.ProEtale.AffineSpacePurity.transportedComparison`,
the only lexical user is the item itself. A direct import search likewise finds no
current external Lean importer. This does not withdraw the item: its unfinished
DAG parents still need it, and their dependencies and statements are preserved.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AffineSpacePurityComposition | A2 | Reexports the exact coordinate API; unchanged theorem statement, completed assembly. |
| Sheaf.Paper.AffineSpacePurityCompositionMaps | new, A2 | Owns the unchanged construction declarations. |
| Sheaf.Paper.AffineSpacePurityOrderedBlocks | new, A2 | Uses the coordinate API to state the ordered regrouping step. |
| Sheaf.Paper.AffineSpacePurityCoordinateInvariance | new, A2 | Uses the coordinate API to state invariance under arbitrary coordinate permutations. |

No other consumer needs adaptation. No target statement or meaning changes; the
extraction changes declaration ownership only.

## Status

landed 20261025T211934-L-4162362 2026-10-25 (merge of deliver/A2/Sheaf.Paper.AffineSpacePurityComposition)
