# AlgebraicGeometry.Etale.StrictLocalMateProjectionData

## Reason

The assignment is the DIFFERENT retirement in coord/retire-items.tsv, row 956.
The item has zero sorry bodies. Its two maps and structure collide with the adopted
source library's public names, but the adopted definitions use strictLocalization and
strictLocalizationToBase. The live Sheaf consumers instead use the spectrum of the small
coordinate-ring colimit, strictHenselizationScheme and strictHenselizationStructuralMap.
Those schemes are canonically isomorphic, not definitionally equal. Replacing the import
with the adopted module would change the existing small-model formulas.

Withdraw the old twin. The adopted canonical names are left verbatim in
WeilConjectures.AlgebraicGeometry.StrictLocalMateProjectionData. Preserve only the needed
small-model target isomorphism and data structure under explicit, distinct names in
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.MateProjectionData. The target isomorphism's
body and every structure field are byte-identical after renaming the two declarations.
The unused local homology-map abbreviation is removed; no consumer used it.

The canonical DAG attachment moves to the adopted source; a separate definition node
records the small-model construction. Ten dependent node descriptions explicitly retain
their small-model objects and formulas. All thirteen adapted consumer modules are unclaimed
in the current coordination snapshot. Their edits are import removal, import replacement,
and the two explicit name substitutions, including the same substitution in docstrings.
StrictLocalInjectiveSourceDerivedRestriction additionally spells out the category of
InjectiveObject.ι in q and scopes backward.isDefEq.respectTransparency=false to the
proof body; its statement is elaborated with respectTransparency=true. Profiling the
original version found expensive normalization in q and a 60-second timeout. The
category annotation is the category already determined by J. It changes no resolved
parameter type, universe or mathematical proof step. The adjusted file compiled in
56.1 seconds under the standard limit; no heartbeat limit is raised. All temporary
diagnostic options were removed.
No source-library file is edited. No hypothesis, conclusion, target statement, universe,
canonical map or choice changes. The existing derived-restriction proof steps are
preserved, with only their elaboration scope adjusted. The additional proof-dependency substitution below uses
the identical adopted theorem. The mathematical meaning of target definitions
is preserved, so semantic target review is not reopened.

## Old

The withdrawn module, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.ExactGlobalSectionsLeray
public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry
public import Sheaf.AlgebraicGeometry.StrictHenselizationSchemeSectionsExact
public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.CohomologyGerms
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs

/-! # Projection restriction formulas for the strict-local mate

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The global-sections map of the degree-n homology of the derived strict-local mate.
Source: Stacks, Tag 03Q9, final proof paragraph
(blueprint: def-weil-pbc-strict-local-mate-projection-data). -/
noncomputable abbrev strictLocalBaseChangeHomologyMap
    {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}).obj
      ((DerivedCategory.Plus.homologyFunctor _ n).obj
        ((upperStar AddCommGrpCat.{v + 1}
          (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlus.obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K))) ⟶
    (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}).obj
      ((DerivedCategory.Plus.homologyFunctor _ n).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1}
          (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).obj
          ((upperStar AddCommGrpCat.{v + 1}
            (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).mapDerivedCategoryPlus.obj
            K))) :=
  ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
    AddCommGrpCat.{v + 1}).map
    ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
        (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
          (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
        (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
          (IsPullback.of_hasPullback f
            (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
            |>.natTrans.app K)))

/-- Exact strict-local sections and Leray identify the target with limit cohomology.
Source: Stacks, Tags 03Q9 and 03QO
(blueprint: def-weil-pbc-strict-local-mate-projection-data). -/
noncomputable def strictLocalBaseChangeTargetIso
    {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}).obj
      ((DerivedCategory.Plus.homologyFunctor _ n).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1}
          (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).obj
          ((upperStar AddCommGrpCat.{v + 1}
            (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).mapDerivedCategoryPlus.obj
            K))) ≅
    (cohomology AddCommGrpCat.{v + 1}
      (pullback f (Scheme.strictHenselizationStructuralMap s)) n).obj
      ((upperStar AddCommGrpCat.{v + 1}
        (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).mapDerivedCategory.obj
        K.obj) :=
  exactGlobalSectionsLerayHomologyIso
    (strictHenselizationScheme_globalSections_preservesFiniteColimits s)
    (pullback.snd f (Scheme.strictHenselizationStructuralMap s)) n _

/-- Hypercohomology identifications, their transitions, and their compatibility with
projection restriction. There is no source colimit assertion in this data.
Source: Stacks, Tag 03Q9, final proof paragraph
(blueprint: def-weil-pbc-strict-local-mate-projection-data). -/
structure StrictLocalMateProjectionData
    {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) (Q : StrictLocalNeighbourhoodGeometry f s) where
  e : ∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
        (strictLocalCohomologyNeighbourhoodFunctor s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).obj (op i) ≅
    (cohomology AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).obj i) n).obj
      ((upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app
        i)).mapDerivedCategory.obj K.obj)
  transition : ∀ {i j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)} (a : i ⟶ j),
        (strictLocalCohomologyNeighbourhoodFunctor s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).map a.op =
      (e j).hom ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).obj j) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
          ((strictLocalNeighbourhoodDiagram f s).map a)).unit.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app
        j)).mapDerivedCategory.obj
              K.obj)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).map a)).hom.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).map
        a)).mapDerivedCategory.obj
              ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f
        s).app j)).mapDerivedCategory.obj
                K.obj))) ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).obj i) n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).map a)
        ((strictLocalNeighbourhoodProjection f s).app j)
            ((strictLocalNeighbourhoodProjection f s).app i) ((Category.comp_id
        ((strictLocalNeighbourhoodProjection f s).app i)).symm.trans
        ((strictLocalNeighbourhoodProjection f s).naturality a).symm)) ≪≫
          Functor.mapDerivedCategoryCompIso
            (Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app j))
            (Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).map
        a))).inv.app K.obj) ≫
      (e i).inv
  restriction : ∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
        ((smallModel_strictLocalCohomologySourceLegs s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).app (op i)) ≫
        ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
                |>.natTrans.app K))) =
      (e i).hom ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).obj i) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
          (Q.smallModelLegs.app i)).unit.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app
        i)).mapDerivedCategory.obj
              K.obj)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)).hom.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)).mapDerivedCategory.obj
              ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f
        s).app i)).mapDerivedCategory.obj
                K.obj))) ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} (pullback f (Scheme.strictHenselizationStructuralMap
        s)) n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)
        ((strictLocalNeighbourhoodProjection f s).app i) (pullback.fst f
        (Scheme.strictHenselizationStructuralMap s))
            (Q.smallModelOver i).symm) ≪≫
          Functor.mapDerivedCategoryCompIso
            (Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app i))
            (Etale.upperStar AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i))).inv.app K.obj) ≫
      (strictLocalBaseChangeTargetIso f s K n).inv


end AlgebraicGeometry.Etale
```

## New

The withdrawn path is listed in deleted.txt; delivery leaves an empty module with no
public declarations. The new small-model module is:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.ExactGlobalSectionsLeray
public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry
public import Sheaf.AlgebraicGeometry.StrictHenselizationSchemeSectionsExact
public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.CohomologyGerms
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs

/-! # Projection data for the small coordinate-ring colimit model

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.

The target is `strictHenselizationScheme s`. The adopted names in
`WeilConjectures.AlgebraicGeometry.StrictLocalMateProjectionData` use
`strictLocalization s`; the explicit small-model names here keep the two APIs distinct.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Exact strict-local sections and Leray identify the target with limit cohomology.
Source: Stacks, Tags 03Q9 and 03QO
(blueprint: def-weil-pbc-small-model-mate-projection-data). -/
noncomputable def smallModel_strictLocalBaseChangeTargetIso
    {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}).obj
      ((DerivedCategory.Plus.homologyFunctor _ n).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1}
          (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).obj
          ((upperStar AddCommGrpCat.{v + 1}
            (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).mapDerivedCategoryPlus.obj
            K))) ≅
    (cohomology AddCommGrpCat.{v + 1}
      (pullback f (Scheme.strictHenselizationStructuralMap s)) n).obj
      ((upperStar AddCommGrpCat.{v + 1}
        (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).mapDerivedCategory.obj
        K.obj) :=
  exactGlobalSectionsLerayHomologyIso
    (strictHenselizationScheme_globalSections_preservesFiniteColimits s)
    (pullback.snd f (Scheme.strictHenselizationStructuralMap s)) n _

/-- Hypercohomology identifications, their transitions, and their compatibility with
projection restriction. There is no source colimit assertion in this data.
Source: Stacks, Tag 03Q9, final proof paragraph
(blueprint: def-weil-pbc-small-model-mate-projection-data). -/
structure SmallModelStrictLocalMateProjectionData
    {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) (Q : StrictLocalNeighbourhoodGeometry f s) where
  e : ∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
        (strictLocalCohomologyNeighbourhoodFunctor s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).obj (op i) ≅
    (cohomology AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).obj i) n).obj
      ((upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app
        i)).mapDerivedCategory.obj K.obj)
  transition : ∀ {i j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)} (a : i ⟶ j),
        (strictLocalCohomologyNeighbourhoodFunctor s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).map a.op =
      (e j).hom ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).obj j) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
          ((strictLocalNeighbourhoodDiagram f s).map a)).unit.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app
        j)).mapDerivedCategory.obj
              K.obj)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).map a)).hom.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).map
        a)).mapDerivedCategory.obj
              ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f
        s).app j)).mapDerivedCategory.obj
                K.obj))) ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).obj i) n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).map a)
        ((strictLocalNeighbourhoodProjection f s).app j)
            ((strictLocalNeighbourhoodProjection f s).app i) ((Category.comp_id
        ((strictLocalNeighbourhoodProjection f s).app i)).symm.trans
        ((strictLocalNeighbourhoodProjection f s).naturality a).symm)) ≪≫
          Functor.mapDerivedCategoryCompIso
            (Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app j))
            (Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).map
        a))).inv.app K.obj) ≫
      (e i).inv
  restriction : ∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
        ((smallModel_strictLocalCohomologySourceLegs s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).app (op i)) ≫
        ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
                |>.natTrans.app K))) =
      (e i).hom ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).obj i) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
          (Q.smallModelLegs.app i)).unit.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app
        i)).mapDerivedCategory.obj
              K.obj)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)).hom.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)).mapDerivedCategory.obj
              ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f
        s).app i)).mapDerivedCategory.obj
                K.obj))) ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} (pullback f (Scheme.strictHenselizationStructuralMap
        s)) n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)
        ((strictLocalNeighbourhoodProjection f s).app i) (pullback.fst f
        (Scheme.strictHenselizationStructuralMap s))
            (Q.smallModelOver i).symm) ≪≫
          Functor.mapDerivedCategoryCompIso
            (Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app i))
            (Etale.upperStar AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i))).inv.app K.obj) ≫
      (smallModel_strictLocalBaseChangeTargetIso f s K n).inv


end AlgebraicGeometry.Etale
```

The adopted source remains unchanged. Consumer substitutions are
`strictLocalBaseChangeTargetIso` → `smallModel_strictLocalBaseChangeTargetIso` and
`StrictLocalMateProjectionData` → `SmallModelStrictLocalMateProjectionData`.
EtaleInjectiveSectionsComparison imports the narrower small-model CohomologyGerms API
instead of projection data. SourceCocycleExactRestriction, StrictLocalLocalizedHomGerm,
and StrictLocalDerivedExchangeLeray remove their unused projection-data proof import.
Every module whose public signature mentions the renamed target isomorphism imports the
new data module publicly and directly: StrictLocalDerivedExchangeGlobalSections,
StrictLocalDerivedMateSectionsFactorization, StrictLocalComplexSectionsMate,
StrictLocalInjectiveSourceDerivedRestriction, StrictLocalInjectiveSourceRestriction and
StrictLocalInjectiveSourceSections. StrictLocalMateProjectionFormulas also imports it
publicly for the data structure. The continuity presentation uses it only in its proof
through its existing private import of the projection formulas.

## Users

Computed with tools/downstream.py on the original module, with --uses for each of the
three original names, and on DerivedCohomologyGermIso with --uses for its original
theorem name. All 25 projection-data downstream modules and the additional direct
germ-isomorphism consumer are listed, including those that require no source change.
Canonical source-library consumers import the adopted module and are
outside this small-model dependency closure; they remain unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleInjectiveSectionsComparison | unclaimed | Replace public projection-data import with small-model CohomologyGerms; same formulas. |
| Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso | unclaimed | Unchanged; no textual use of a retired name; existing mathematical interface preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology | unclaimed | Unchanged; no textual use of a retired name; existing mathematical interface preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology | unclaimed | Unchanged; no textual use of a retired name; existing mathematical interface preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation | unclaimed | Rename the target isomorphism in its proof; public signature unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.InjectiveExchangeRepresentative | unclaimed | Unchanged; no textual use of a retired name; existing mathematical interface preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.InjectiveExchangeSourceTransport | unclaimed | Unchanged; no textual use of a retired name; existing mathematical interface preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.InjectiveExchangeTargetTransport | unclaimed | Unchanged; no textual use of a retired name; existing mathematical interface preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceCocycleExactRestriction | unclaimed | Remove unused projection-data proof import; declarations unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceDerivedSectionsNaturality | unclaimed | Unchanged; no textual use of a retired name; existing mathematical interface preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceDerivedSectionsNaturalityCore | unclaimed | Unchanged; no textual use of a retired name; existing mathematical interface preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceLocalizedCocycleHomology | unclaimed | Unchanged; no textual use of a retired name; existing mathematical interface preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceStageSectionsNaturality | unclaimed | Unchanged; no textual use of a retired name; existing mathematical interface preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalCohomologySourceColimit | unclaimed | Replace the private DerivedCohomologyGermIso import and smallModel_isIso_strictLocalCohomologyGermMap by the identical adopted import and isIso_strictLocalCohomologyGermMap theorem; public signature and cocone construction unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalComplexSectionsMate | unclaimed | Use explicit small-model target-isomorphism name; add a direct public data import where it occurs in the signature; identical formulas. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedExchangeGlobalSections | unclaimed | Use explicit small-model target-isomorphism name; add a direct public data import where it occurs in the signature; identical formulas. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedExchangeLeray | unclaimed | Remove unused projection-data proof import; declarations unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedMateSectionsFactorization | unclaimed | Use explicit small-model target-isomorphism name; add a direct public data import where it occurs in the signature; identical formulas. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceComparison | unclaimed | Unchanged; no textual use of a retired name; existing mathematical interface preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceDerivedRestriction | unclaimed | Rename the target isomorphism and import its data publicly; spell out the already determined category of q and scope aggressive unfolding to the proof; identical resolved signature and formulas. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceRestriction | unclaimed | Use explicit small-model target-isomorphism name; add a direct public data import where it occurs in the signature; identical formulas. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceSections | unclaimed | Use explicit small-model target-isomorphism name; add a direct public data import where it occurs in the signature; identical formulas. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceTransition | unclaimed | Unchanged; no textual use of a retired name; existing mathematical interface preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalLocalizedHomGerm | unclaimed | Remove unused projection-data proof import; declarations unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalMateProjectionFormulas | unclaimed | Import explicit small-model data and name its structure; identical field assembly. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalUnderivedSectionsMate | unclaimed | Unchanged; no textual use of a retired name; existing mathematical interface preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.MateProjectionData | new, H1 | Concrete existing small-model target isomorphism and structure with distinct names. |

## Additional duplicate proof pruned

StrictLocalSmallModel.DerivedCohomologyGermIso has one public declaration,
smallModel_isIso_strictLocalCohomologyGermMap. Its statement contains only the common
canonical presheaf and germ map, without a strict-local scheme model. Since the
cohomology-germs retirement already adopted those common definitions, this is exactly
WeilConjectures.AlgebraicGeometry.DerivedCohomologyGermIso.isIso_strictLocalCohomologyGermMap
(in namespace AlgebraicGeometry.Etale). Replace the sole consumer's private proof import
and theorem name, and withdraw the duplicate proved module. Preserve the node
lem-weil-pbc-derived-cohomology-germ-isomorphism, reattached to the unchanged adopted
theorem; its statement and proof dependencies do not change. No source-library proof or
public import is changed. Both affected Sheaf modules are unclaimed.

Old and adopted theorem signatures differ only in the `smallModel_` prefix:

```lean
theorem smallModel_isIso_strictLocalCohomologyGermMap {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    IsIso ((Scheme.pointSmallEtale s).presheafFiber.map
      (strictLocalCohomologyGermMap L n))

theorem isIso_strictLocalCohomologyGermMap {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    IsIso ((Scheme.pointSmallEtale s).presheafFiber.map
      (strictLocalCohomologyGermMap L n))
```

The only direct consumer is StrictLocalSmallModel.StrictLocalCohomologySourceColimit,
whose proof changes only the private import and the name after `have :=`. Its public
signature and construction are unchanged. All five downstream consumers were checked:
StrictLocalSmallModel.StrictLocalCohomologySourceColimit (the direct adaptation),
StrictLocalMateContinuityPresentation (already adapted for the data name), and
StrictHenselizationCohomologyComparisonIso, StrictLocalBaseChangeGlobalHomology,
StrictLocalBaseChangeModelGlobalHomology (unchanged). There are no other public
names in the withdrawn helper and no remaining imports or uses. The original helper's
private proofs and the adopted source implementation prove the same generic stalk
isomorphism; no small-model comparison is being assumed.

The 28-module validation batch compiled without warnings. Fourteen packet sources are
unchanged validation dependencies; they ensure a rebuild against the changed public
imports and yield no git diff. The original target/data compatibility probe also passed.

## Status

landed 20261022T025328-L-1279972 2026-10-22 (merge of deliver/H1/Sheaf.AlgebraicGeometry.StrictLocalMateProjectionData)
