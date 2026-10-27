# AlgebraicGeometry.Etale.smallModel_injectiveSections_strictLocal_comparison

## Reason

This is the DIFFERENT retirement item in coord/retire-items.tsv. The assigned module
has zero sorry bodies. Its five public sections constructions are byte-identical to
WeilConjectures.AlgebraicGeometry.EtaleInjectiveSectionsComparison, but its theorem
has a genuinely different last clause: the pullback uses strictHenselizationStructuralMap
and Q.smallModelLegs, whereas the adopted theorem uses strictLocalizationToBase and
Q.legs. The small-model statement is needed by the live mate proof and cannot be
replaced by the canonical-model statement or withdrawn without replacement.

Withdraw the old twin module. Reuse the five common constructions from the adopted
source and retain only the distinct small-model theorem in
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.EtaleInjectiveSectionsComparison,
under the explicit smallModel_ name. The first two clauses are exactly the adopted
comparison theorem's first two clauses; the last is arbitrary triangle naturality
for the transported small-model leg, with Q.smallModelOver supplying the triangle.
This also removes the duplicate private etale-invertibility proof. No adopted
source file, declaration, signature, attribute, or public import changes.

The validation probe checks each of the five common constructions by rfl, comparing
against private copies of their old bodies, and applies the renamed theorem to the
entire original small-model statement. Thus no target statement, object, hypothesis,
conclusion, chosen representative, or canonical map changes. The corresponding DAG
node is preserved and reattached to the renamed theorem; there is no new node or hole.
Historical quarantine snapshots of already-retired source-section twins are not
current rework entries and are not changed or used as evidence of withdrawal.

The first consumer rebuild exposed a formerly indirect dependency in
StrictLocalSmallModel.StrictLocalLocalizedHomGerm: unknown identifiers
smallModel_strictLocalCohomologySourceLegs at lines 146 and 186 and
smallModel_strictLocalCohomologySourceLegs_app at line 155. Add the direct public
StrictLocalSmallModel.CohomologyGerms import there, where those names occur in
public statements. No declaration or proof in that consumer changes. All six
adapted consumers are unclaimed.

## Old

The old item module, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.CohomologyGerms
public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry
import WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic
import WeilConjectures.AlgebraicGeometry.EtaleSectionsTriangleNaturality

/-! # Termwise sections and derived pullback cohomology

Source: Stacks Project, Tag 03Q9, final injective-complex restriction paragraph.
(blueprint: lem-weil-pbc-injective-sections-pullback-comparison).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Sections of an inverse image, using the unit and the underived Leray comparison.
Source: Stacks, Tag 03Q9, final proof paragraph
(blueprint: lem-weil-pbc-injective-sections-pullback-comparison). -/
noncomputable def sectionsPullbackNat {Y Z : Scheme.{v}} (a : Y ⟶ Z) :
    Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{v + 1} ⟶
      upperStar AddCommGrpCat.{v + 1} a ⋙
        Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1} :=
  Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} a).unit
      (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{v + 1}) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (upperStar AddCommGrpCat.{v + 1} a)
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} a).hom

/-- Cohomology of the actual complex of sections, before deriving sections.
Source: Stacks, Tag 03Q9, final proof paragraph
(blueprint: lem-weil-pbc-injective-sections-pullback-comparison). -/
noncomputable abbrev termwiseSectionsCohomology (Y : Scheme.{v})
    (C : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) (n : ℤ) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).obj
    (DerivedCategory.Q.obj
      (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).mapHomologicalComplex
        (.up ℤ)).obj C))

/-- The actual chain-level restriction of sections along a triangle, on cohomology.
Source: Stacks, Tag 03Q9, final proof paragraph
(blueprint: lem-weil-pbc-injective-sections-pullback-comparison). -/
noncomputable def termwiseSectionsRestriction {X Y T : Scheme.{v}}
    (a : X ⟶ Y) (g : Y ⟶ T) (h : X ⟶ T) (hh : h = a ≫ g)
    (J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) (n : ℤ) :
    termwiseSectionsCohomology Y
      (((upperStar AddCommGrpCat.{v + 1} g).mapHomologicalComplex (.up ℤ)).obj J) n ⟶
      termwiseSectionsCohomology X
        (((upperStar AddCommGrpCat.{v + 1} h).mapHomologicalComplex (.up ℤ)).obj J) n :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
    (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (sectionsPullbackNat a) (.up ℤ)).app
          (((upperStar AddCommGrpCat.{v + 1} g).mapHomologicalComplex (.up ℤ)).obj J) ≫
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}).mapHomologicalComplex
          (.up ℤ)).map ((NatIso.mapHomologicalComplex
            (upperStarComp AddCommGrpCat.{v + 1} a g h hh) (.up ℤ)).inv.app J)))

/-- The canonical comparison from termwise sections to derived sections. Its unit
is used even if the complex is not acyclic for sections.
Source: Stacks, Tag 03Q9, final injective-complex paragraph (map to derived sections)
(blueprint: lem-weil-pbc-injective-sections-pullback-comparison). -/
noncomputable def termwiseSectionsToDerived (Y : Scheme.{v})
    (C : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) (n : ℤ) :
    termwiseSectionsCohomology Y C n ⟶
      (cohomology AddCommGrpCat.{v + 1} Y n).obj (DerivedCategory.Q.obj C) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
    ((DerivedCategory.quotientCompQhIso AddCommGrpCat.{v + 1}).inv.app
        (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).mapHomologicalComplex
          (.up ℤ)).obj C) ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj C) ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.map
        ((DerivedCategory.quotientCompQhIso _).hom.app C))

/-- Transport the canonical sections comparison through a specified representative.
Source: Stacks, Tag 03Q9, final proof paragraph
(blueprint: lem-weil-pbc-injective-sections-pullback-comparison). -/
noncomputable def representativeSectionsComparison {Y T : Scheme.{v}} (g : Y ⟶ T)
    {K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{v + 1})}
    {J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ}
    (q : K ≅ DerivedCategory.Q.obj J) (n : ℤ) :
    termwiseSectionsCohomology Y
      (((upperStar AddCommGrpCat.{v + 1} g).mapHomologicalComplex (.up ℤ)).obj J) n ⟶
      (cohomology AddCommGrpCat.{v + 1} Y n).obj
        ((upperStar AddCommGrpCat.{v + 1} g).mapDerivedCategory.obj K) :=
  termwiseSectionsToDerived Y
      (((upperStar AddCommGrpCat.{v + 1} g).mapHomologicalComplex (.up ℤ)).obj J) n ≫
    (cohomology AddCommGrpCat.{v + 1} Y n).map
      (((upperStar AddCommGrpCat.{v + 1} g).mapDerivedCategoryFactors.inv.app J) ≫
        (upperStar AddCommGrpCat.{v + 1} g).mapDerivedCategory.map q.inv)

private theorem isIso_representativeSectionsComparison_of_etale
    {Y T : Scheme.{v}} (g : Y ⟶ T) [AlgebraicGeometry.Etale g]
    {K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{v + 1})}
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) (n : ℤ) :
    IsIso (representativeSectionsComparison g q n) := by
  let C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ :=
    ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
  let D : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ :=
    ((upperStar AddCommGrpCat.{v + 1} g).mapHomologicalComplex (.up ℤ)).obj C
  have (k : ℤ) : Injective (D.X k) :=
    injective_upperStar_obj_of_etale_addCommGrp g ((J.obj.X k).obj)
  obtain ⟨d, hd⟩ := J.property
  have : J.obj.IsStrictlyGE d := hd
  have : D.IsStrictlyGE d := by
    dsimp [D, C]
    infer_instance
  have : D.IsKInjective := CochainComplex.isKInjective_of_injective D d
  dsimp [representativeSectionsComparison, termwiseSectionsToDerived]
  infer_instance


/-- The comparison from termwise sections to stage hypercohomology is invertible,
and intertwines both neighbourhood and cone restrictions. This theorem concerns
only the derived-sections unit and its naturality, not derived Hom or the mate.
Source: Stacks, Tag 03Q9, final injective-complex paragraph
(blueprint: lem-weil-pbc-injective-sections-pullback-comparison).

Proof: each stage projection to X is etale. Restriction on its small etale site
preserves injectives, since it has an exact extension-by-zero left adjoint. Hence
the restricted bounded-below complex is K-injective and the right-derived sections
unit there is invertible. This proves the first assertion. Apply naturality of
that unit to termwise sections restriction along each neighbourhood map and each
cone leg. Deriving the sections restriction transformation gives the derived
adjunction unit followed by Leray. Exact inverse-image localization transports
the complex composition comparison to upperStarComp in the derived category.
Naturality with q then gives each displayed square. At the limit use only the
comparison unit, without assuming the pullback of J remains injective. This proves
both squares even for nonetale cone legs. All constructions are valid in negative
degrees and for zero complexes and empty schemes. -/
theorem injectiveSections_strictLocal_comparison {X S : Scheme.{v}}
    (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) (Q : StrictLocalNeighbourhoodGeometry f s)
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    (∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
      IsIso (representativeSectionsComparison
        ((strictLocalNeighbourhoodProjection f s).app i) q n)) ∧
    (∀ {i j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)} (a : i ⟶ j),
      representativeSectionsComparison
        ((strictLocalNeighbourhoodProjection f s).app j) q n ≫
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
        a))).inv.app K.obj) =
        termwiseSectionsRestriction ((strictLocalNeighbourhoodDiagram f s).map a)
          ((strictLocalNeighbourhoodProjection f s).app j)
          ((strictLocalNeighbourhoodProjection f s).app i)
          ((Category.comp_id _).symm.trans
            ((strictLocalNeighbourhoodProjection f s).naturality a).symm)
          (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj) n ≫
        representativeSectionsComparison
          ((strictLocalNeighbourhoodProjection f s).app i) q n) ∧
    (∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
      representativeSectionsComparison
        ((strictLocalNeighbourhoodProjection f s).app i) q n ≫
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
            (Etale.upperStar AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i))).inv.app K.obj) =
        termwiseSectionsRestriction (Q.smallModelLegs.app i)
          ((strictLocalNeighbourhoodProjection f s).app i)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))
          (Q.smallModelOver i).symm
          (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj) n ≫
        representativeSectionsComparison
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) q n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have : AlgebraicGeometry.Etale ((strictLocalNeighbourhoodProjection f s).app i) := by
      dsimp [strictLocalNeighbourhoodProjection]
      infer_instance
    exact isIso_representativeSectionsComparison_of_etale _ J q n
  · intro i j a
    exact sectionsComparison_triangle_naturality
      ((strictLocalNeighbourhoodDiagram f s).map a)
      ((strictLocalNeighbourhoodProjection f s).app j)
      ((strictLocalNeighbourhoodProjection f s).app i)
      ((Category.comp_id _).symm.trans
        ((strictLocalNeighbourhoodProjection f s).naturality a).symm)
      _ q n
  · intro i
    exact sectionsComparison_triangle_naturality (Q.smallModelLegs.app i)
      ((strictLocalNeighbourhoodProjection f s).app i)
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) (Q.smallModelOver i).symm
      _ q n

end AlgebraicGeometry.Etale
```

## New

The original module is withdrawn as an empty module. The common constructions are
sectionsPullbackNat, termwiseSectionsCohomology, termwiseSectionsRestriction,
termwiseSectionsToDerived, and representativeSectionsComparison in the unchanged
WeilConjectures.AlgebraicGeometry.EtaleInjectiveSectionsComparison.
Only the genuinely distinct theorem is retained:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry
public import WeilConjectures.AlgebraicGeometry.EtaleInjectiveSectionsComparison
import WeilConjectures.AlgebraicGeometry.EtaleSectionsTriangleNaturality

/-! # Termwise sections and derived pullback cohomology

Source: Stacks Project, Tag 03Q9, final injective-complex restriction paragraph.
(blueprint: lem-weil-pbc-injective-sections-pullback-comparison).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The comparison from termwise sections to stage hypercohomology is invertible,
and intertwines both neighbourhood and cone restrictions. This theorem concerns
only the derived-sections unit and its naturality, not derived Hom or the mate.
Source: Stacks, Tag 03Q9, final injective-complex paragraph
(blueprint: lem-weil-pbc-injective-sections-pullback-comparison).

Proof: each stage projection to X is etale. Restriction on its small etale site
preserves injectives, since it has an exact extension-by-zero left adjoint. Hence
the restricted bounded-below complex is K-injective and the right-derived sections
unit there is invertible. This proves the first assertion. Apply naturality of
that unit to termwise sections restriction along each neighbourhood map and each
cone leg. Deriving the sections restriction transformation gives the derived
adjunction unit followed by Leray. Exact inverse-image localization transports
the complex composition comparison to upperStarComp in the derived category.
Naturality with q then gives each displayed square. At the limit use only the
comparison unit, without assuming the pullback of J remains injective. This proves
both squares even for nonetale cone legs. All constructions are valid in negative
degrees and for zero complexes and empty schemes. -/
theorem smallModel_injectiveSections_strictLocal_comparison {X S : Scheme.{v}}
    (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) (Q : StrictLocalNeighbourhoodGeometry f s)
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    (∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
      IsIso (representativeSectionsComparison
        ((strictLocalNeighbourhoodProjection f s).app i) q n)) ∧
    (∀ {i j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)} (a : i ⟶ j),
      representativeSectionsComparison
        ((strictLocalNeighbourhoodProjection f s).app j) q n ≫
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
        a))).inv.app K.obj) =
        termwiseSectionsRestriction ((strictLocalNeighbourhoodDiagram f s).map a)
          ((strictLocalNeighbourhoodProjection f s).app j)
          ((strictLocalNeighbourhoodProjection f s).app i)
          ((Category.comp_id _).symm.trans
            ((strictLocalNeighbourhoodProjection f s).naturality a).symm)
          (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj) n ≫
        representativeSectionsComparison
          ((strictLocalNeighbourhoodProjection f s).app i) q n) ∧
    (∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
      representativeSectionsComparison
        ((strictLocalNeighbourhoodProjection f s).app i) q n ≫
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
            (Etale.upperStar AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i))).inv.app K.obj) =
        termwiseSectionsRestriction (Q.smallModelLegs.app i)
          ((strictLocalNeighbourhoodProjection f s).app i)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))
          (Q.smallModelOver i).symm
          (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj) n ≫
        representativeSectionsComparison
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) q n) := by
  have h := injectiveSections_strictLocal_comparison f s K n Q J q
  refine ⟨h.1, h.2.1, ?_⟩
  intro i
  exact sectionsComparison_triangle_naturality (Q.smallModelLegs.app i)
    ((strictLocalNeighbourhoodProjection f s).app i)
    (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) (Q.smallModelOver i).symm
    _ q n

end AlgebraicGeometry.Etale
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso | unclaimed | Unchanged consumer: common sections constructions now resolve to the identical adopted declarations; small-model maps and formulas preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology | unclaimed | Unchanged consumer: common sections constructions now resolve to the identical adopted declarations; small-model maps and formulas preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology | unclaimed | Unchanged consumer: common sections constructions now resolve to the identical adopted declarations; small-model maps and formulas preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation | unclaimed | Unchanged consumer: common sections constructions now resolve to the identical adopted declarations; small-model maps and formulas preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.InjectiveExchangeRepresentative | unclaimed | Unchanged consumer: common sections constructions now resolve to the identical adopted declarations; small-model maps and formulas preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.InjectiveExchangeSourceTransport | unclaimed | Unchanged consumer: common sections constructions now resolve to the identical adopted declarations; small-model maps and formulas preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.InjectiveExchangeTargetTransport | unclaimed | Unchanged consumer: common sections constructions now resolve to the identical adopted declarations; small-model maps and formulas preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceCocycleExactRestriction | unclaimed | Unchanged consumer: common sections constructions now resolve to the identical adopted declarations; small-model maps and formulas preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceDerivedSectionsNaturality | unclaimed | Unchanged consumer: common sections constructions now resolve to the identical adopted declarations; small-model maps and formulas preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceDerivedSectionsNaturalityCore | unclaimed | Unchanged consumer: common sections constructions now resolve to the identical adopted declarations; small-model maps and formulas preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceLocalizedCocycleHomology | unclaimed | Unchanged consumer: common sections constructions now resolve to the identical adopted declarations; small-model maps and formulas preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceStageSectionsNaturality | unclaimed | Unchanged consumer: common sections constructions now resolve to the identical adopted declarations; small-model maps and formulas preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalComplexSectionsMate | unclaimed | Unchanged consumer: common sections constructions now resolve to the identical adopted declarations; small-model maps and formulas preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedExchangeGlobalSections | unclaimed | Unchanged consumer: common sections constructions now resolve to the identical adopted declarations; small-model maps and formulas preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedExchangeLeray | unclaimed | Unchanged consumer: common sections constructions now resolve to the identical adopted declarations; small-model maps and formulas preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedMateSectionsFactorization | unclaimed | Unchanged consumer: common sections constructions now resolve to the identical adopted declarations; small-model maps and formulas preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceComparison | unclaimed | Replace the direct public twin import with the focused small-model module, which publicly imports the identical adopted constructions. Public declarations unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceDerivedRestriction | unclaimed | Use the renamed small-model cone-leg comparison in the proof and identify it in the docstring. Signature unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceRestriction | unclaimed | Use the renamed small-model cone-leg comparison in the proof. Signature unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceSections | unclaimed | Replace the direct public twin import with the focused small-model theorem module. Public declarations unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceTransition | unclaimed | Unchanged consumer: common sections constructions now resolve to the identical adopted declarations; small-model maps and formulas preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalLocalizedHomGerm | unclaimed | Add the direct public CohomologyGerms import needed by the small-model source legs in its unchanged statement; it had relied on the removed twin import. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalMateProjectionFormulas | unclaimed | Use the renamed small-model theorem in the proof. Signature unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalUnderivedSectionsMate | unclaimed | Unchanged consumer: common sections constructions now resolve to the identical adopted declarations; small-model maps and formulas preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.EtaleInjectiveSectionsComparison | new, E2 | Preserve the full original small-model statement under its distinct name, using the adopted common constructions. |

The complete 26-module rebuilt set (retained theorem, equality/signature probe and
all 24 downstream modules) compiled without warnings. Maximum per-file time was
57.2 seconds. The retained theorem uses only propext, Classical.choice and
Quot.sound. Byte-identical validation files remain compile inputs to avoid the older
published dependency artifacts; they and the disposable probe are not committed.

## Status

landed 20261022T044009-L-1166090 2026-10-22 (merge of deliver/E2/Sheaf.AlgebraicGeometry.EtaleInjectiveSectionsComparison)
