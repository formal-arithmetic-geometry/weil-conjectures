/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.CohomologyGerms

public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationSchemeSectionsExact
public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalSectionCone
public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalInjectiveSourceComparison
import WeilConjectures.AlgebraicGeometry.Source.SourceCocycleExactRestriction
public import WeilConjectures.AlgebraicGeometry.StrictLocalLocalizedHomGerm

/-! # Localized Hom classes and restriction of a complex on the base

Source: Stacks Project, Tags 03Q8 and 03Q9, injective-complex computation.
-/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.StrictLocalLocalizedHomGerm.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry CochainComplex CochainComplex.HomComplex

namespace AlgebraicGeometry.Etale

attribute [local irreducible] smallModel_sourcePlusHomIso
  smallModel_sourceClassDerivedHomIso smallModel_sourceFreeSectionsComplexIso

/-- Evaluation of localized Hom classes as cohomology of the complex of sections, in the
small coordinate-ring colimit model.
Source: Stacks Project, Tag 03Q8, computation by an injective complex.
(blueprint: lem-weil-pbc-strict-local-localized-hom-germ). -/
@[irreducible] noncomputable def smallModel_sourceLocalizedSectionsIso {S : Scheme.{v}}
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    [L.IsKInjective] (r : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ) (W : S.Etale) :
    (strictLocalCohomologyPresheaf K n).obj (op W) ≅
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).obj
        ((((sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
          (op W)).mapHomologicalComplex (.up ℤ)).obj L) :=
  smallModel_sourcePlusHomIso ((strictLocalFreeSheaf S.smallEtaleTopology).obj W) K L r n ≪≫
    (smallModel_sourceClassDerivedHomIso
      ((strictLocalFreeSheaf S.smallEtaleTopology).obj W) L n).symm ≪≫
    (leftHomologyData
      ((CochainComplex.singleFunctor _ 0).obj
        ((strictLocalFreeSheaf S.smallEtaleTopology).obj W)) L n).homologyIso.symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).mapIso
      (smallModel_sourceFreeSectionsComplexIso W L)

/-- The natural transformation of pointed neighbourhood section restriction, in the small
coordinate-ring colimit model.
Source: Stacks Project, Tag 03Q9, the canonical restriction construction.
(blueprint: lem-weil-pbc-strict-local-localized-hom-germ). -/
@[irreducible] noncomputable def smallModel_strictLocalSectionRestrictionNat {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    (sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
        (op ((strictLocalNeighbourhoods s).obj i)) ⟶
      upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s) ⋙
        Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          AddCommGrpCat.{v + 1} where
  app F := (strictLocalSectionCone s).restriction F i
  naturality {_ _} b := smallModel_strictHenselizationSectionRestriction_naturality s i b

set_option backward.isDefEq.respectTransparency false in
/-- The restriction on the complex of sections, transported to strict-local homology, in the
small coordinate-ring colimit model.
Source: Stacks Project, Tag 03Q9, restriction of the complex to the strict local scheme.
(blueprint: lem-weil-pbc-strict-local-localized-hom-germ). -/
@[irreducible] noncomputable def smallModel_strictLocalComplexSectionRestriction
    {S : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (r : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).obj
        ((((sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
          (op ((strictLocalNeighbourhoods s).obj i))).mapHomologicalComplex (.up ℤ)).obj L) ⟶
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
        ((DerivedCategory.Plus.homologyFunctor _ n).obj
          ((upperStar AddCommGrpCat.{v + 1}
            (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlus.obj K)) := by
  let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
  let G := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
    AddCommGrpCat.{v + 1}
  have := strictHenselizationScheme_globalSections_preservesFiniteColimits s
  let C := (U.mapHomologicalComplex (.up ℤ)).obj L
  let a := (NatTrans.mapHomologicalComplex (smallModel_strictLocalSectionRestrictionNat s i)
    (.up ℤ)).app L
  exact (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} n).inv.app _ ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
      (DerivedCategory.Q.map a ≫ G.mapDerivedCategoryFactors.inv.app C ≫
        G.mapDerivedCategory.map
          (U.mapDerivedCategoryFactors.inv.app L ≫ U.mapDerivedCategory.map r.inv)) ≫
    (G.mapDerivedCategoryHomologyFunctorIso n).inv.app (U.mapDerivedCategory.obj K.obj)

end AlgebraicGeometry.Etale
