/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceComparison
import WeilConjectures.AlgebraicGeometry.SourceDerivedSectionsNaturalityCore

/-! # Naturality of the derived Hom to sections comparison

## References

* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex CochainComplex.HomComplex

namespace AlgebraicGeometry.Etale

/-- Localizing Hom classes and evaluating the free generator commutes with restriction. -/
theorem sourceDerivedSections_naturality
    {C : Type (v + 1)} [Category.{v} C]
    {T : GrothendieckTopology C} [HasSheafify T AddCommGrpCat.{v + 1}]
    [HasDerivedCategory.{v + 1} (Sheaf T AddCommGrpCat.{v + 1})]
    (K : DerivedCategory.Plus (Sheaf T AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf T AddCommGrpCat.{v + 1}) ℤ) [L.IsKInjective]
    (q : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ) {U V : C} (a : U ⟶ V) :
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n
    let e := fun W : C ↦
      sourcePlusHomIso ((strictLocalFreeSheaf T).obj W) K L q n ≪≫
      (sourceClassDerivedHomIso ((strictLocalFreeSheaf T).obj W) L n).symm ≪≫
      (leftHomologyData ((CochainComplex.singleFunctor _ 0).obj
        ((strictLocalFreeSheaf T).obj W)) L n).homologyIso.symm ≪≫
      H.mapIso (sourceFreeSectionsComplexIso W L)
    AddCommGrpCat.ofHom (Preadditive.leftComp (K⟦n⟧)
      ((DerivedCategory.Plus.singleFunctor _ 0).map ((strictLocalFreeSheaf T).map a))) ≫
        (e U).hom =
      (e V).hom ≫ H.map
        ((NatTrans.mapHomologicalComplex
          ((sheafSections T AddCommGrpCat.{v + 1}).map a.op) (.up ℤ)).app L) := by
  simpa only [Iso.trans_hom, Category.assoc] using
    (sourceDerivedSections_naturality_compose K L q n a)


end AlgebraicGeometry.Etale
