module

public import Sheaf.AlgebraicGeometry.StrictLocalInjectiveSourceComparison

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex CochainComplex.HomComplex
namespace AlgebraicGeometry.Etale

/-- Naturality of the localization and derived Hom part of the source comparison.
Source: Stacks Project, Tags 03Q8 and 03Q9.
(blueprint: lem-weil-pbc-source-derived-sections-naturality-core)

The proof is the cocycle computation: precomposition on the Hom complex descends
through cocycles and boundaries, and the quotient and the specified derived
representative preserve this map. -/
theorem sourceDerivedSections_naturality_core
    {C : Type (v + 1)} [Category.{v} C]
    {T : GrothendieckTopology C} [HasSheafify T AddCommGrpCat.{v + 1}]
    [HasDerivedCategory.{v + 1} (Sheaf T AddCommGrpCat.{v + 1})]
    (K : DerivedCategory.Plus (Sheaf T AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf T AddCommGrpCat.{v + 1}) ℤ) [L.IsKInjective]
    (q : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ) {U V : C} (a : U ⟶ V) :
    let e₀ := fun W : C ↦
      sourcePlusHomIso ((strictLocalFreeSheaf T).obj W) K L q n
    AddCommGrpCat.ofHom (Preadditive.leftComp (K⟦n⟧)
      ((DerivedCategory.Plus.singleFunctor _ 0).map ((strictLocalFreeSheaf T).map a))) ≫
        (e₀ U).hom =
      (e₀ V).hom ≫ AddCommGrpCat.ofHom (Preadditive.leftComp ((DerivedCategory.Q.obj L)⟦n⟧)
        ((DerivedCategory.singleFunctor _ 0).map ((strictLocalFreeSheaf T).map a))) := by
  sorry

/-- Naturality of evaluation of the Hom complex at the free sheaf generator.
Source: Stacks Project, Tags 03Q8 and 03Q9.
(blueprint: lem-weil-pbc-source-derived-sections-naturality-evaluation)

This is the degreewise Yoneda calculation: the free-sheaf evaluation sends
precomposition by the map induced by `a` to restriction of sections, and the
left-homology comparison is functorial. -/
theorem sourceDerivedSections_naturality_evaluation
    {C : Type (v + 1)} [Category.{v} C]
    {T : GrothendieckTopology C} [HasSheafify T AddCommGrpCat.{v + 1}]
    [HasDerivedCategory.{v + 1} (Sheaf T AddCommGrpCat.{v + 1})]
    (K : DerivedCategory.Plus (Sheaf T AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf T AddCommGrpCat.{v + 1}) ℤ) [L.IsKInjective]
    (q : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ) {U V : C} (a : U ⟶ V) :
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n
    let e₁ := fun W : C ↦
      (sourceClassDerivedHomIso ((strictLocalFreeSheaf T).obj W) L n).symm ≪≫
      (leftHomologyData ((CochainComplex.singleFunctor _ 0).obj
        ((strictLocalFreeSheaf T).obj W)) L n).homologyIso.symm ≪≫
      H.mapIso (sourceFreeSectionsComplexIso W L)
    AddCommGrpCat.ofHom (Preadditive.leftComp ((DerivedCategory.Q.obj L)⟦n⟧)
      ((DerivedCategory.singleFunctor _ 0).map ((strictLocalFreeSheaf T).map a))) ≫
        (e₁ U).hom =
      (e₁ V).hom ≫ H.map
        ((NatTrans.mapHomologicalComplex
          ((sheafSections T AddCommGrpCat.{v + 1}).map a.op) (.up ℤ)).app L) := by
  sorry

/-- Composition of the localization and evaluation squares gives the displayed
source comparison square. This is the categorical pasting step in Tags 03Q8--03Q9.
(blueprint: lem-weil-pbc-source-derived-sections-naturality-compose) -/
theorem sourceDerivedSections_naturality_compose
    {C : Type (v + 1)} [Category.{v} C]
    {T : GrothendieckTopology C} [HasSheafify T AddCommGrpCat.{v + 1}]
    [HasDerivedCategory.{v + 1} (Sheaf T AddCommGrpCat.{v + 1})]
    (K : DerivedCategory.Plus (Sheaf T AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf T AddCommGrpCat.{v + 1}) ℤ) [L.IsKInjective]
    (q : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ) {U V : C} (a : U ⟶ V) :
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n
    let e₀ := fun W : C ↦ sourcePlusHomIso ((strictLocalFreeSheaf T).obj W) K L q n
    let e₁ := fun W : C ↦
      (sourceClassDerivedHomIso ((strictLocalFreeSheaf T).obj W) L n).symm ≪≫
      (leftHomologyData ((CochainComplex.singleFunctor _ 0).obj
        ((strictLocalFreeSheaf T).obj W)) L n).homologyIso.symm ≪≫
      H.mapIso (sourceFreeSectionsComplexIso W L)
    AddCommGrpCat.ofHom (Preadditive.leftComp (K⟦n⟧)
      ((DerivedCategory.Plus.singleFunctor _ 0).map ((strictLocalFreeSheaf T).map a))) ≫
        (e₀ U).hom ≫ (e₁ U).hom =
      (e₀ V).hom ≫ (e₁ V).hom ≫ H.map
        ((NatTrans.mapHomologicalComplex
          ((sheafSections T AddCommGrpCat.{v + 1}).map a.op) (.up ℤ)).app L) := by
  dsimp only
  rw [← Category.assoc,
    sourceDerivedSections_naturality_core K L q n a]
  rw [Category.assoc, sourceDerivedSections_naturality_evaluation K L q n a]

end AlgebraicGeometry.Etale
