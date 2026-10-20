/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.GeometricPointDerivedConstants
public import Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction
public import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import Sheaf.AlgebraicGeometry.GeometricPointPullbackTensorNormalization
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat

/-! # Geometric-point projection comparison

Source: Stacks Project, `sites-cohomology.tex`, Tag 0B56, and
`etale-cohomology.tex`, Tags 07A4 and 0F0F
(blueprint: lem-kun-geometric-point-projection-comparison).

The theorem records the compatibility of the canonical derived projection map with
geometric-stalk evaluation and the constant-section projection map. The vertical maps
are the normalized monoidal comparison and the specified right-adjoint comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- Integer modules in the coefficient universe fixed by the dependency equivalence.
The `ULift` is the existing integer-module encoding of ordinary abelian groups.
Source: Stacks Tag 0F0F (blueprint: lem-kun-geometric-point-projection-comparison). -/
abbrev GeometricPointIntegerModule := ModuleCat.{u + 1} (ULift.{u + 1} ℤ)
/-- The normalized strong monoidal stalk structure supplied by the point equivalence.
Source: Stacks Tags 04JQ and 0F0F
(blueprint: lem-kun-geometric-point-projection-comparison). -/
noncomputable instance geometricPointDerivedStalkMonoidal
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    (geometricPointStalk Ω).mapDerivedCategory.Monoidal :=
  (Classical.choice (nonempty_geometricPointDerivedConstantsData Ω)).derivedStalkMonoidal

/-- The specified derived constant-germ unit is invertible by the point equivalence.
Source: Stacks Tags 04JQ and 0F0F
(blueprint: lem-kun-geometric-point-projection-comparison). -/
noncomputable instance geometricPointDerivedSectionsStalkUnitIsIso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    IsIso ((geometricPointSectionsStalkAdjunction Ω).mapDerivedCategoryAdjunction.unit) :=
  (Classical.choice (nonempty_geometricPointDerivedConstantsData Ω)).derivedUnitIsIso

/-- The canonical pullback-of-constants comparison, transported through the canonical
identifications of the left derived exact functors with their termwise derived functors.
Its component is the node's `γ`, expressed in the normalization of the projection maps.
Source: Stacks Tags 07A4, 07A6 and 0F0F
(blueprint: lem-kun-geometric-point-projection-comparison). -/
noncomputable def geometricPointProjectionCoefficientIso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}}
    (h : Z ⟶ Spec (.of Ω)) :
    (geometricPointConstants Ω).mapDerivedCategory ⋙
        (upperStar GeometricPointIntegerModule h).leftDerivedFunctor ≅
      (constantSheaf Z.smallEtaleTopology GeometricPointIntegerModule).leftDerivedFunctor :=
  Functor.isoWhiskerLeft (geometricPointConstants Ω).mapDerivedCategory
      (upperStar GeometricPointIntegerModule h).leftDerivedFunctorIsoMapDerivedCategory ≪≫
    geometricPointSectionsConstantsIso Ω h ≪≫
    (constantSheaf Z.smallEtaleTopology
      GeometricPointIntegerModule).leftDerivedFunctorIsoMapDerivedCategory.symm

/-- The equation of the geometric-point projection comparison square, written with
abstract functors so that specialization does not expand tensor localization objects.
`F,H` are inverse/direct image, `S,K` are stalk/constants, and `L,R` are constants/sections.
`β,γ,unit` are the fixed right-adjoint comparison, coefficient comparison and germ unit.
`P,p` are the two projection transformations. The conclusion quantifies over every `E,M`;
its left side is the top arrow followed by the right vertical map, and its right side
is the normalized monoidal left vertical map followed by the bottom projection arrow.
This definition assumes no commutativity, invertibility or projection-formula property.
Source: Stacks Tags 0B56 and 0F0F
(blueprint: lem-kun-geometric-point-projection-comparison). -/
noncomputable def GeometricPointProjectionSquare
    {C : Type u₁} {A : Type u₂} {D : Type u₃}
    [Category.{v₁} C] [Category.{v₂} A] [Category.{v₃} D]
    [MonoidalCategory C] [MonoidalCategory A] [MonoidalCategory D]
    (F : A ⥤ C) (H : C ⥤ A) (S : A ⥤ D) [S.Monoidal]
    (K : D ⥤ A) (L : D ⥤ C) (R : C ⥤ D)
    (β : H ⋙ S ≅ R) (γ : K ⋙ F ≅ L) (unit : 𝟭 D ⟶ K ⋙ S) [IsIso unit]
    (P : H ⋙ curriedTensor A ⟶
      (Functor.postcompose₂.obj H).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj F).obj (curriedTensor C)))
    (p : R ⋙ curriedTensor D ⟶
      (Functor.postcompose₂.obj R).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj L).obj (curriedTensor C))) : Prop :=
  ∀ (E : C) (M : D),
    S.map ((P.app E).app (K.obj M)) ≫
        β.hom.app (E ⊗ F.obj (K.obj M)) ≫ R.map (E ◁ γ.hom.app M) =
      Functor.OplaxMonoidal.δ S (H.obj E) (K.obj M) ≫
        (S.obj (H.obj E) ◁ inv (unit.app M)) ≫
        (β.hom.app E ▷ M) ≫ (p.app E).app M

/-- Formal projection-mate square, followed by cancellation of the coefficient unit.
Source: Stacks 0B56 and 07A6
(blueprint: lem-kun-geometric-point-projection-comparison). -/
private theorem projection_square
    {C : Type u₁} {A : Type u₂} {D : Type u₃}
    [Category.{v₁} C] [Category.{v₂} A] [Category.{v₃} D]
    [MonoidalCategory C] [MonoidalCategory A] [MonoidalCategory D]
    {F : A ⥤ C} {H : C ⥤ A} {S : A ⥤ D} [S.Monoidal]
    {K : D ⥤ A} {L : D ⥤ C} {R : C ⥤ D}
    (a : F ⊣ H) (b : L ⊣ R)
    (φ : (Functor.postcompose₂.obj F).obj (curriedTensor A) ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))
    (ψ : (Functor.postcompose₂.obj L).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj L).obj L).obj (curriedTensor C))
    (β : H ⋙ S ≅ R) (γ : K ⋙ F ≅ L)
    (unit : 𝟭 D ⟶ K ⋙ S) [IsIso unit]
    (σ : S ⋙ L ⟶ F)
    (hσ : PullbackStalkTensorCompatible F S L φ ψ σ)
    (hβ : ∀ E, L.map (β.hom.app E) ≫ b.counit.app E =
      σ.app (H.obj E) ≫ a.counit.app E)
    (hunit : ∀ M, L.map (unit.app M) ≫ σ.app (K.obj M) ≫ γ.hom.app M = 𝟙 _) :
    GeometricPointProjectionSquare F H S K L R β γ unit
      (a.rightAdjointProjectionMap φ) (b.rightAdjointProjectionMap ψ) := by
  intro E M
  have e := a.rightAdjointProjectionMap_mate b φ ψ
    (Functor.OplaxMonoidal.δNatTrans S)
    (Functor.OplaxMonoidal.δNatTrans (𝟭 C)) σ β.hom
    (fun X Y ↦ by
      change L.map (Functor.OplaxMonoidal.δ S X Y) ≫
        (ψ.app (S.obj X)).app (S.obj Y) ≫
          σ.app X ▷ L.obj (S.obj Y) ≫ F.obj X ◁ σ.app Y =
        σ.app (X ⊗ Y) ≫ (φ.app X).app Y ≫ 𝟙 _
      simpa only [Category.comp_id, tensorHom_def, Category.assoc] using hσ X Y)
    hβ E (K.obj M)
  change S.map (((a.rightAdjointProjectionMap φ).app E).app (K.obj M)) ≫
      β.hom.app (E ⊗ F.obj (K.obj M)) ≫ R.map (𝟙 _) =
    Functor.OplaxMonoidal.δ S (H.obj E) (K.obj M) ≫
      (β.hom.app E ▷ S.obj (K.obj M)) ≫
      ((b.rightAdjointProjectionMap ψ).app E).app (S.obj (K.obj M)) ≫
      R.map (E ◁ σ.app (K.obj M)) at e
  simp only [R.map_id, Category.comp_id] at e
  rw [← Category.assoc, e]
  have hui : σ.app (K.obj M) ≫ γ.hom.app M = L.map (inv (unit.app M)) := by
    apply (cancel_epi (L.map (unit.app M))).mp
    simpa only [← L.map_comp, IsIso.hom_inv_id, L.map_id] using hunit M
  have n := ((b.rightAdjointProjectionMap ψ).app E).naturality (inv (unit.app M))
  change (R.obj E ◁ inv (unit.app M)) ≫
      ((b.rightAdjointProjectionMap ψ).app E).app M =
    ((b.rightAdjointProjectionMap ψ).app E).app (S.obj (K.obj M)) ≫
      R.map (E ◁ L.map (inv (unit.app M))) at n
  simp only [Category.assoc]
  rw [← R.map_comp, ← whiskerLeft_comp, hui, ← n, ← whisker_exchange_assoc]
  rfl

/-- Transport the specified counit equation through the canonical left-adjoint isomorphisms.
Source: Stacks 07A6
(blueprint: lem-kun-geometric-point-projection-comparison). -/
private theorem transport_counit
    {C A D : Type*} [Category* C] [Category* A] [Category* D]
    {F F' : A ⥤ C} {H : C ⥤ A} {S : A ⥤ D} {K : D ⥤ A}
    {L L' : D ⥤ C} {R : C ⥤ D}
    (a : F ⊣ H) (b : L ⊣ R) (e : K ⊣ S)
    (i : F ≅ F') (j : L ≅ L') (g : K ⋙ F' ≅ L') (β : H ⋙ S ≅ R)
    (h : ∀ E, g.hom.app (S.obj (H.obj E)) ≫ L'.map (β.hom.app E) ≫
        (b.ofNatIsoLeft j).counit.app E =
      F'.map (e.counit.app (H.obj E)) ≫ (a.ofNatIsoLeft i).counit.app E)
    (E : C) :
    L.map (β.hom.app E) ≫ b.counit.app E =
      (pullbackStalkComparison e (Functor.isoWhiskerLeft K i ≪≫ g ≪≫ j.symm)).app
        (H.obj E) ≫ a.counit.app E := by
  simp only [pullbackStalkComparison, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp, Category.assoc]
  have h := h E
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app] at h
  apply (cancel_epi (j.inv.app (S.obj (H.obj E)))).mp
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [← j.inv.naturality_assoc]
  have h' := congrArg (fun f ↦ g.inv.app (S.obj (H.obj E)) ≫ f) h
  simp only [Iso.inv_hom_id_app_assoc] at h'
  rw [← i.inv.naturality_assoc]
  simpa only [Iso.inv_hom_id_app_assoc, Functor.id_obj] using h'

/-- The evaluation comparison on constants satisfies the adjunction triangle identity.
Source: Stacks 07A6 and the normalized point equivalence of 04JQ
(blueprint: lem-kun-geometric-point-projection-comparison). -/
private theorem pullbackStalk_unit
    {C A D : Type*} [Category* C] [Category* A] [Category* D]
    {F : A ⥤ C} {S : A ⥤ D} {K : D ⥤ A} {L : D ⥤ C}
    (a : K ⊣ S) (γ : K ⋙ F ≅ L) (M : D) :
    L.map (a.unit.app M) ≫ (pullbackStalkComparison a γ).app (K.obj M) ≫
        γ.hom.app M = 𝟙 _ := by
  simp only [pullbackStalkComparison, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp, Category.assoc]
  have n := γ.inv.naturality (a.unit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at n
  rw [reassoc_of% n, ← F.map_comp_assoc]
  simpa only [Functor.comp_map, Functor.id_obj, a.left_triangle_components, F.map_id,
    Category.id_comp]
    using γ.inv_hom_id_app M

/-- The canonical geometric-point projection comparison square commutes.
Source: Stacks Tag 0B56, with the canonical-map identification in Tag 0F0F
(blueprint: lem-kun-geometric-point-projection-comparison).

Proof:
1. Define σ : S ⋙ L ⟶ F by the inverse constants comparison followed by F of the
   constant/stalk counit. The pullback tensor-normalization lemma says that σ commutes
   with the canonical tensor comparisons. It is a statement about inverse image and
   evaluation only, independent of both right adjoints and both projection morphisms.
2. Transport the specified counit equation of
   `lem-kun-geometric-point-derived-sections-adjunction` through the canonical exact-functor
   identifications. It becomes L(β_E) followed by the sections counit equals σ_HE followed
   by the image counit. Naturality of the identifications proves this transport equation.
3. Apply `Adjunction.rightAdjointProjectionMap_mate` to the two tensor comparisons, σ,
   the monoidal stalk constraint and β. This gives the projection square with coefficient
   S(K(M)) and the comparison σ_K(M).
4. Naturality of the coefficient comparison and the constant/stalk triangle identity give
   L(unit_M) followed by σ_K(M) and γ_M equal to identity. Cancel the invertible germ unit
   to identify σ_K(M) followed by γ_M with L(unit_M inverse). Finally, naturality of the
   sections projection transformation and tensor interchange give the stated square.
   No horizontal projection morphism is inverted.
-/
theorem geometricPoint_projection_comparison
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}}
    (h : Z ⟶ Spec (.of Ω)) :
    GeometricPointProjectionSquare
      (upperStar GeometricPointIntegerModule h).leftDerivedFunctor
      (lowerStar GeometricPointIntegerModule h).rightDerivedFunctor
      (geometricPointStalk Ω).mapDerivedCategory
      (geometricPointConstants Ω).mapDerivedCategory
      (constantSheaf Z.smallEtaleTopology GeometricPointIntegerModule).leftDerivedFunctor
      (rightDerivedGlobalSections GeometricPointIntegerModule Z)
      (geometricPointDerivedSectionsIso Ω h)
      (geometricPointProjectionCoefficientIso Ω h)
      (geometricPointSectionsStalkAdjunction Ω).mapDerivedCategoryAdjunction.unit
      (rightDerivedLowerStarProjectionMap GeometricPointIntegerModule h)
      ((derivedConstantGlobalSectionsAdjunction
        GeometricPointIntegerModule Z).rightAdjointProjectionMap
          (constantSheaf Z.smallEtaleTopology
            GeometricPointIntegerModule).leftDerivedTensorComparison) := by
  exact projection_square
    (F := (upperStar GeometricPointIntegerModule h).leftDerivedFunctor)
    (H := (lowerStar GeometricPointIntegerModule h).rightDerivedFunctor)
    (S := (geometricPointStalk Ω).mapDerivedCategory)
    (K := (geometricPointConstants Ω).mapDerivedCategory)
    (L := (constantSheaf Z.smallEtaleTopology GeometricPointIntegerModule).leftDerivedFunctor)
    (R := rightDerivedGlobalSections GeometricPointIntegerModule Z)
    (derivedUpperStarLowerStarAdjunction GeometricPointIntegerModule h)
    (derivedConstantGlobalSectionsAdjunction GeometricPointIntegerModule Z)
    (leftDerivedUpperStarTensorComparison GeometricPointIntegerModule h)
    (constantSheaf Z.smallEtaleTopology GeometricPointIntegerModule).leftDerivedTensorComparison
    (geometricPointDerivedSectionsIso Ω h) (geometricPointProjectionCoefficientIso Ω h)
    (geometricPointSectionsStalkAdjunction Ω).mapDerivedCategoryAdjunction.unit
    (geometricPointPullbackStalkComparison Ω h)
    (geometricPoint_pullbackStalk_tensor Ω h)
    (transport_counit
      (derivedUpperStarLowerStarAdjunction GeometricPointIntegerModule h)
      (derivedConstantGlobalSectionsAdjunction GeometricPointIntegerModule Z)
      (geometricPointSectionsStalkAdjunction Ω).mapDerivedCategoryAdjunction
      (upperStar GeometricPointIntegerModule h).leftDerivedFunctorIsoMapDerivedCategory
      (constantSheaf Z.smallEtaleTopology
        GeometricPointIntegerModule).leftDerivedFunctorIsoMapDerivedCategory
      (geometricPointSectionsConstantsIso Ω h)
      (geometricPointDerivedSectionsIso Ω h)
      (geometricPoint_derivedSections_adjunction Ω h).1)
    (pullbackStalk_unit
      (geometricPointSectionsStalkAdjunction Ω).mapDerivedCategoryAdjunction
      (geometricPointProjectionCoefficientIso Ω h))

end AlgebraicGeometry.Etale
