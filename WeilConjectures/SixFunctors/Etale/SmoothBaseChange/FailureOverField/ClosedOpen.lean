/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.TransitionComposition
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity
public import WeilConjectures.SixFunctors.Finite.BaseChange
public import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Supported
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison

/-!
# The closed–open step of the detection of a failure of base change

TODO
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace CategoryTheory.Adjunction

section Mates

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj' : L' ⊣ R')

/-- The mate of a square of left adjoints, precomposed with the image of the unit, is the unit
followed by the square. -/
lemma map_unit_comp_mate_app (G : C ⥤ C') (G' : D ⥤ D') (θ : G ⋙ L' ⟶ L ⋙ G') (K : C) :
    G.map (adj.unit.app K) ≫ adj'.unit.app (G.obj (R.obj (L.obj K))) ≫
        R'.map (θ.app (R.obj (L.obj K))) ≫ R'.map (G'.map (adj.counit.app (L.obj K))) =
      adj'.unit.app (G.obj K) ≫ R'.map (θ.app K) := by
  have h₁ := adj'.unit.naturality (G.map (adj.unit.app K))
  have h₂ := θ.naturality (adj.unit.app K)
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at h₁ h₂
  rw [reassoc_of% h₁, ← R'.map_comp_assoc, h₂, R'.map_comp_assoc, ← R'.map_comp, ← G'.map_comp,
    adj.left_triangle_components, G'.map_id, R'.map_id, Category.comp_id]

/-- The form of `CategoryTheory.Adjunction.map_unit_comp_mate_app` in which the square and the
counit are grouped under `R'`. -/
lemma map_unit_comp_unit_app_comp_map (S : C ⥤ C') (S' : D ⥤ D') (s : S ⋙ L' ⟶ L ⋙ S')
    (F : C) :
    S.map (adj.unit.app F) ≫ adj'.unit.app (S.obj (R.obj (L.obj F))) ≫
        R'.map (s.app (R.obj (L.obj F)) ≫ S'.map (adj.counit.app (L.obj F))) =
      adj'.unit.app (S.obj F) ≫ R'.map (s.app F) := by
  rw [R'.map_comp]
  exact adj.map_unit_comp_mate_app adj' S S' s F

/-- The mate `S (R N) ⟶ R' (S' N)` of `L' (S (R N)) ≅ S' (L (R N)) ⟶ S' N` is natural in `N`. -/
lemma unit_app_comp_map_naturality (S : C ⥤ C') (S' : D ⥤ D') (s : S ⋙ L' ⟶ L ⋙ S')
    {N N' : D} (f : N ⟶ N') :
    (adj'.unit.app (S.obj (R.obj N)) ≫ R'.map (s.app (R.obj N) ≫ S'.map (adj.counit.app N))) ≫
        R'.map (S'.map f) =
      S.map (R.map f) ≫
        adj'.unit.app (S.obj (R.obj N')) ≫ R'.map (s.app (R.obj N') ≫ S'.map (adj.counit.app N')) := by
  have h₁ := adj'.unit.naturality (S.map (R.map f))
  have h₂ := s.naturality (R.map f)
  have h₃ := adj.counit.naturality f
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at h₁ h₂ h₃
  rw [reassoc_of% h₁, Category.assoc, ← R'.map_comp, ← R'.map_comp]
  congr 2
  rw [reassoc_of% h₂, ← S'.map_comp, h₃, S'.map_comp, Category.assoc]

end Mates

section Plus

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] (adj : L ⊣ R)

/-- If the counit of `adj` is an isomorphism, so is the counit of the induced adjunction on the
bounded below homotopy categories. -/
lemma isIso_mapHomotopyCategoryPlus_counit_app (hε : ∀ Y, IsIso (adj.counit.app Y))
    (K : HomotopyCategory.Plus D) : IsIso (adj.mapHomotopyCategoryPlus.counit.app K) := by
  suffices IsIso ((HomotopyCategory.Plus.ι D).map (adj.mapHomotopyCategoryPlus.counit.app K)) from
    isIso_of_fully_faithful (HomotopyCategory.Plus.ι D) _
  have key : ∀ Y : HomotopyCategory D (ComplexShape.up ℤ),
      IsIso ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app Y) := by
    intro Y
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    rw [mapHomotopyCategory_counit_app_quotient]
    have : ∀ n, IsIso (((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app X).f n) :=
      fun n ↦ by rw [mapHomologicalComplex_counit_app_f]; exact hε _
    have : IsIso ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app X) :=
      HomologicalComplex.Hom.isIso_of_components _
    exact Functor.map_isIso (HomotopyCategory.quotient D (ComplexShape.up ℤ)) _
  rw [ι_map_mapHomotopyCategoryPlus_counit_app]
  exact key K.obj

variable [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- If the counit of `adj` is an isomorphism, the counit of the bounded below derived adjunction
is an isomorphism at the image of a complex on which the unit of the right derived functor of
`R` is an isomorphism. -/
lemma isIso_derivedPlus_counit_app_Qh_obj (hε : ∀ Y, IsIso (adj.counit.app Y))
    (M : HomotopyCategory.Plus D) [IsIso (R.rightDerivedFunctorPlusUnit.app M)] :
    IsIso (adj.derivedPlus.counit.app (DerivedCategory.Plus.Qh.obj M)) := by
  have h := adj.derivedPlus_counit_app_fac M
  have := adj.isIso_mapHomotopyCategoryPlus_counit_app hε M
  have : IsIso (L.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnit.app M) ≫
      adj.derivedPlus.counit.app (DerivedCategory.Plus.Qh.obj M)) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_left (L.mapDerivedCategoryPlus.map
    (R.rightDerivedFunctorPlusUnit.app M)) _

end Plus

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

section DerivedUnit

/-- The transition map `Rh_* K ⟶ R(a ≫ h)_* (a^* K)` is `Rh_*` of the unit of `a^* ⊣ Ra_*`
followed by the composition isomorphism `Rh_* ∘ Ra_* ≅ R(a ≫ h)_*`. -/
lemma Etale.lowerStarPlusTransition_eq_unit {X Y Y' : Scheme.{u}} (a : Y' ⟶ Y) (h : Y ⟶ X)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    haveI : ((a)_*[ModuleCat.{u + 1} Λ]).PreservesInjectiveObjects :=
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
        (Etale.upperStarLowerStarAdjunction _ a)
    Etale.lowerStarPlusTransition Λ a h (a ≫ h) rfl K =
      R+((h)_*[ModuleCat.{u + 1} Λ]).map
          ((Etale.derivedUpperStarLowerStarAdjunctionPlus _ a).unit.app K) ≫
        (Functor.rightDerivedFunctorPlusCompIso' ((a)_*[ModuleCat.{u + 1} Λ])
          ((h)_*[ModuleCat.{u + 1} Λ]) (Etale.lowerStarComp _ a h)).hom.app
          (D+((a)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  have : ((a)_*[ModuleCat.{u + 1} Λ]).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction _ a)
  have hu := Etale.derivedPlus_unit_comp_upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a h
    (a ≫ h) rfl (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)
  simp only [Etale.lowerStarPlusTransition,
    Etale.derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus, eqToIso_refl, Iso.refl_trans]
  change _ ≫ R+((a ≫ h)_*[ModuleCat.{u + 1} Λ]).map
    ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a h (a ≫ h) rfl).hom.app _ ≫ _) = _
  rw [Functor.map_comp, reassoc_of% hu]
  have hn := (Functor.rightDerivedFunctorPlusCompIso' ((a)_*[ModuleCat.{u + 1} Λ])
          ((h)_*[ModuleCat.{u + 1} Λ]) (Etale.lowerStarComp _ a h)).hom.naturality
    (D+((a)^*[ModuleCat.{u + 1} Λ]).map
      ((Etale.upperStarLowerStarAdjunction _ h).derivedPlus.counit.app K))
  simp only [Functor.comp_map] at hn
  erw [← hn]
  rw [← Functor.map_comp_assoc]
  have hu2 := (Etale.upperStarLowerStarAdjunction _ a).derivedPlus.unit.naturality
    ((Etale.upperStarLowerStarAdjunction _ h).derivedPlus.counit.app K)
  simp only [Functor.comp_map, Functor.id_map] at hu2
  erw [← hu2]
  rw [Functor.map_comp, ← Category.assoc, ← Category.assoc,
    (Etale.upperStarLowerStarAdjunction _ h).derivedPlus.right_triangle_components K,
    Category.id_comp]
  rfl

/-- The derived base-change map of a square, precomposed with the pullback of the unit, is the
unit followed by the pullback comparison of the square. -/
lemma Etale.upperStar_map_unit_comp_baseChange_app {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D+((g)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus _ f).unit.app K) ≫
      (Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app (D+((f)^*[ModuleCat.{u + 1} Λ]).obj K) =
    (Etale.derivedUpperStarLowerStarAdjunctionPlus _ f').unit.app
        (D+((g)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      R+((f')_*[ModuleCat.{u + 1} Λ]).map
        ((Etale.pullbackSquareComparison _ sq).hom.app K) := by
  rw [Etale.baseChange_app, Etale.baseChangeUnitStep_app, Etale.baseChangeSquareStep_hom_app,
    Etale.baseChangeCounitStep_app]
  exact Adjunction.map_unit_comp_mate_app (Etale.derivedUpperStarLowerStarAdjunctionPlus _ f)
    (Etale.derivedUpperStarLowerStarAdjunctionPlus _ f') D+((g)^*[ModuleCat.{u + 1} Λ])
    D+((g')^*[ModuleCat.{u + 1} Λ]) (Etale.pullbackSquareComparison _ sq).hom K

/-- The comparison `k_* N [0] ⟶ R k_* (N [0])`: the map adjoint to
`k^* (k_* N [0]) ≅ (k^* k_* N)[0] ⟶ N[0]`, the second map being the counit of `k^* ⊣ k_*`. -/
noncomputable def Etale.singleLowerStarComparison {T' T₁ : Scheme.{u}} (k : T₁ ⟶ T')
    (N : Sheaf T₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj (((k)_*[ModuleCat.{u + 1} Λ]).obj N) ⟶
      R+((k)_*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj N) :=
  (Etale.derivedUpperStarLowerStarAdjunctionPlus _ k).unit.app _ ≫
    R+((k)_*[ModuleCat.{u + 1} Λ]).map
      ((((k)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((Etale.upperStarLowerStarAdjunction _ k).counit.app N))

/-- The comparison `AlgebraicGeometry.Etale.singleLowerStarComparison` is natural. -/
lemma Etale.singleLowerStarComparison_naturality {T' T₁ : Scheme.{u}} (k : T₁ ⟶ T')
    {N N' : Sheaf T₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : N ⟶ N') :
    Etale.singleLowerStarComparison Λ k N ≫
        R+((k)_*[ModuleCat.{u + 1} Λ]).map ((DerivedCategory.Plus.singleFunctor _ 0).map f) =
      (DerivedCategory.Plus.singleFunctor _ 0).map (((k)_*[ModuleCat.{u + 1} Λ]).map f) ≫
        Etale.singleLowerStarComparison Λ k N' :=
  Adjunction.unit_app_comp_map_naturality (Etale.upperStarLowerStarAdjunction _ k)
    (Etale.derivedUpperStarLowerStarAdjunctionPlus _ k) (DerivedCategory.Plus.singleFunctor _ 0)
    (DerivedCategory.Plus.singleFunctor _ 0)
    (((k)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom f

/-- The unit of `k^* ⊣ k_*` placed in degree `0`, followed by the comparison
`AlgebraicGeometry.Etale.singleLowerStarComparison`, is the unit of the derived adjunction. -/
lemma Etale.singleFunctor_map_unit_comp_singleLowerStarComparison {T' T₁ : Scheme.{u}}
    (k : T₁ ⟶ T') (F : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (DerivedCategory.Plus.singleFunctor _ 0).map
        ((Etale.upperStarLowerStarAdjunction _ k).unit.app F) ≫
      Etale.singleLowerStarComparison Λ k (((k)^*[ModuleCat.{u + 1} Λ]).obj F) =
    (Etale.derivedUpperStarLowerStarAdjunctionPlus _ k).unit.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      R+((k)_*[ModuleCat.{u + 1} Λ]).map
        ((((k)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F) :=
  Adjunction.map_unit_comp_unit_app_comp_map (Etale.upperStarLowerStarAdjunction _ k)
    (Etale.derivedUpperStarLowerStarAdjunctionPlus _ k) (DerivedCategory.Plus.singleFunctor _ 0)
    (DerivedCategory.Plus.singleFunctor _ 0)
    (((k)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom F

end DerivedUnit

end AlgebraicGeometry
