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
  (Etale.derivedUpperStarLowerStarAdjunctionPlus _ k).unit.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (((k)_*[ModuleCat.{u + 1} Λ]).obj N)) ≫
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

section Comparison

/-- The comparison `k_* N [0] ⟶ R k_* (N [0])`, precomposed with a morphism `a : A ⟶ k_* N`
placed in degree `0`, is the derived adjoint of the adjoint of `a`, placed in degree `0`. -/
lemma Etale.singleFunctor_map_comp_singleLowerStarComparison {T' T₁ : Scheme.{u}}
    (k : T₁ ⟶ T') (N : Sheaf T₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {A : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (a : A ⟶ ((k)_*[ModuleCat.{u + 1} Λ]).obj N) :
    (DerivedCategory.Plus.singleFunctor _ 0).map a ≫ Etale.singleLowerStarComparison Λ k N =
      (Etale.derivedUpperStarLowerStarAdjunctionPlus _ k).unit.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj A) ≫
        R+((k)_*[ModuleCat.{u + 1} Λ]).map
          ((((k)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫
            (DerivedCategory.Plus.singleFunctor _ 0).map
              (((k)^*[ModuleCat.{u + 1} Λ]).map a ≫
                (Etale.upperStarLowerStarAdjunction _ k).counit.app N)) := by
  have n₁ := (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) k).unit.naturality
    ((DerivedCategory.Plus.singleFunctor _ 0).map a)
  have n₂ := (((k)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.naturality a
  rw [Functor.id_map, Functor.comp_map] at n₁
  rw [Functor.comp_map, Functor.comp_map] at n₂
  rw [Etale.singleLowerStarComparison, reassoc_of% n₁, ← Functor.map_comp,
    reassoc_of% n₂, Functor.map_comp (DerivedCategory.Plus.singleFunctor _ 0)]

/-- Postcomposition with the comparison `k_* N [0] ⟶ R k_* (N [0])` is bijective on morphisms out
of a sheaf placed in degree `0`: both sides are identified with `Hom(k^* A, N)` by the
adjunctions. -/
lemma Etale.bijective_comp_singleLowerStarComparison {T' T₁ : Scheme.{u}} (k : T₁ ⟶ T')
    (N : Sheaf T₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (A : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Bijective (fun φ : (DerivedCategory.Plus.singleFunctor _ 0).obj A ⟶
        (DerivedCategory.Plus.singleFunctor _ 0).obj (((k)_*[ModuleCat.{u + 1} Λ]).obj N) ↦
      φ ≫ Etale.singleLowerStarComparison Λ k N) := by
  have hs : Function.Bijective (fun a : A ⟶ ((k)_*[ModuleCat.{u + 1} Λ]).obj N ↦
      (DerivedCategory.Plus.singleFunctor (Sheaf T'.smallEtaleTopology
        (ModuleCat.{u + 1} Λ)) 0).map a) :=
    ⟨(DerivedCategory.Plus.singleFunctor _ 0).map_injective,
      (DerivedCategory.Plus.singleFunctor _ 0).map_surjective⟩
  have hiso : Function.Bijective (fun b : (DerivedCategory.Plus.singleFunctor _ 0).obj
        (((k)^*[ModuleCat.{u + 1} Λ]).obj A) ⟶ (DerivedCategory.Plus.singleFunctor _ 0).obj N ↦
      (((k)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫ b) :=
    ⟨fun _ _ h ↦ (cancel_epi _).1 h, fun c ↦ ⟨(((k)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv.app A ≫ c,
      by simp⟩⟩
  have hs' : Function.Bijective (fun a : ((k)^*[ModuleCat.{u + 1} Λ]).obj A ⟶ N ↦
      (DerivedCategory.Plus.singleFunctor (Sheaf T₁.smallEtaleTopology
        (ModuleCat.{u + 1} Λ)) 0).map a) :=
    ⟨(DerivedCategory.Plus.singleFunctor _ 0).map_injective,
      (DerivedCategory.Plus.singleFunctor _ 0).map_surjective⟩
  have h₁ : (fun a : A ⟶ ((k)_*[ModuleCat.{u + 1} Λ]).obj N ↦
      (DerivedCategory.Plus.singleFunctor _ 0).map a ≫ Etale.singleLowerStarComparison Λ k N) =
      (Etale.derivedUpperStarLowerStarAdjunctionPlus _ k).homEquiv _ _ ∘
        (fun b ↦ (((k)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫
          b) ∘ (fun a ↦ (DerivedCategory.Plus.singleFunctor _ 0).map a) ∘
        ((Etale.upperStarLowerStarAdjunction _ k).homEquiv _ _).symm := by
    funext a
    simp only [Function.comp_apply, Adjunction.homEquiv_unit, Adjunction.homEquiv_counit,
      Etale.singleFunctor_map_comp_singleLowerStarComparison]
  have hb : Function.Bijective (fun a : A ⟶ ((k)_*[ModuleCat.{u + 1} Λ]).obj N ↦
      (DerivedCategory.Plus.singleFunctor _ 0).map a ≫ Etale.singleLowerStarComparison Λ k N) := by
    rw [h₁]
    exact (Equiv.bijective _).comp (hiso.comp (hs'.comp (Equiv.bijective _)))
  exact (Function.Bijective.of_comp_iff _ hs).1 hb

/-- In degree `0`, the comparison `k_* N [0] ⟶ R k_* (N [0])` is an isomorphism, that is,
`R⁰ k_* N = k_* N`: by the Yoneda lemma, since postcomposition with it is bijective on
morphisms out of every sheaf placed in degree `0`, and `H⁰` is bijective on morphisms from an
object `≤ 0` to an object `≥ 0`. -/
lemma Etale.isIso_homologyFunctor_zero_map_singleLowerStarComparison {T' T₁ : Scheme.{u}}
    (k : T₁ ⟶ T') (N : Sheaf T₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ 0).map
      (Etale.singleLowerStarComparison Λ k N)) := by
  have hR : (DerivedCategory.Plus.ι.obj (R+((k)_*[ModuleCat.{u + 1} Λ]).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj N))).IsGE 0 :=
    (DerivedCategory.isGE_iff _ 0).2 fun i hi ↦
      ((k)_*[ModuleCat.{u + 1} Λ]).isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
        ((DerivedCategory.Plus.singleFunctor _ 0).obj N) 0 hi
  have hbij {Y : DerivedCategory.Plus (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      (hY : (DerivedCategory.Plus.ι.obj Y).IsGE 0)
      (A : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      Function.Bijective (fun φ : (DerivedCategory.Plus.singleFunctor _ 0).obj A ⟶ Y ↦
        ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).app A).inv ≫
          (DerivedCategory.Plus.homologyFunctor _ 0).map φ) := by
    exact Function.Bijective.comp (g := fun ψ ↦
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).app A).inv ≫ ψ)
      ⟨fun _ _ h ↦ (cancel_epi _).1 h, fun ψ ↦ ⟨_, Iso.inv_hom_id_assoc _ ψ⟩⟩
      ((DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE 0).comp
        ((Functor.FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).map_bijective _ _))
  refine isIso_of_yoneda_map_bijective _ fun A ↦ ?_
  have h₁ := hbij (Y := (DerivedCategory.Plus.singleFunctor _ 0).obj
    (((k)_*[ModuleCat.{u + 1} Λ]).obj N)) inferInstance A
  have h₂ := hbij hR A
  have hc := Etale.bijective_comp_singleLowerStarComparison Λ k N A
  refine (Function.Bijective.of_comp_iff _ h₁).1 ?_
  convert h₂.comp hc using 1
  funext φ
  simp

/-- The comparison `k_* N [0] ⟶ R k_* (N [0])` is an isomorphism as soon as the higher direct
images `R^q k_* N`, `q > 0`, vanish. -/
lemma Etale.isIso_singleLowerStarComparison {T' T₁ : Scheme.{u}} (k : T₁ ⟶ T')
    (N : Sheaf T₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hN : ∀ q : ℤ, 0 < q → IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      (R+((k)_*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj N)))) :
    IsIso (Etale.singleLowerStarComparison Λ k N) := by
  rw [DerivedCategory.Plus.isIso_iff]
  intro q
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · refine ⟨0, ?_, ?_⟩
    · exact (DerivedCategory.Plus.isZero_homology_of_isGE _ 0 q hq).eq_of_src _ _
    · exact (((k)_*[ModuleCat.{u + 1} Λ]).isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
        ((DerivedCategory.Plus.singleFunctor _ 0).obj N) 0 hq).eq_of_src _ _
  · exact Etale.isIso_homologyFunctor_zero_map_singleLowerStarComparison Λ k N
  · refine ⟨0, ?_, ?_⟩
    · exact (DerivedCategory.Plus.isZero_homology_of_isLE _ 0 q hq).eq_of_src _ _
    · exact (hN q hq).eq_of_src _ _

/-- For an injective sheaf `N`, the comparison `k_* N [0] ⟶ R k_* (N [0])` is an isomorphism. -/
lemma Etale.isIso_singleLowerStarComparison_of_injective {T' T₁ : Scheme.{u}} (k : T₁ ⟶ T')
    (N : Sheaf T₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective N] :
    IsIso (Etale.singleLowerStarComparison Λ k N) :=
  Etale.isIso_singleLowerStarComparison Λ k N fun _ hq ↦
    ((k)_*[ModuleCat.{u + 1} Λ]).isZero_homologyFunctor_rightDerivedFunctorPlus_singleFunctor N
      hq.ne'

/-- For a finite morphism `k`, the comparison `k_* N [0] ⟶ R k_* (N [0])` is an isomorphism:
`k_*` is exact. -/
lemma Etale.isIso_singleLowerStarComparison_of_isFinite {T' T₁ : Scheme.{u}} (k : T₁ ⟶ T')
    [IsFinite k] (N : Sheaf T₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.singleLowerStarComparison Λ k N) :=
  Etale.isIso_singleLowerStarComparison Λ k N fun q hq ↦
    IsZero.of_iso (DerivedCategory.Plus.isZero_homology_of_isLE
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (((k)_*[ModuleCat.{u + 1} Λ]).obj N)) 0 q hq)
      ((DerivedCategory.Plus.homologyFunctor _ q).mapIso
        (((k)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.app _ ≪≫
          (((k)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app N))

end Comparison

section TransitionFormula

/-- The composition isomorphism `Ra_* ⋙ Rh_* ≅ Rh'_*` of derived pushforwards along a
commutative triangle `a ≫ h = h'`. -/
noncomputable def Etale.lowerStarPlusCompIso {X Y Y' : Scheme.{u}} (a : Y' ⟶ Y) (h : Y ⟶ X)
    (h' : Y' ⟶ X) (w : a ≫ h = h') :
    R+((a)_*[ModuleCat.{u + 1} Λ]) ⋙ R+((h)_*[ModuleCat.{u + 1} Λ]) ≅
      R+((h')_*[ModuleCat.{u + 1} Λ]) :=
  Functor.rightDerivedFunctorPlusCompIso' ((a)_*[ModuleCat.{u + 1} Λ])
    ((h)_*[ModuleCat.{u + 1} Λ]) (Etale.lowerStarComp _ a h h' w.symm)

/-- The transition map `Rh_* K ⟶ Rh'_*(a^* K)` followed by `Rh'_*` of a morphism
`ψ : a^* K ⟶ L` is `Rh_*` of the adjoint `K ⟶ Ra_* L` of `ψ`, followed by the composition
isomorphism `Rh_* Ra_* ≅ Rh'_*`. -/
lemma Etale.lowerStarPlusTransition_comp_map {X Y Y' : Scheme.{u}} (a : Y' ⟶ Y) (h : Y ⟶ X)
    (h' : Y' ⟶ X) (w : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (ψ : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ L) :
    Etale.lowerStarPlusTransition Λ a h h' w K ≫ R+((h')_*[ModuleCat.{u + 1} Λ]).map ψ =
      R+((h)_*[ModuleCat.{u + 1} Λ]).map
          ((Etale.derivedUpperStarLowerStarAdjunctionPlus _ a).unit.app K ≫
            R+((a)_*[ModuleCat.{u + 1} Λ]).map ψ) ≫
        (Etale.lowerStarPlusCompIso Λ a h h' w).hom.app L := by
  subst w
  rw [Etale.lowerStarPlusTransition_eq_unit, Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg (R+((h)_*[ModuleCat.{u + 1} Λ]).map
    ((Etale.derivedUpperStarLowerStarAdjunctionPlus _ a).unit.app K) ≫ ·)
    ((Etale.lowerStarPlusCompIso Λ a h (a ≫ h) rfl).hom.naturality ψ).symm

/-- The composite `a^* e^* ≅ (a ≫ e)^* = (e' ≫ k)^* ≅ e'^* k^*` does not depend on the morphism
through which the two composition isomorphisms are taken. -/
lemma Etale.upperStarCompDerivedPlus_inv_app_comp_hom_app_congr {Y' Y T T' : Scheme.{u}}
    (a : Y' ⟶ Y) (e : Y ⟶ T) (e' : Y' ⟶ T') (k : T' ⟶ T) (φ₁ φ₂ : Y' ⟶ T)
    (h₁ : φ₁ = a ≫ e) (h₁' : φ₁ = e' ≫ k) (h₂ : φ₂ = a ≫ e) (h₂' : φ₂ = e' ≫ k)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a e φ₁ h₁).inv.app K ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e' k φ₁ h₁').hom.app K =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a e φ₂ h₂).inv.app K ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e' k φ₂ h₂').hom.app K := by
  subst h₁ h₂
  rfl

/-- The pullback comparison of the square `e' ≫ k = a ≫ e`, written with the composition
isomorphisms through `a ≫ e`. -/
lemma Etale.pullbackSquareComparison_hom_app_eq {T Y T' Y' : Scheme.{u}} (e : Y ⟶ T)
    (k : T' ⟶ T) (a : Y' ⟶ Y) (e' : Y' ⟶ T') (wa : a ≫ e = e' ≫ k)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (sqk : CommSq e' a k e) :
    (Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sqk).hom.app K =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a e (a ≫ e) rfl).inv.app K ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e' k (a ≫ e) wa).hom.app K := by
  rw [Etale.pullbackSquareComparison_eq, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  exact Etale.upperStarCompDerivedPlus_inv_app_comp_hom_app_congr Λ a e e' k _ _ _ _ _ _ K

omit [CommRing Λ] in
/-- An abstract form of the last step of
`AlgebraicGeometry.Etale.targetTransitionPlus_comp_map`, stated for abstract functors so that
its instance at the concrete derived functors is checked syntactically. -/
lemma unit_comp_map_comp_map_eq_of_naturality {𝒞₁ 𝒞₂ 𝒟₁ 𝒟₂ : Type*} [Category* 𝒞₁]
    [Category* 𝒞₂] [Category* 𝒟₁] [Category* 𝒟₂] (E : 𝒟₁ ⥤ 𝒟₂) (Rk : 𝒞₁ ⥤ 𝒟₁)
    (Ra : 𝒞₂ ⥤ 𝒟₂) (E' : 𝒞₁ ⥤ 𝒞₂) (β : Rk ⋙ E ⟶ E' ⋙ Ra) {K₀ : 𝒟₁} {M L : 𝒞₁}
    {P : 𝒞₂} (u : K₀ ⟶ Rk.obj M) (ψ : M ⟶ L) (ua : E.obj K₀ ⟶ Ra.obj P) (c : P ⟶ E'.obj M)
    (hu : E.map u ≫ β.app M = ua ≫ Ra.map c) :
    ua ≫ Ra.map c ≫ Ra.map (E'.map ψ) = E.map u ≫ E.map (Rk.map ψ) ≫ β.app L := by
  have hn := β.naturality ψ
  simp only [Functor.comp_map] at hn
  rw [hn, reassoc_of% hu]

/-- The transition map of the targets of the derived base-change maps along `k : T' ⟶ T`,
followed by `Rh'_* e'^*` of a morphism `ψ : k^* K ⟶ L`, is `Rh_*` of `e^*` of the adjoint
`K ⟶ Rk_* L` of `ψ` followed by the derived base-change map of the square `e' ≫ k = a ≫ e`,
followed by the composition isomorphism `Rh_* Ra_* ≅ Rh'_*`. -/
lemma Etale.targetTransitionPlus_comp_map {X T Y T' Y' : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X)
    (k : T' ⟶ T) (a : Y' ⟶ Y) (e' : Y' ⟶ T') (h' : Y' ⟶ X) (wa : a ≫ e = e' ≫ k)
    (wh : a ≫ h = h') (sqk : CommSq e' a k e)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory.Plus (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (ψ : D+((k)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ L) :
    Etale.targetTransitionPlus Λ e h k a e' h' wa wh K ≫
        R+((h')_*[ModuleCat.{u + 1} Λ]).map (D+((e')^*[ModuleCat.{u + 1} Λ]).map ψ) =
      R+((h)_*[ModuleCat.{u + 1} Λ]).map
          (D+((e)^*[ModuleCat.{u + 1} Λ]).map
              ((Etale.derivedUpperStarLowerStarAdjunctionPlus _ k).unit.app K) ≫
            D+((e)^*[ModuleCat.{u + 1} Λ]).map (R+((k)_*[ModuleCat.{u + 1} Λ]).map ψ) ≫
            (Etale.baseChange (ModuleCat.{u + 1} Λ) sqk).app L) ≫
        (Etale.lowerStarPlusCompIso Λ a h h' wh).hom.app (D+((e')^*[ModuleCat.{u + 1} Λ]).obj L) := by
  have hpsc := Etale.pullbackSquareComparison_hom_app_eq Λ e k a e' wa K sqk
  have hu := Etale.upperStar_map_unit_comp_baseChange_app Λ sqk K
  rw [Etale.targetTransitionPlus, Category.assoc, ← Functor.map_comp, ← hpsc,
    Etale.lowerStarPlusTransition_comp_map]
  congr 2
  rw [Functor.map_comp]
  exact unit_comp_map_comp_map_eq_of_naturality D+((e)^*[ModuleCat.{u + 1} Λ])
    R+((k)_*[ModuleCat.{u + 1} Λ]) R+((a)_*[ModuleCat.{u + 1} Λ]) D+((e')^*[ModuleCat.{u + 1} Λ])
    (Etale.baseChange (ModuleCat.{u + 1} Λ) sqk) _ ψ _ _ hu

end TransitionFormula

end AlgebraicGeometry
