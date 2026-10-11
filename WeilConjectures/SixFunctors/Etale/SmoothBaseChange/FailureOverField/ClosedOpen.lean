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

universe v u

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

section StalkRange

namespace CategoryTheory

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] {R : Type*} [Ring R]

/-- Let `Φ` be an exact functor to modules. If the map induced on the cokernels of `f` and `f'`
by a commutative square is a monomorphism, then an element whose image under `Φ β` lies in the
range of `Φ f'` already lies in the range of `Φ f`. -/
lemma mem_range_of_mono_cokernelMap (Φ : 𝒜 ⥤ ModuleCat.{v} R) [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ] {A B A' B' : 𝒜} (f : A ⟶ B) (f' : A' ⟶ B') (α : A ⟶ A')
    (β : B ⟶ B') (w : f ≫ β = α ≫ f') [Mono (cokernel.map f f' α β w)] (x : Φ.obj B)
    (hx : (Φ.map β).hom x ∈ Set.range (Φ.map f').hom) : x ∈ Set.range (Φ.map f).hom := by
  have hex := ((ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).exact_of_g_is_cokernel
    (cokernelIsCokernel f)).map Φ
  rw [ShortComplex.moduleCat_exact_iff] at hex
  refine hex x ?_
  have hm : Function.Injective (Φ.map (cokernel.map f f' α β w)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  apply hm
  obtain ⟨y, hy⟩ := hx
  rw [map_zero]
  change (Φ.map (cokernel.π f) ≫ Φ.map (cokernel.map f f' α β w)).hom x = 0
  rw [← Φ.map_comp, cokernel.π_desc, Φ.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, ← hy]
  change (Φ.map f' ≫ Φ.map (cokernel.π f')).hom y = 0
  rw [← Φ.map_comp, cokernel.condition, Φ.map_zero]
  rfl

/-- Let `τ : S ⟶ T` be a natural transformation between functors to an additive category,
with `T` additive, and let `Φ` be an additive functor to modules. An element of
`Φ (T (G₁ ⊞ G₂))` whose two components are in the ranges of `Φ τ` is in the range of
`Φ τ`. -/
lemma mem_range_of_biprod {𝒞 : Type*} [Category* 𝒞] [Preadditive 𝒞] [HasBinaryBiproducts 𝒞]
    {ℬ : Type*} [Category* ℬ] [Preadditive ℬ] (Φ : ℬ ⥤ ModuleCat.{v} R) [Φ.Additive]
    {S T : 𝒞 ⥤ ℬ} [T.Additive] (τ : S ⟶ T) {G₁ G₂ : 𝒞} (x : Φ.obj (T.obj (G₁ ⊞ G₂)))
    (h₁ : (Φ.map (T.map biprod.fst)).hom x ∈ Set.range (Φ.map (τ.app G₁)).hom)
    (h₂ : (Φ.map (T.map biprod.snd)).hom x ∈ Set.range (Φ.map (τ.app G₂)).hom) :
    x ∈ Set.range (Φ.map (τ.app (G₁ ⊞ G₂))).hom := by
  obtain ⟨y₁, hy₁⟩ := h₁
  obtain ⟨y₂, hy₂⟩ := h₂
  refine ⟨(Φ.map (S.map biprod.inl)).hom y₁ + (Φ.map (S.map biprod.inr)).hom y₂, ?_⟩
  have e (G : 𝒞) (b : G ⟶ G₁ ⊞ G₂) (y : Φ.obj (S.obj G)) :
      (Φ.map (τ.app (G₁ ⊞ G₂))).hom ((Φ.map (S.map b)).hom y) =
        (Φ.map (T.map b)).hom ((Φ.map (τ.app G)).hom y) := by
    rw [← ModuleCat.comp_apply, ← Φ.map_comp, τ.naturality, Φ.map_comp, ModuleCat.comp_apply]
  rw [map_add, e, e, hy₁, hy₂, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← Φ.map_comp,
    ← Φ.map_comp, ← T.map_comp, ← T.map_comp, ← LinearMap.add_apply, ← ModuleCat.hom_add,
    ← Φ.map_add, ← T.map_add, biprod.total, T.map_id, Φ.map_id]
  rfl

end CategoryTheory

end StalkRange

section MonoRightDerived

open Pretriangulated

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- Let `c : K ⟶ L` be a morphism of the bounded below derived category which is an
isomorphism on `H^i` for `i < n` and a monomorphism on `H^n`. Then `R⁺F(c)` is a monomorphism
on `H^n`: the cone of `c` is cohomologically `≥ n`, hence so is its image under `R⁺F`. -/
theorem mono_homologyFunctor_map_rightDerivedFunctorPlus_map (F : C ⥤ D) [F.Additive]
    {K L : DerivedCategory.Plus C} (c : K ⟶ L) (n : ℤ)
    (h₁ : ∀ i < n, IsIso ((DerivedCategory.Plus.homologyFunctor C i).map c))
    (h₂ : Mono ((DerivedCategory.Plus.homologyFunctor C n).map c)) :
    Mono ((DerivedCategory.Plus.homologyFunctor D n).map (F.rightDerivedFunctorPlus.map c)) := by
  obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle c
  have hZ : ∀ i < n, IsZero ((DerivedCategory.Plus.homologyFunctor C i).obj Z) := by
    intro i hi
    have hg : (DerivedCategory.Plus.homologyFunctor C i).map g = 0 := by
      have := h₁ i hi
      exact ((DerivedCategory.Plus.homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff
        _ hT i).1 (inferInstanceAs (Epi ((DerivedCategory.Plus.homologyFunctor C i).map c)))
    have hδ : (DerivedCategory.Plus.homologyFunctor C 0).homologySequenceδ
        (Triangle.mk c g δ) i (i + 1) rfl = 0 := by
      refine ((DerivedCategory.Plus.homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff
        _ hT i (i + 1) rfl).1 ?_
      change Mono ((DerivedCategory.Plus.homologyFunctor C (i + 1)).map c)
      rcases (show i + 1 < n ∨ i + 1 = n by lia) with h | h
      · have := h₁ _ h
        infer_instance
      · rw [h]
        exact h₂
    exact ((DerivedCategory.Plus.homologyFunctor C 0).homologySequence_exact₃ _ hT i (i + 1)
      rfl).isZero_of_both_zeros hg hδ
  have : Z.IsGE n := by
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
    exact hZ
  have hT' := F.rightDerivedFunctorPlus.map_distinguished _ hT
  have hz := F.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE Z n
    (show n - 1 < n by lia)
  refine ((DerivedCategory.Plus.homologyFunctor D 0).homologySequence_mono_shift_map_mor₁_iff
    _ hT' (n - 1) n (by lia)).2 ?_
  exact hz.eq_of_src _ _

end CategoryTheory.Functor

end MonoRightDerived

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

section Pushforward

variable {X S T Y T' Y' : Scheme.{u}}

omit [CommRing Λ] in
/-- The naturality of a natural transformation between composites, evaluated at objects, stated
for abstract functors so that its instances are checked syntactically. -/
lemma natTrans_app_comp_map_map_eq {𝒜 ℬ ℬ' 𝒞 : Type*} [Category* 𝒜] [Category* ℬ]
    [Category* ℬ'] [Category* 𝒞] {F₁ : 𝒜 ⥤ ℬ} {F₂ : ℬ ⥤ 𝒞} {G₁ : 𝒜 ⥤ ℬ'} {G₂ : ℬ' ⥤ 𝒞}
    (β : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂) {A A' : 𝒜} (f : A ⟶ A') :
    β.app A ≫ G₂.map (G₁.map f) = F₂.map (F₁.map f) ≫ β.app A' :=
  (β.naturality f).symm

/-- The derived base-change maps over `T` and over `T'` commute with the comparison maps of a
complex `K` on `T` and a complex `L` on `T'` attached to a morphism `ψ : k^* K ⟶ L`. -/
theorem Etale.baseChange_app_comp_pushforward {p : X ⟶ S} {g : T ⟶ S}
    {e : Y ⟶ T} {h : Y ⟶ X} (sq : CommSq e h g p) (k : T' ⟶ T) {e' : Y' ⟶ T'}
    {h' : Y' ⟶ X} (g' : T' ⟶ S) (hg : k ≫ g = g') (sq' : CommSq e' h' g' p) (a : Y' ⟶ Y)
    (wa : a ≫ e = e' ≫ k) (wh : a ≫ h = h') (sqk : CommSq e' a k e)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory.Plus (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (ψ : D+((k)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ L) :
    (Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app K ≫
        R+((h)_*[ModuleCat.{u + 1} Λ]).map
          (D+((e)^*[ModuleCat.{u + 1} Λ]).map
              ((Etale.derivedUpperStarLowerStarAdjunctionPlus _ k).unit.app K) ≫
            D+((e)^*[ModuleCat.{u + 1} Λ]).map (R+((k)_*[ModuleCat.{u + 1} Λ]).map ψ) ≫
            (Etale.baseChange (ModuleCat.{u + 1} Λ) sqk).app L) ≫
        (Etale.lowerStarPlusCompIso Λ a h h' wh).hom.app (D+((e')^*[ModuleCat.{u + 1} Λ]).obj L) =
      D+((p)^*[ModuleCat.{u + 1} Λ]).map
          (R+((g)_*[ModuleCat.{u + 1} Λ]).map
              ((Etale.derivedUpperStarLowerStarAdjunctionPlus _ k).unit.app K ≫
                R+((k)_*[ModuleCat.{u + 1} Λ]).map ψ) ≫
            (Etale.lowerStarPlusCompIso Λ k g g' hg).hom.app L) ≫
        (Etale.baseChange (ModuleCat.{u + 1} Λ) sq').app L := by
  rw [← Etale.targetTransitionPlus_comp_map Λ e h k a e' h' wa wh sqk K L ψ,
    reassoc_of% (Etale.baseChange_app_comp_targetTransitionPlus Λ sq k g' hg sq' a wa wh K),
    natTrans_app_comp_map_map_eq (Etale.baseChange (ModuleCat.{u + 1} Λ) sq'),
    ← Functor.map_comp_assoc, Etale.lowerStarPlusTransition_comp_map]

/-- The comparison `k_* N[0] ⟶ Rk_*(N[0])` is the unit followed by `Rk_*` of the counit. -/
lemma Etale.singleLowerStarComparison_eq (k : T' ⟶ T)
    (N : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Etale.singleLowerStarComparison Λ k N =
      (Etale.derivedUpperStarLowerStarAdjunctionPlus _ k).unit.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (((k)_*[ModuleCat.{u + 1} Λ]).obj N)) ≫
        R+((k)_*[ModuleCat.{u + 1} Λ]).map
          ((((k)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
            (DerivedCategory.Plus.singleFunctor _ 0).map
              ((Etale.upperStarLowerStarAdjunction _ k).counit.app N)) := rfl

/-- `e^*` of the comparison `k_* N[0] ⟶ Rk_*(N[0])` is `e^*` of the unit followed by `e^*` of
`Rk_*` of the counit. -/
lemma Etale.upperStar_map_singleLowerStarComparison (e : Y ⟶ T) (k : T' ⟶ T)
    (N : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    D+((e)^*[ModuleCat.{u + 1} Λ]).map (Etale.singleLowerStarComparison Λ k N) =
      D+((e)^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.derivedUpperStarLowerStarAdjunctionPlus _ k).unit.app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj (((k)_*[ModuleCat.{u + 1} Λ]).obj N))) ≫
        D+((e)^*[ModuleCat.{u + 1} Λ]).map (R+((k)_*[ModuleCat.{u + 1} Λ]).map
          ((((k)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
            (DerivedCategory.Plus.singleFunctor _ 0).map
              ((Etale.upperStarLowerStarAdjunction _ k).counit.app N))) :=
  CategoryTheory.Functor.map_comp _ _ _

/-- The base-change maps commute with the comparisons of the sources and of the targets for a
sheaf pushed forward along `k : T' ⟶ T`. -/
theorem Etale.baseChangeHomologyMap_comp_pushforward {p : X ⟶ S} {g : T ⟶ S}
    {e : Y ⟶ T} {h : Y ⟶ X} (sq : IsPullback e h g p) (k : T' ⟶ T) {e' : Y' ⟶ T'}
    {h' : Y' ⟶ X} (g' : T' ⟶ S) (hg : k ≫ g = g') (sq' : IsPullback e' h' g' p) (a : Y' ⟶ Y)
    (wa : a ≫ e = e' ≫ k) (wh : a ≫ h = h') (sqk : CommSq e' a k e) (q : ℤ)
    (N : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Etale.baseChangeHomologyMap Λ sq q (((k)_*[ModuleCat.{u + 1} Λ]).obj N) ≫
        (DerivedCategory.Plus.homologyFunctor _ q).map
          (R+((h)_*[ModuleCat.{u + 1} Λ]).map
              (D+((e)^*[ModuleCat.{u + 1} Λ]).map (Etale.singleLowerStarComparison Λ k N) ≫
                (Etale.baseChange (ModuleCat.{u + 1} Λ) sqk).app
                  ((DerivedCategory.Plus.singleFunctor _ 0).obj N)) ≫
            (Etale.lowerStarPlusCompIso Λ a h h' wh).hom.app
              (D+((e')^*[ModuleCat.{u + 1} Λ]).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj N))) =
      (DerivedCategory.Plus.homologyFunctor _ q).map
          (D+((p)^*[ModuleCat.{u + 1} Λ]).map
            (R+((g)_*[ModuleCat.{u + 1} Λ]).map (Etale.singleLowerStarComparison Λ k N) ≫
              (Etale.lowerStarPlusCompIso Λ k g g' hg).hom.app
                ((DerivedCategory.Plus.singleFunctor _ 0).obj N))) ≫
        Etale.baseChangeHomologyMap Λ sq' q N := by
  rw [Etale.baseChangeHomologyMap_eq_homologyFunctor_map,
    Etale.baseChangeHomologyMap_eq_homologyFunctor_map, ← Functor.map_comp, ← Functor.map_comp,
    Etale.upperStar_map_singleLowerStarComparison, Category.assoc,
    Etale.singleLowerStarComparison_eq]
  congr 1
  refine Eq.trans ?_ (Eq.trans (Etale.baseChange_app_comp_pushforward Λ sq.toCommSq k g' hg
    sq'.toCommSq a wa wh sqk
    ((DerivedCategory.Plus.singleFunctor _ 0).obj (((k)_*[ModuleCat.{u + 1} Λ]).obj N))
    ((DerivedCategory.Plus.singleFunctor _ 0).obj N)
    ((((k)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((Etale.upperStarLowerStarAdjunction _ k).counit.app N))) ?_) <;> rfl


/-- The image of a morphism of sheaves under the target functor of the base-change map. -/
lemma Etale.baseChangeTargetFunctor_map (e : Y ⟶ T) (h : Y ⟶ X) (q : ℤ)
    {A B : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : A ⟶ B) :
    (Etale.baseChangeTargetFunctor Λ e h q).map f =
      (DerivedCategory.Plus.homologyFunctor _ q).map (R+((h)_*[ModuleCat.{u + 1} Λ]).map
        (D+((e)^*[ModuleCat.{u + 1} Λ]).map ((DerivedCategory.Plus.singleFunctor _ 0).map f))) :=
  rfl

omit [CommRing Λ] in
/-- The naturality of a natural transformation out of a composite, stated for abstract functors
so that its instances are checked syntactically. -/
lemma natTrans_app_comp_map {𝒜 ℬ 𝒞 : Type*} [Category* 𝒜] [Category* ℬ] [Category* 𝒞]
    {F₁ : 𝒜 ⥤ ℬ} {F₂ : ℬ ⥤ 𝒞} {G : 𝒜 ⥤ 𝒞} (β : F₁ ⋙ F₂ ⟶ G) {A A' : 𝒜} (f : A ⟶ A') :
    β.app A ≫ G.map f = F₂.map (F₁.map f) ≫ β.app A' :=
  (β.naturality f).symm

omit [CommRing Λ] in
/-- Two equal composites stay equal under a functor. -/
lemma map_comp_map_eq_map_comp_map {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (G : 𝒞 ⥤ 𝒟)
    {A B B' C : 𝒞} {f₁ : A ⟶ B} {f₂ : B ⟶ C} {g₁ : A ⟶ B'} {g₂ : B' ⟶ C}
    (w : f₁ ≫ f₂ = g₁ ≫ g₂) : G.map f₁ ≫ G.map f₂ = G.map g₁ ≫ G.map g₂ := by
  rw [← G.map_comp, w, G.map_comp]

/-- The comparison of the targets for a pushed forward sheaf is natural in the sheaf. -/
lemma Etale.targetPushforward_naturality (e : Y ⟶ T) (h : Y ⟶ X) (k : T' ⟶ T) (a : Y' ⟶ Y)
    (e' : Y' ⟶ T') (h' : Y' ⟶ X) (wh : a ≫ h = h') (sqk : CommSq e' a k e) (q : ℤ)
    {N N' : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : N ⟶ N') :
    (DerivedCategory.Plus.homologyFunctor _ q).map (R+((h)_*[ModuleCat.{u + 1} Λ]).map
        (D+((e)^*[ModuleCat.{u + 1} Λ]).map ((DerivedCategory.Plus.singleFunctor _ 0).map
          (((k)_*[ModuleCat.{u + 1} Λ]).map φ)))) ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
          (R+((h)_*[ModuleCat.{u + 1} Λ]).map
              (D+((e)^*[ModuleCat.{u + 1} Λ]).map (Etale.singleLowerStarComparison Λ k N') ≫
                (Etale.baseChange (ModuleCat.{u + 1} Λ) sqk).app
                  ((DerivedCategory.Plus.singleFunctor _ 0).obj N')) ≫
            (Etale.lowerStarPlusCompIso Λ a h h' wh).hom.app
              (D+((e')^*[ModuleCat.{u + 1} Λ]).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj N'))) =
    (DerivedCategory.Plus.homologyFunctor _ q).map
          (R+((h)_*[ModuleCat.{u + 1} Λ]).map
              (D+((e)^*[ModuleCat.{u + 1} Λ]).map (Etale.singleLowerStarComparison Λ k N) ≫
                (Etale.baseChange (ModuleCat.{u + 1} Λ) sqk).app
                  ((DerivedCategory.Plus.singleFunctor _ 0).obj N)) ≫
            (Etale.lowerStarPlusCompIso Λ a h h' wh).hom.app
              (D+((e')^*[ModuleCat.{u + 1} Λ]).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj N))) ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map (R+((h')_*[ModuleCat.{u + 1} Λ]).map
        (D+((e')^*[ModuleCat.{u + 1} Λ]).map ((DerivedCategory.Plus.singleFunctor _ 0).map φ))) := by
  have h₁ := map_comp_map_eq_map_comp_map D+((e)^*[ModuleCat.{u + 1} Λ])
    (Etale.singleLowerStarComparison_naturality Λ k φ).symm
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [Category.assoc, natTrans_app_comp_map (Etale.lowerStarPlusCompIso Λ a h h' wh).hom,
    ← Functor.map_comp_assoc (R+((h)_*[ModuleCat.{u + 1} Λ])),
    ← Functor.map_comp_assoc (R+((h)_*[ModuleCat.{u + 1} Λ])), reassoc_of% h₁, Category.assoc,
    natTrans_app_comp_map_map_eq (Etale.baseChange (ModuleCat.{u + 1} Λ) sqk)]

/-- The comparison of the targets for a pushed forward sheaf is an isomorphism when the
comparison `k_* N[0] ⟶ Rk_*(N[0])` and the derived base-change map at `N[0]` are. -/
lemma Etale.isIso_targetPushforward (e : Y ⟶ T) (h : Y ⟶ X) (k : T' ⟶ T) (a : Y' ⟶ Y)
    (e' : Y' ⟶ T') (h' : Y' ⟶ X) (wh : a ≫ h = h') (sqk : CommSq e' a k e) (q : ℤ)
    (N : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsIso (Etale.singleLowerStarComparison Λ k N)]
    [IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sqk).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj N))] :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
          (R+((h)_*[ModuleCat.{u + 1} Λ]).map
              (D+((e)^*[ModuleCat.{u + 1} Λ]).map (Etale.singleLowerStarComparison Λ k N) ≫
                (Etale.baseChange (ModuleCat.{u + 1} Λ) sqk).app
                  ((DerivedCategory.Plus.singleFunctor _ 0).obj N)) ≫
            (Etale.lowerStarPlusCompIso Λ a h h' wh).hom.app
              (D+((e')^*[ModuleCat.{u + 1} Λ]).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj N)))) :=
  inferInstance

/-- The comparison of the sources for a pushed forward sheaf is an isomorphism when the
comparison `k_* N[0] ⟶ Rk_*(N[0])` is. -/
lemma Etale.isIso_sourcePushforward (p : X ⟶ S) (g : T ⟶ S) (k : T' ⟶ T) (g' : T' ⟶ S)
    (hg : k ≫ g = g') (q : ℤ) (N : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsIso (Etale.singleLowerStarComparison Λ k N)] :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
          (D+((p)^*[ModuleCat.{u + 1} Λ]).map
            (R+((g)_*[ModuleCat.{u + 1} Λ]).map (Etale.singleLowerStarComparison Λ k N) ≫
              (Etale.lowerStarPlusCompIso Λ k g g' hg).hom.app
                ((DerivedCategory.Plus.singleFunctor _ 0).obj N)))) :=
  inferInstance

/-- The comparison of the targets for a pushed forward sheaf is a monomorphism when the
comparison `k_* N[0] ⟶ Rk_*(N[0])` is an isomorphism and the derived base-change map at `N[0]`
is an isomorphism in degrees `< q` and a monomorphism in degree `q`. -/
lemma Etale.mono_targetPushforward (e : Y ⟶ T) (h : Y ⟶ X) (k : T' ⟶ T) (a : Y' ⟶ Y)
    (e' : Y' ⟶ T') (h' : Y' ⟶ X) (wh : a ≫ h = h') (sqk : CommSq e' a k e) (q : ℤ)
    (N : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsIso (Etale.singleLowerStarComparison Λ k N)]
    (h₁ : ∀ i < q, IsIso ((DerivedCategory.Plus.homologyFunctor _ i).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) sqk).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj N))))
    (h₂ : Mono ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) sqk).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj N)))) :
    Mono ((DerivedCategory.Plus.homologyFunctor _ q).map
          (R+((h)_*[ModuleCat.{u + 1} Λ]).map
              (D+((e)^*[ModuleCat.{u + 1} Λ]).map (Etale.singleLowerStarComparison Λ k N) ≫
                (Etale.baseChange (ModuleCat.{u + 1} Λ) sqk).app
                  ((DerivedCategory.Plus.singleFunctor _ 0).obj N)) ≫
            (Etale.lowerStarPlusCompIso Λ a h h' wh).hom.app
              (D+((e')^*[ModuleCat.{u + 1} Λ]).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj N)))) := by
  rw [Functor.map_comp]
  have : Mono ((DerivedCategory.Plus.homologyFunctor _ q).map
      (R+((h)_*[ModuleCat.{u + 1} Λ]).map
        (D+((e)^*[ModuleCat.{u + 1} Λ]).map (Etale.singleLowerStarComparison Λ k N) ≫
          (Etale.baseChange (ModuleCat.{u + 1} Λ) sqk).app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj N)))) := by
    refine Functor.mono_homologyFunctor_map_rightDerivedFunctorPlus_map _ _ q (fun i hi ↦ ?_) ?_
    · have := h₁ i hi
      rw [Functor.map_comp]
      infer_instance
    · rw [Functor.map_comp]
      infer_instance
  infer_instance

/-- **The transition maps of the targets compose**, on the degree-`q` homology at a sheaf placed
in degree `0`: the transition from `T` to `T₂`, followed by the transition from `T₂` to `T₁`
(conjugated by the identifications of pulled back sheaves placed in degree `0`), is the
transition from `T` to `T₁`. -/
lemma Etale.baseChangeTargetTransition_comp_eq {X T Y T₂ Y₂ T₁ Y₁ : Scheme.{u}} {e : Y ⟶ T}
    {h : Y ⟶ X} (q : ℤ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (f₂ : T₂ ⟶ T)
    {e₂ : Y₂ ⟶ T₂} {h₂ : Y₂ ⟶ X} (a₂ : Y₂ ⟶ Y) (wa₂ : a₂ ≫ e = e₂ ≫ f₂) (wh₂ : a₂ ≫ h = h₂)
    (i : T₁ ⟶ T₂) {e₁ : Y₁ ⟶ T₁} {h₁ : Y₁ ⟶ X} (a₁ : Y₁ ⟶ Y) (wa₁ : a₁ ≫ e = e₁ ≫ i ≫ f₂)
    (wh₁ : a₁ ≫ h = h₁) (a' : Y₁ ⟶ Y₂) (wa' : a' ≫ e₂ = e₁ ≫ i) (wh' : a' ≫ h₂ = h₁)
    (ha : a' ≫ a₂ = a₁) :
    Etale.baseChangeTargetTransition Λ e h q f₂ a₂ e₂ h₂ wa₂ wh₂ F ≫
        (DerivedCategory.Plus.homologyFunctor _ q).map
          (R+((h₂)_*[ModuleCat.{u + 1} Λ]).map (D+((e₂)^*[ModuleCat.{u + 1} Λ]).map
            ((((f₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv.app F)) ≫
          Etale.targetTransitionPlus Λ e₂ h₂ i a' e₁ h₁ wa' wh'
            (D+((f₂)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
          R+((h₁)_*[ModuleCat.{u + 1} Λ]).map (D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
            ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) i f₂ (i ≫ f₂) rfl).inv.app
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
              ((((i ≫ f₂))^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
                F ≫ 𝟙 ((DerivedCategory.Plus.singleFunctor _ 0).obj
                  (((i ≫ f₂)^*[ModuleCat.{u + 1} Λ]).obj F))))) =
      Etale.baseChangeTargetTransition Λ e h q (i ≫ f₂) a₁ e₁ h₁ wa₁ wh₁ F := by
  rw [Etale.baseChangeTargetTransition_eq, Etale.baseChangeTargetTransition_eq,
    ← Functor.map_comp]
  congr 1
  have hT := Etale.targetTransitionPlus_comp Λ e h f₂ a₂ e₂ h₂ wa₂ wh₂ i a' e₁ h₁ wa' wh'
    (i ≫ f₂) a₁ ha rfl wa₁ wh₁ ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  simp only [Category.assoc, Functor.map_comp] at hT ⊢
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← Functor.map_comp_assoc (R+((h₂)_*[ModuleCat.{u + 1} Λ])),
    ← Functor.map_comp (D+((e₂)^*[ModuleCat.{u + 1} Λ])), Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% hT]

omit [CommRing Λ] in
/-- Two equal composites stay equal under a functor, followed by a common morphism. -/
lemma map_comp_map_comp_map_comp_eq {ℬ 𝒞 𝒟 : Type*} [Category* ℬ] [Category* 𝒞] [Category* 𝒟]
    (R : ℬ ⥤ 𝒞) (G : 𝒞 ⥤ 𝒟) {A B C B' : 𝒞} {L : ℬ} {E : 𝒟} {a : A ⟶ B} {b : B ⟶ C}
    {c : C ⟶ R.obj L} {x : A ⟶ B'} {y : B' ⟶ R.obj L} (d : (R ⋙ G).obj L ⟶ E) (w : x ≫ y = a ≫ b ≫ c) :
    G.map a ≫ G.map b ≫ G.map c ≫ d = G.map x ≫ G.map y ≫ d := by
  simpa using congrArg (fun f ↦ G.map f ≫ d) w.symm

/-- **Decomposition of the transition maps along a morphism `i : T₁ ⟶ T₂`.** The transition map
from `T` to `T₁` is the transition map from `T` to `T₂`, followed by `R^q h₂_* e₂⁻¹` of a map
`β : f₂^* F ⟶ i_*((i ≫ f₂)^* F)` whose adjoint is an isomorphism, followed by the comparison of
the targets for the pushed forward sheaf `i_*((i ≫ f₂)^* F)`. -/
theorem Etale.exists_baseChangeTargetTransition_comp_eq {X T Y T₂ Y₂ T₁ Y₁ : Scheme.{u}}
    {e : Y ⟶ T} {h : Y ⟶ X} (q : ℤ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (f₂ : T₂ ⟶ T) {e₂ : Y₂ ⟶ T₂} {h₂ : Y₂ ⟶ X} (a₂ : Y₂ ⟶ Y) (wa₂ : a₂ ≫ e = e₂ ≫ f₂)
    (wh₂ : a₂ ≫ h = h₂) (i : T₁ ⟶ T₂) {e₁ : Y₁ ⟶ T₁} {h₁ : Y₁ ⟶ X} (a₁ : Y₁ ⟶ Y)
    (wa₁ : a₁ ≫ e = e₁ ≫ i ≫ f₂) (wh₁ : a₁ ≫ h = h₁) (a' : Y₁ ⟶ Y₂) (wa' : a' ≫ e₂ = e₁ ≫ i)
    (wh' : a' ≫ h₂ = h₁) (ha : a' ≫ a₂ = a₁) (sqk : CommSq e₁ a' i e₂) :
    ∃ β : ((f₂)^*[ModuleCat.{u + 1} Λ]).obj F ⟶
        ((i)_*[ModuleCat.{u + 1} Λ]).obj (((i ≫ f₂)^*[ModuleCat.{u + 1} Λ]).obj F),
      IsIso (((i)^*[ModuleCat.{u + 1} Λ]).map β ≫
        (Etale.upperStarLowerStarAdjunction _ i).counit.app _) ∧
      Etale.baseChangeTargetTransition Λ e h q f₂ a₂ e₂ h₂ wa₂ wh₂ F ≫
          (Etale.baseChangeTargetFunctor Λ e₂ h₂ q).map β ≫
          (DerivedCategory.Plus.homologyFunctor _ q).map
            (R+((h₂)_*[ModuleCat.{u + 1} Λ]).map
                (D+((e₂)^*[ModuleCat.{u + 1} Λ]).map (Etale.singleLowerStarComparison Λ i
                    (((i ≫ f₂)^*[ModuleCat.{u + 1} Λ]).obj F)) ≫
                  (Etale.baseChange (ModuleCat.{u + 1} Λ) sqk).app
                    ((DerivedCategory.Plus.singleFunctor _ 0).obj
                      (((i ≫ f₂)^*[ModuleCat.{u + 1} Λ]).obj F))) ≫
              (Etale.lowerStarPlusCompIso Λ a' h₂ h₁ wh').hom.app
                (D+((e₁)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
                  (((i ≫ f₂)^*[ModuleCat.{u + 1} Λ]).obj F)))) =
        Etale.baseChangeTargetTransition Λ e h q (i ≫ f₂) a₁ e₁ h₁ wa₁ wh₁ F := by
  obtain ⟨φ, hφ⟩ := (Etale.bijective_comp_singleLowerStarComparison Λ i
    (((i ≫ f₂)^*[ModuleCat.{u + 1} Λ]).obj F) (((f₂)^*[ModuleCat.{u + 1} Λ]).obj F)).2
    ((((f₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv.app F ≫
      (Etale.derivedUpperStarLowerStarAdjunctionPlus _ i).unit.app
        (D+((f₂)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
      (R+((i)_*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) i f₂ (i ≫ f₂) rfl).inv.app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
          ((((i ≫ f₂))^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
            𝟙 ((DerivedCategory.Plus.singleFunctor _ 0).obj (((i ≫ f₂)^*[ModuleCat.{u + 1} Λ]).obj F)) :
          D+((i)^*[ModuleCat.{u + 1} Λ]).obj (D+((f₂)^*[ModuleCat.{u + 1} Λ]).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ⟶ _) :
        _ ⟶ _))
  obtain ⟨β, rfl⟩ := (DerivedCategory.Plus.singleFunctor _ 0).map_surjective φ
  simp only at hφ
  refine ⟨β, ?_, ?_⟩
  · have h₁ := Etale.singleFunctor_map_comp_singleLowerStarComparison Λ i
      (((i ≫ f₂)^*[ModuleCat.{u + 1} Λ]).obj F) β
    have hn := (Etale.derivedUpperStarLowerStarAdjunctionPlus _ i).unit.naturality
      ((((f₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv.app F)
    simp only [Functor.id_map, Functor.comp_map] at hn
    rw [h₁, reassoc_of% hn, ← Functor.map_comp] at hφ
    erw [← Adjunction.homEquiv_unit, ← Adjunction.homEquiv_unit] at hφ
    have hφ' := ((Etale.derivedUpperStarLowerStarAdjunctionPlus _ i).homEquiv _ _).injective hφ
    rw [← Iso.app_hom, ← Iso.eq_inv_comp] at hφ'
    have : IsIso ((DerivedCategory.Plus.singleFunctor _ 0).map
        (((i)^*[ModuleCat.{u + 1} Λ]).map β ≫
          (Etale.upperStarLowerStarAdjunction _ i).counit.app _)) := by
      rw [hφ']
      erw [Category.comp_id]
      infer_instance
    exact isIso_of_fully_faithful (DerivedCategory.Plus.singleFunctor _ 0) _
  · rw [← Etale.baseChangeTargetTransition_comp_eq Λ q F f₂ a₂ wa₂ wh₂ i a₁ wa₁ wh₁ a' wa' wh' ha]
    congr 1
    rw [Etale.baseChangeTargetFunctor_map, ← Functor.map_comp]
    congr 1
    rw [Etale.targetTransitionPlus_comp_map Λ e₂ h₂ i a' e₁ h₁ wa' wh' sqk,
      ← Functor.map_comp_assoc (R+((h₂)_*[ModuleCat.{u + 1} Λ])),
      ← Functor.map_comp_assoc (R+((h₂)_*[ModuleCat.{u + 1} Λ]))]
    refine Eq.trans ?lhs (Eq.trans (congrArg (fun x ↦ R+((h₂)_*[ModuleCat.{u + 1} Λ]).map x ≫
      (Etale.lowerStarPlusCompIso Λ a' h₂ h₁ wh').hom.app
        (D+((e₁)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (((i ≫ f₂)^*[ModuleCat.{u + 1} Λ]).obj F))))
      (map_comp_map_comp_map_comp_eq R+((i)_*[ModuleCat.{u + 1} Λ]) D+((e₂)^*[ModuleCat.{u + 1} Λ])
        (A := (DerivedCategory.Plus.singleFunctor _ 0).obj (((f₂)^*[ModuleCat.{u + 1} Λ]).obj F))
        (B := ?oB) (C := ?oC) (B' := ?oB') (L := ?oL)
        (E := R+((a')_*[ModuleCat.{u + 1} Λ]).obj (D+((e₁)^*[ModuleCat.{u + 1} Λ]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (((i ≫ f₂)^*[ModuleCat.{u + 1} Λ]).obj F))))
        (a := ?ca) (b := ?cb) (c := ?cc) (x := ?cx) (y := ?cy) ?dd ?hwφ).symm) ?rhs)
    case lhs => rfl
    case rhs => rfl
    case hwφ => exact hφ

/-- A morphism `G ⟶ j_* N₁ ⊞ i_* N₂` along complementary open and closed immersions is a
monomorphism as soon as its two adjoint components `j^* G ⟶ N₁` and `i^* G ⟶ N₂` are. -/
lemma Etale.mono_biprod_lift {T' V Z : Scheme.{u}} (j : V ⟶ T') [IsOpenImmersion j]
    (i : Z ⟶ T') [IsClosedImmersion i] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {G : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {N₁ : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {N₂ : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (β₁ : G ⟶ ((j)_*[ModuleCat.{u + 1} Λ]).obj N₁) (β₂ : G ⟶ ((i)_*[ModuleCat.{u + 1} Λ]).obj N₂)
    [Mono (((j)^*[ModuleCat.{u + 1} Λ]).map β₁ ≫
      (Etale.upperStarLowerStarAdjunction _ j).counit.app N₁)]
    [Mono (((i)^*[ModuleCat.{u + 1} Λ]).map β₂ ≫
      (Etale.upperStarLowerStarAdjunction _ i).counit.app N₂)] :
    Mono (biprod.lift β₁ β₂) := by
  have h₁ : kernel.ι (biprod.lift β₁ β₂) ≫ β₁ = 0 := by
    have := kernel.condition (biprod.lift β₁ β₂) =≫ biprod.fst
    rwa [Category.assoc, biprod.lift_fst, zero_comp] at this
  have h₂ : kernel.ι (biprod.lift β₁ β₂) ≫ β₂ = 0 := by
    have := kernel.condition (biprod.lift β₁ β₂) =≫ biprod.snd
    rwa [Category.assoc, biprod.lift_snd, zero_comp] at this
  refine Preadditive.mono_of_kernel_zero (IsZero.eq_of_src ?_ _ _)
  refine Etale.isZero_of_isZero_upperStar i hij ?_ ?_
  · refine IsZero.of_mono_eq_zero (((j)^*[ModuleCat.{u + 1} Λ]).map (kernel.ι _)) ?_
    rw [← cancel_mono (((j)^*[ModuleCat.{u + 1} Λ]).map β₁ ≫
      (Etale.upperStarLowerStarAdjunction _ j).counit.app N₁), ← Category.assoc,
      ← Functor.map_comp, h₁, Functor.map_zero, zero_comp, zero_comp]
  · refine IsZero.of_mono_eq_zero (((i)^*[ModuleCat.{u + 1} Λ]).map (kernel.ι _)) ?_
    rw [← cancel_mono (((i)^*[ModuleCat.{u + 1} Λ]).map β₂ ≫
      (Etale.upperStarLowerStarAdjunction _ i).counit.app N₂), ← Category.assoc,
      ← Functor.map_comp, h₂, Functor.map_zero, zero_comp, zero_comp]


section Summands

variable {X S T Y T₁ Y₁ : Scheme.{u}}

omit [CommRing Λ] in
/-- On modules: if `b` sends `y` outside the range of `bc₂`, and `bc₂` and `bc₁` are related by
isomorphisms `τ` and `σ`, then `b ≫ τ` sends `y` outside the range of `bc₁`. -/
lemma not_mem_range_of_isIso_comm {R : Type*} [Ring R] {M₂ M₂' S₂ S₁ M₁ : ModuleCat R}
    (b : M₂ ⟶ M₂') (τ : M₂' ⟶ M₁) (bc₂ : S₂ ⟶ M₂') (σ : S₂ ⟶ S₁) (bc₁ : S₁ ⟶ M₁)
    [IsIso τ] [IsIso σ] (w : bc₂ ≫ τ = σ ≫ bc₁) (y : M₂) (hB : b.hom y ∉ Set.range bc₂.hom) :
    τ.hom (b.hom y) ∉ Set.range bc₁.hom := by
  rintro ⟨s, hs⟩
  apply hB
  refine ⟨(inv σ).hom s, ((ConcreteCategory.isIso_iff_bijective τ).1 inferInstance).1 ?_⟩
  rw [← hs, ← ModuleCat.comp_apply, w, ModuleCat.comp_apply, ← ModuleCat.comp_apply (inv σ),
    IsIso.inv_hom_id, ModuleCat.id_apply]

variable {X S T Y T₁ Y₁ : Scheme.{u}}

/-- **The closed summand.** For a finite `k : T₁ ⟶ T` and a square over `T₁` obtained by base
change, if the image of `y` under `R^q h_* e⁻¹ β` is not in the image of the base-change map for
`k_* N`, then its image under the comparison of the targets is not in the image of the
base-change map over `T₁` for `N`. -/
theorem Etale.not_mem_range_of_isFinite {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
    (sq : IsPullback e h g p) (k : T₁ ⟶ T) [IsFinite k] {e₁ : Y₁ ⟶ T₁} {h₁ : Y₁ ⟶ X}
    (g₁ : T₁ ⟶ S) (hg : k ≫ g = g₁) (sq₁ : IsPullback e₁ h₁ g₁ p) (a : Y₁ ⟶ Y)
    (wa : a ≫ e = e₁ ≫ k) (wh : a ≫ h = h₁) (sqk : IsPullback e₁ a k e) (q : ℤ)
    {A : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {N : Sheaf T₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (β : A ⟶ ((k)_*[ModuleCat.{u + 1} Λ]).obj N) (x : X)
    (y : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj A) : ModuleCat.{u + 1} Λ))
    (hy : ((X.uliftPointSmallEtale x).sheafFiber.map
        ((Etale.baseChangeTargetFunctor Λ e h q).map β)).hom y ∉
      Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.baseChangeHomologyMap Λ sq q (((k)_*[ModuleCat.{u + 1} Λ]).obj N))).hom) :
    ((X.uliftPointSmallEtale x).sheafFiber.map
        ((DerivedCategory.Plus.homologyFunctor _ q).map
          (R+((h)_*[ModuleCat.{u + 1} Λ]).map
              (D+((e)^*[ModuleCat.{u + 1} Λ]).map (Etale.singleLowerStarComparison Λ k N) ≫
                (Etale.baseChange (ModuleCat.{u + 1} Λ) sqk.toCommSq).app
                  ((DerivedCategory.Plus.singleFunctor _ 0).obj N)) ≫
            (Etale.lowerStarPlusCompIso Λ a h h₁ wh).hom.app
              (D+((e₁)^*[ModuleCat.{u + 1} Λ]).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj N))))).hom
        (((X.uliftPointSmallEtale x).sheafFiber.map
          ((Etale.baseChangeTargetFunctor Λ e h q).map β)).hom y) ∉
      Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.baseChangeHomologyMap Λ sq₁ q N)).hom := by
  have := Etale.isIso_singleLowerStarComparison_of_isFinite Λ k N
  have : IsIso (Etale.baseChange (ModuleCat.{u + 1} Λ) sqk.toCommSq) := by
    rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
    exact Etale.IsBaseChangeIso.isIso _ _ _ sqk
  have hτ := Etale.isIso_targetPushforward Λ e h k a e₁ h₁ wh sqk.toCommSq q N
  have hσ := Etale.isIso_sourcePushforward Λ p g k g₁ hg q N
  have w := congrArg (fun φ ↦ (X.uliftPointSmallEtale x).sheafFiber.map φ)
    (Etale.baseChangeHomologyMap_comp_pushforward Λ sq k g₁ hg sq₁ a wa wh sqk.toCommSq q N)
  rw [(X.uliftPointSmallEtale x).sheafFiber.map_comp,
    (X.uliftPointSmallEtale x).sheafFiber.map_comp] at w
  exact not_mem_range_of_isIso_comm _ _ _ _ _ w y hy

omit [CommRing Λ] in
/-- On modules: if `b ≫ jι` sends `y` outside the range of `bcJ`, `jι ≫ τJ = τ ≫ ι₁` with `τJ`
injective and `bc₁ ≫ ι₁ = 0`, then `b ≫ τ` sends `y` outside the range of `bc₁`. -/
lemma not_mem_range_of_mono_comm {R : Type*} [Ring R] {M₂ M₂' M₁ M₁' J₂ S₁ SJ : ModuleCat R}
    (b : M₂ ⟶ M₂') (τ : M₂' ⟶ M₁) (ι₁ : M₁ ⟶ M₁') (jι : M₂' ⟶ J₂) (τJ : J₂ ⟶ M₁')
    (bc₁ : S₁ ⟶ M₁) (bcJ : SJ ⟶ J₂) [Mono τJ] (wn : jι ≫ τJ = τ ≫ ι₁) (hz : bc₁ ≫ ι₁ = 0)
    (y : M₂) (hA : jι.hom (b.hom y) ∉ Set.range bcJ.hom) :
    τ.hom (b.hom y) ∉ Set.range bc₁.hom := by
  rintro ⟨s, hs⟩
  apply hA
  refine ⟨0, ?_⟩
  rw [map_zero]
  symm
  apply (ModuleCat.mono_iff_injective τJ).1 inferInstance
  rw [map_zero, ← ModuleCat.comp_apply, wn, ModuleCat.comp_apply, ← hs, ← ModuleCat.comp_apply,
    hz]
  rfl

/-- **The open summand.** For a quasi-compact quasi-separated `j : T₁ ⟶ T` such that the
base-change maps of the squares along `j` over `e` are isomorphisms in degrees `< q`, if the
image of `y` under `R^q h_* e⁻¹ (β ≫ j_* ι)`, `ι : N ⟶ J` an injective envelope, is not in the
image of the base-change map for `j_* J`, then the image of `y` under the comparison of the
targets is not in the image of the base-change map over `T₁` for `N`. -/
theorem Etale.not_mem_range_of_baseChangeProperty {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T}
    {h : Y ⟶ X} (sq : IsPullback e h g p) (j : T₁ ⟶ T) [QuasiCompact j] [QuasiSeparated j]
    {e₁ : Y₁ ⟶ T₁} {h₁ : Y₁ ⟶ X} (g₁ : T₁ ⟶ S) (hg : j ≫ g = g₁) (sq₁ : IsPullback e₁ h₁ g₁ p)
    (a : Y₁ ⟶ Y) (wh : a ≫ h = h₁) (sqk : IsPullback e₁ a j e) (q : ℤ) (hq : 1 ≤ q)
    (hbc : ∀ i < q, Etale.BaseChangeProperty Λ e i)
    {A : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {N : Sheaf T₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (β : A ⟶ ((j)_*[ModuleCat.{u + 1} Λ]).obj N) (x : X)
    (y : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj A) : ModuleCat.{u + 1} Λ))
    (hy : ((X.uliftPointSmallEtale x).sheafFiber.map
        ((Etale.baseChangeTargetFunctor Λ e h q).map
          (((j)_*[ModuleCat.{u + 1} Λ]).map (Injective.ι N)))).hom
        (((X.uliftPointSmallEtale x).sheafFiber.map
          ((Etale.baseChangeTargetFunctor Λ e h q).map β)).hom y) ∉
      Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.baseChangeHomologyMap Λ sq q
          (((j)_*[ModuleCat.{u + 1} Λ]).obj (Injective.under N)))).hom) :
    ((X.uliftPointSmallEtale x).sheafFiber.map
        ((DerivedCategory.Plus.homologyFunctor _ q).map
          (R+((h)_*[ModuleCat.{u + 1} Λ]).map
              (D+((e)^*[ModuleCat.{u + 1} Λ]).map (Etale.singleLowerStarComparison Λ j N) ≫
                (Etale.baseChange (ModuleCat.{u + 1} Λ) sqk.toCommSq).app
                  ((DerivedCategory.Plus.singleFunctor _ 0).obj N)) ≫
            (Etale.lowerStarPlusCompIso Λ a h h₁ wh).hom.app
              (D+((e₁)^*[ModuleCat.{u + 1} Λ]).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj N))))).hom
        (((X.uliftPointSmallEtale x).sheafFiber.map
          ((Etale.baseChangeTargetFunctor Λ e h q).map β)).hom y) ∉
      Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.baseChangeHomologyMap Λ sq₁ q N)).hom := by
  have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1, u}
  have := Etale.isIso_singleLowerStarComparison_of_injective Λ j (Injective.under N)
  have hm := Etale.mono_targetPushforward Λ e h j a e₁ h₁ wh sqk.toCommSq q (Injective.under N)
    (fun i hi ↦ by
      have := hbc i hi j e₁ a sqk (Injective.under N)
      rwa [Etale.baseChangeHomologyMap_eq_homologyFunctor_map] at this)
    (by
      have := Etale.mono_baseChangeHomologyMap Λ q hq (hbc (q - 1) (by lia)) sqk
        (Injective.under N)
      rwa [Etale.baseChangeHomologyMap_eq_homologyFunctor_map] at this)
  have wn := congrArg (fun φ ↦ (X.uliftPointSmallEtale x).sheafFiber.map φ)
    (Etale.targetPushforward_naturality Λ e h j a e₁ h₁ wh sqk.toCommSq q (Injective.ι N))
  rw [(X.uliftPointSmallEtale x).sheafFiber.map_comp,
    (X.uliftPointSmallEtale x).sheafFiber.map_comp] at wn
  have hz := congrArg (fun φ ↦ (X.uliftPointSmallEtale x).sheafFiber.map φ)
    (Etale.baseChangeHomologyMap_comp_map_eq_zero_of_injective Λ sq₁ (q := q) (by lia)
      (Injective.ι N))
  rw [(X.uliftPointSmallEtale x).sheafFiber.map_comp, Functor.map_zero] at hz
  exact not_mem_range_of_mono_comm _ _ _ _ _ _ _ wn hz y hy


end Summands

end Pushforward

end AlgebraicGeometry
