/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientExactClopenData
import WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientOrdinaryClopenLocalization
import WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientSystemClopenLocalization
import WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientSystemBetaLocalization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import all WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearAlphaPullback
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearAlphaRestriction
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.LocalVanishing

/-! # Exact localization of the ambient clopen comparison

Source: Stacks Project, Tags 0F7B, 07A7 and 015F.
(blueprint: lem-sf-ambient-exact-clopen-comparison-localization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v₁ v₂ w₁ w₂ h₁ h₂
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures WeilConjectures.IntegralSystemRealization
namespace AlgebraicGeometry.ProEtale.AmbientClopen

private theorem adjunction_on_complexes
    {C : Type v₁} [Category.{h₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    {D : Type v₂} [Category.{h₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    AdjunctionOnComplexes a a.mapExactDerivedCategory := by
  constructor
  · intro K
    simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_unit_app]
    change (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
      G.mapDerivedCategoryFactors.inv.app _ ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K)) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app _ = _
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    simp
  · intro K
    simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_counit_app]
    rfl

private theorem mate_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₁' : A ⥤ B} {R₁ R₁' : B ⥤ A}
    {L₂ L₂' : C ⥤ D} {R₂ R₂' : D ⥤ C}
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (a : L₁ ⊣ R₁) (a' : L₁' ⊣ R₁') (b : L₂ ⊣ R₂) (b' : L₂' ⊣ R₂')
    (e : L₁ ≅ L₁') (f : L₂ ≅ L₂') (g : G ≅ G') (h : H ≅ H')
    (α : G' ⋙ L₂' ⟶ L₁' ⋙ H') (M : B) :
    (mateEquiv a b (TwoSquare.mk _ _ _ _
      (Functor.whiskerRight g.hom L₂ ≫ Functor.whiskerLeft G' f.hom ≫ α ≫
        Functor.whiskerRight e.inv H' ≫ Functor.whiskerLeft L₁ h.inv))).natTrans.app M ≫
        (conjugateIsoEquiv b b' f.symm).hom.app (H.obj M) ≫ R₂'.map (h.hom.app M) =
      g.hom.app (R₁.obj M) ≫ G'.map ((conjugateIsoEquiv a a' e.symm).hom.app M) ≫
        (mateEquiv a' b' (TwoSquare.mk _ _ _ _ α)).natTrans.app M := by
  let w : TwoSquare G' L₁ L₂ H' := .mk _ _ _ _
    (Functor.whiskerLeft G' f.hom ≫ α ≫ Functor.whiskerRight e.inv H')
  have he : (TwoSquare.mk _ _ _ _ α).whiskerLeft e.inv = w.whiskerRight f.inv := by
    ext X
    simp [w, TwoSquare.whiskerLeft, TwoSquare.whiskerRight]
  have hh := mateEquiv_whiskerTop_conjugateEquiv a a' b b' e.inv f.inv w
    (TwoSquare.mk _ _ _ _ α) he
  have hs := mateEquiv_whiskerTop_whiskerBottom a b w g.hom h.inv
  have ht := congrArg (fun t ↦ t.natTrans.app M) hs
  have hu := congrArg (fun t ↦ t.natTrans.app M) hh
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    TwoSquare.whiskerLeft, TwoSquare.whiskerRight, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj] at ht hu
  dsimp only [w] at ht
  simp only [Category.assoc] at ht
  erw [ht]
  simp only [Category.assoc]
  rw [← (conjugateIsoEquiv b b' f.symm).hom.naturality]
  simp only [Functor.comp_obj, ← R₂.map_comp_assoc,
    Iso.inv_hom_id_app, R₂.map_id, Category.id_comp]
  exact congrArg (fun t ↦ g.hom.app (R₁.obj M) ≫ t) hu.symm

private theorem mate_transport_component
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₁' : A ⥤ B} {R₁ R₁' : B ⥤ A}
    {L₂ L₂' : C ⥤ D} {R₂ R₂' : D ⥤ C}
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (a : L₁ ⊣ R₁) (a' : L₁' ⊣ R₁') (b : L₂ ⊣ R₂) (b' : L₂' ⊣ R₂')
    (e : L₁ ≅ L₁') (f : L₂ ≅ L₂') (g : G ≅ G') (h : H ≅ H')
    (α : G' ⋙ L₂' ⟶ L₁' ⋙ H') (γ : R₁ ⋙ G ⟶ H ⋙ R₂) (M : B)
    (hc : γ.app M ≫ (conjugateIsoEquiv b b' f.symm).hom.app (H.obj M) ≫
        R₂'.map (h.hom.app M) =
      g.hom.app (R₁.obj M) ≫ G'.map ((conjugateIsoEquiv a a' e.symm).hom.app M) ≫
        (mateEquiv a' b' (TwoSquare.mk _ _ _ _ α)).natTrans.app M) :
    γ.app M = (mateEquiv a b (TwoSquare.mk _ _ _ _
      (Functor.whiskerRight g.hom L₂ ≫ Functor.whiskerLeft G' f.hom ≫ α ≫
        Functor.whiskerRight e.inv H' ≫ Functor.whiskerLeft L₁ h.inv))).natTrans.app M := by
  apply (cancel_mono ((conjugateIsoEquiv b b' f.symm).hom.app (H.obj M))).mp
  apply (cancel_mono (R₂'.map (h.hom.app M))).mp
  simpa only [Category.assoc] using hc.trans
    (mate_transport a a' b b' e f g h α M).symm

private theorem mate_transport_formula
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₁' : A ⥤ B} {R₁ R₁' : B ⥤ A}
    {L₂ L₂' : C ⥤ D} {R₂ R₂' : D ⥤ C}
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (a : L₁ ⊣ R₁) (a' : L₁' ⊣ R₁') (b : L₂ ⊣ R₂) (b' : L₂' ⊣ R₂')
    (e : L₁ ≅ L₁') (f : L₂ ≅ L₂') (g : G ≅ G') (h : H ≅ H')
    (α : G' ⋙ L₂' ⟶ L₁' ⋙ H') (γ : R₁ ⋙ G ⟶ H ⋙ R₂) (M : B)
    (hc : γ.app M ≫ (conjugateIsoEquiv b b' f.symm).hom.app (H.obj M) ≫
        R₂'.map (h.hom.app M) =
      g.hom.app (R₁.obj M) ≫ G'.map ((conjugateIsoEquiv a a' e.symm).hom.app M) ≫
        (mateEquiv a' b' (TwoSquare.mk _ _ _ _ α)).natTrans.app M) :
    γ.app M = b.unit.app (G.obj (R₁.obj M)) ≫
      R₂.map ((transportAlpha e f g h α).app (R₁.obj M)) ≫
      R₂.map (H.map (a.counit.app M)) := by
  change γ.app M = b.unit.app _ ≫ R₂.map
    ((Functor.whiskerRight g.hom L₂ ≫ Functor.whiskerLeft G' f.hom ≫ α ≫
      Functor.whiskerRight e.inv H' ≫ Functor.whiskerLeft L₁ h.inv).app _) ≫ _
  rw [mate_transport_component a a' b b' e f g h α γ M hc]
  simp only [mateEquiv_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app, Functor.comp_obj,
    Functor.comp_map, Functor.id_obj, Functor.map_comp, Category.assoc,
    Category.id_comp, Category.comp_id]

private theorem factorsh_hom
    {C : Type v₁} [Category.{h₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    {D : Type v₂} [Category.{h₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  have h₁ : (DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ := rfl
  have h₂ : (DerivedCategory.quotientCompQhIso D).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := rfl
  have h₃ : (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := rfl
  simp only [h₁, h₂, h₃, F.mapDerivedCategory.map_id, Category.id_comp]
  erw [DerivedCategory.Qh.map_id, Category.comp_id, Category.comp_id]

private theorem map_adjunction_exact
    {C : Type v₁} [Category.{h₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    {D : Type v₂} [Category.{h₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).obj X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasKInjectiveResolutions D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R) :
    a.mapDerivedCategoryAdjunction = a.mapExactDerivedCategory := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  apply (cancel_mono (R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
    R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K))).mp
  have h := a.mapDerivedCategoryAdjunction_unit_app_fac
    ((HomotopyCategory.quotient _ _).obj K)
  erw [factorsh_hom L K,
    factorsh_hom R ((L.mapHomologicalComplex (.up ℤ)).obj K),
    Adjunction.mapHomotopyCategory_unit_app_quotient] at h
  exact h.trans ((adjunction_on_complexes a).1 K).symm

private theorem ordinary_open_adjunction_exact
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j =
      (openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} Λ) j).mapExactDerivedCategory :=
  map_adjunction_exact _

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf SemilinearProperOpen.P
  SemilinearProperOpen.J SemilinearProperOpen.R CanonicalBridge.pull CanonicalBridge.shriek
  SemilinearProperOpen.alpha SemilinearProperOpen.adj upperStar lowerStar
  openImmersionLowerShriek upperStarLowerStarAdjunction
  openImmersionLowerShriekUpperStarAdjunction upperStarComp

private theorem unit_map_injective
    {A B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R)
    {X Y : A} [Mono (a.unit.app Y)] {f g : X ⟶ Y}
    (h : L.map f = L.map g) : f = g := by
  apply (cancel_mono (a.unit.app Y)).mp
  calc
    _ = a.unit.app X ≫ R.map (L.map f) := a.unit.naturality f
    _ = a.unit.app X ≫ R.map (L.map g) := by rw [h]
    _ = _ := (a.unit.naturality g).symm

private theorem normalized_unique
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {I : A ⥤ B} {T : B ⥤ A} {P : B ⥤ C} {J : D ⥤ C} {K : C ⥤ D} {S : D ⥤ C}
    (R : A ⥤ D) (η : 𝟭 A ⟶ I ⋙ T) [IsIso η]
    (σ : T ⋙ R ≅ P ⋙ K) (c : K ⊣ S)
    (a b : I ⋙ P ⟶ R ⋙ J)
    (hm : ∀ M, Mono (c.unit.app ((R ⋙ J).obj M)))
    (v : ∀ M, R.obj M ⟶ K.obj (J.obj (R.obj M)))
    (ha : restrictionNormalized R η σ v a)
    (hb : restrictionNormalized R η σ v b) : a = b := by
  apply NatTrans.ext
  funext M
  have := hm M
  apply unit_map_injective c
  apply (cancel_epi (σ.hom.app (I.obj M))).mp
  apply (cancel_epi (R.map (η.app M))).mp
  exact (ha M).trans (hb M).symm

private theorem sheaf_normalized_unique
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] (h : k ≫ p = r ≫ i)
    (a b : openImmersionLowerShriek A i ⋙
      upperStar A p ⟶
        upperStar A r ⋙
          openImmersionLowerShriek A k)
    (ha : sheafNormalized A k r p i h.symm a)
    (hb : sheafNormalized A k r p i h.symm b) :
    a = b := by
  have hu : IsIso (openImmersionLowerShriekUpperStarAdjunction A i).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful
      (L := openImmersionLowerShriek A i) (R := upperStar A i)
      (openImmersionLowerShriekUpperStarAdjunction A i)
  exact normalized_unique (upperStar A r)
    (openImmersionLowerShriekUpperStarAdjunction A i).unit (upperStarCompIso A h.symm)
    (upperStarLowerStarAdjunction A k) a b
    (fun M ↦ mono_upperStarLowerStarAdjunction_unit_app_openImmersionLowerShriek
      k A ((upperStar A r).obj M))
    (fun M ↦ (openImmersionLowerShriekUpperStarAdjunction A k).unit.app
      ((upperStar A r).obj M)) ha hb

private theorem ordinary_normalized_unique
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] (h : k ≫ p = r ≫ i)
    (a b : openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ⋙
      upperStar (ModuleCat.{u + 1} Λ) p ⟶
        upperStar (ModuleCat.{u + 1} Λ) r ⋙
          openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
    (ha : Normalized Λ k r p i h a) (hb : Normalized Λ k r p i h b) : a = b := by
  exact sheaf_normalized_unique (ModuleCat.{u + 1} Λ) k r p i h a b ha hb

private theorem ordinary_beta_localizes
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (b : U' ⟶ X')
    (i : U ⟶ X) (p : X' ⟶ X) [IsOpenImmersion i] [IsOpenImmersion b]
    (sq : IsPullback a b i p) :
    (Functor.isoWhiskerLeft _
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) p)).hom ≫
      localizeSquare _ _ _ _ (beta Λ a b i p sq).hom ≫
      (Functor.isoWhiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) a).symm _).hom =
      (properOpenBeta Λ a b i p sq).hom := by
  rfl

private theorem chosen_exact_adjunction_congr
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (P Q : A ⥤ B) [P.IsRightAdjoint] [Q.IsRightAdjoint]
    [P.Additive] [Q.Additive] [P.leftAdjoint.Additive] [Q.leftAdjoint.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits P.leftAdjoint] [PreservesFiniteColimits P.leftAdjoint]
    [PreservesFiniteLimits Q.leftAdjoint] [PreservesFiniteColimits Q.leftAdjoint]
    (h : P = Q) :
    HEq (Adjunction.ofIsRightAdjoint P).mapExactDerivedCategory
      (Adjunction.ofIsRightAdjoint Q).mapExactDerivedCategory := by
  subst Q
  rfl

private theorem system_open_adjunction_exact
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    HEq (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
      (VaryingRing.moduleJAdj C τ j)) (SemilinearProperOpen.jAdj C τ j) := by
  have := SemilinearProperOpen.openPull_isRightAdjoint C τ j
  have := SemilinearProperOpen.pull_additive C τ j
  have := SemilinearProperOpen.pull_limits C τ j
  have := SemilinearProperOpen.pull_colimits C τ j
  have := SemilinearProperOpen.extension_additive C τ j
  have := SemilinearProperOpen.extension_limits C τ j
  have := SemilinearProperOpen.extension_colimits C τ j
  unfold SemilinearProperOpen.jAdj SemilinearProperOpen.J SemilinearProperOpen.P
    SemilinearProperOpen.ordinaryOpenAdj VaryingRing.moduleJAdj
    SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
  exact chosen_exact_adjunction_congr (VaryingRing.pull C τ j)
    (SemilinearProperOpen.pull C τ j) (SemilinearProperOpen.pull_eq C τ j).symm

private theorem sheaf_projector_restrict
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    (M : Sheaf (Scheme.ProEt.topology X) A) :
    (upperStar A s).map ((sheafProjector A s).app M) =
      (openImmersionLowerShriekUpperStarAdjunction A s).unit.app
        ((upperStar A s).obj M) := by
  let P := upperStar A s
  let a := openImmersionLowerShriekUpperStarAdjunction A s
  have hi : P.map ((clopenIdempotentSheaf A s
      s.isClosedEmbedding.isClosed_range).app M) = 𝟙 _ := by
    let e := upperStarIsoOpenImmersionRestriction A s
    apply (cancel_mono (e.hom.app M)).mp
    erw [e.hom.naturality]
    rw [openImmersionRestriction_map_clopenIdempotentSheaf_app]
    simp only [Category.comp_id, Category.id_comp]
    rfl
  have hu : IsIso (a.unit.app (P.obj M)) := inferInstance
  have ht : a.unit.app (P.obj M) ≫ P.map (a.counit.app M) = 𝟙 _ :=
    a.right_triangle_components M
  have hc : IsIso (P.map (a.counit.app M)) := by
    have : IsIso (a.unit.app (P.obj M) ≫ P.map (a.counit.app M)) := by
      rw [ht]
      infer_instance
    exact IsIso.of_isIso_comp_left (a.unit.app (P.obj M)) _
  apply (cancel_mono (P.map (a.counit.app M))).mp
  have he : ((sheafProjector A s).app M ≫ a.counit.app M) =
      (clopenIdempotentSheaf A s s.isClosedEmbedding.isClosed_range).app M := by
    simp only [sheafProjector, clopenIdempotentSheaf, NatTrans.comp_app,
      Functor.whiskerLeft_app, a, Category.assoc]
  rw [← P.map_comp, he, hi, ht]
  rfl

private theorem left_comp_unit
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} {L' : B ⥤ C} {R' : C ⥤ B}
    {L'' : A ⥤ C} {R'' : C ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (c : L'' ⊣ R'') (η : R' ⋙ R ≅ R'') (M : A) :
    (a.comp b).homEquiv M _ ((Adjunction.leftAdjointCompIso a b c η).hom.app M) ≫
      η.hom.app (L''.obj M) = c.unit.app M := by
  rw [Adjunction.homEquiv_unit, Category.assoc, η.hom.naturality, ← Category.assoc]
  have hu := unit_conjugateEquiv (a.comp b) c
    (Adjunction.leftAdjointCompIso a b c η).inv M
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv] at hu
  rw [hu, Category.assoc, ← R''.map_comp, Iso.inv_hom_id_app, R''.map_id]
  exact Category.comp_id _

private theorem left_comp_unit_explicit
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} {L' : B ⥤ C} {R' : C ⥤ B}
    {L'' : A ⥤ C} {R'' : C ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (c : L'' ⊣ R'') (η : R' ⋙ R ≅ R'') (M : A) :
    a.unit.app M ≫ R.map (b.unit.app (L.obj M)) ≫ η.hom.app (L'.obj (L.obj M)) ≫
      R''.map ((Adjunction.leftAdjointCompIso a b c η).hom.app M) = c.unit.app M := by
  have h := left_comp_unit a b c η M
  rw [Adjunction.homEquiv_unit] at h
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Category.assoc] at h
  have hn := η.hom.naturality ((Adjunction.leftAdjointCompIso a b c η).hom.app M)
  dsimp only [Functor.comp_map] at hn
  rw [hn] at h
  exact h

private theorem left_comp_unit_transported
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} {L' : B ⥤ C} {R' : C ⥤ B}
    {L'' L''' : A ⥤ C} {R'' R''' : C ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (c : L'' ⊣ R'') (d : L''' ⊣ R''')
    (η : R' ⋙ R ≅ R'') (e : R'' ≅ R''') (M : A) :
    a.unit.app M ≫ R.map (b.unit.app (L.obj M)) ≫ η.hom.app (L'.obj (L.obj M)) ≫
      e.hom.app (L'.obj (L.obj M)) ≫
      R'''.map (((Adjunction.leftAdjointCompIso a b c η).hom ≫
        ((c.ofNatIsoRight e).leftAdjointUniq d).hom).app M) = d.unit.app M := by
  have hc := left_comp_unit_explicit a b c η M
  have hd := Adjunction.unit_leftAdjointUniq_hom_app (c.ofNatIsoRight e) d M
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc] at hd
  calc
    _ = (a.unit.app M ≫ R.map (b.unit.app (L.obj M)) ≫
        η.hom.app (L'.obj (L.obj M)) ≫
        R''.map ((Adjunction.leftAdjointCompIso a b c η).hom.app M)) ≫
          e.hom.app (L''.obj M) ≫
          R'''.map (((c.ofNatIsoRight e).leftAdjointUniq d).hom.app M) := by
      simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc,
        e.hom.naturality_assoc]
    _ = c.unit.app M ≫ e.hom.app (L''.obj M) ≫
        R'''.map (((c.ofNatIsoRight e).leftAdjointUniq d).hom.app M) := by rw [hc]
    _ = _ := hd

private theorem left_comp_unit_with_data
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} {L' : B ⥤ C} {R' : C ⥤ B}
    {L'' L''' : A ⥤ C} {R'' R''' : C ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (c : L'' ⊣ R'') (d : L''' ⊣ R''')
    (η : R' ⋙ R ≅ R'') (e : R'' ≅ R''')
    (cc : L ⋙ L' ≅ L'') (cg : L'' ≅ L''') (cf : R''' ≅ R' ⋙ R)
    (hc : cc = Adjunction.leftAdjointCompIso a b c η)
    (hg : cg = (c.ofNatIsoRight e).leftAdjointUniq d)
    (hf : cf = e.symm ≪≫ η.symm) (M : A) :
    a.unit.app M ≫ R.map (b.unit.app (L.obj M)) ≫
      cf.inv.app (L'.obj (L.obj M)) ≫ R'''.map ((cc.hom ≫ cg.hom).app M) =
        d.unit.app M := by
  subst cc
  subst cg
  subst cf
  simpa only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc] using
    left_comp_unit_transported a b c d η e M

private theorem conjugate_inverse_hom
    {A B : Type*} [Category A] [Category B]
    {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : R₁ ≅ R₂) :
    (((conjugateIsoEquiv a b).symm e).symm).inv =
      (conjugateEquiv a b).symm e.hom := rfl

private theorem mate_unit_of_eq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) (δ : TwoSquare R₁ H G R₂)
    (h : mateEquiv a b α = δ) (M : A) :
    b.unit.app (G.obj M) ≫ R₂.map (α.app M) =
      G.map (a.unit.app M) ≫ δ.app (L₁.obj M) := by
  have hm := unit_mateEquiv a b α M
  rw [h] at hm
  exact hm.symm

private theorem sheaf_beta_unit
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (b : U' ⟶ X')
    (i : U ⟶ X) (p : X' ⟶ X) [IsOpenImmersion i] [IsOpenImmersion b]
    (sq : IsPullback a b i p)
    (M : Sheaf (Scheme.ProEt.topology U) A) :
    (openImmersionLowerShriekUpperStarAdjunction A b).unit.app
        ((upperStar A a).obj M) ≫
      (upperStar A b).map ((openImmersionLowerShriekBaseChangeMap A sq.toCommSq).app M) =
    (upperStar A a).map
        ((openImmersionLowerShriekUpperStarAdjunction A i).unit.app M) ≫
      (upperStarCompIso A sq.w).hom.app
        ((openImmersionLowerShriek A i).obj M) := by
  exact mate_unit_of_eq
    (openImmersionLowerShriekUpperStarAdjunction A i)
    (openImmersionLowerShriekUpperStarAdjunction A b)
    (TwoSquare.mk _ _ _ _ (openImmersionLowerShriekBaseChangeMap A sq.toCommSq))
    (TwoSquare.mk _ _ _ _ (upperStarCompIso A sq.w).hom)
    (mateEquiv_openImmersionLowerShriekBaseChangeMap A sq.toCommSq) M

private theorem sheaf_lift_square_unit
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {U P V W Z : Scheme.{u}} (s : U ⟶ P) (b : P ⟶ V) (q : P ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) (k : U ⟶ V) (r : U ⟶ W)
    (hk : s ≫ b = k) (hr : s ≫ q = r) (hb : q ≫ i = b ≫ p)
    (h : k ≫ p = r ≫ i)
    (M : Sheaf (Scheme.ProEt.topology Z) A) :
    (upperStarFactor A hr).hom.app
        ((upperStar A i).obj M) ≫
      (upperStar A s).map
        ((upperStarCompIso A hb).hom.app M) ≫
      (upperStarFactor A hk).inv.app
        ((upperStar A p).obj M) =
    (upperStarCompIso A h.symm).hom.app M := by
  have he : s ≫ (q ≫ i) = r ≫ i := by rw [← Category.assoc, hr]
  have h₁ := upperStarFactor_hom_app_assoc A rfl he hr rfl M
  have h₂ := upperStarFactor_hom_app_assoc A hb.symm he hk h M
  rw [upperStarCompIso_eq_upperStarFactor A hb rfl hb.symm,
    upperStarCompIso_eq_upperStarFactor A h.symm rfl h]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp]
  apply (cancel_epi ((upperStarFactor A (rfl : r ≫ i = r ≫ i)).hom.app M)).mp
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% h₁.symm]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% h₂]
  rw [Iso.hom_inv_id_app, Category.comp_id]

private theorem sheaf_open_comp_unit_transport
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X) (k : U ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] [IsOpenImmersion k]
    (hk : s ≫ b = k)
    (M : Sheaf (Scheme.ProEt.topology U) A) :
    (openImmersionLowerShriekUpperStarAdjunction A s).unit.app M ≫
      (upperStar A s).map
        ((openImmersionLowerShriekUpperStarAdjunction A b).unit.app
          ((openImmersionLowerShriek A s).obj M)) ≫
      (upperStarFactor A hk).inv.app
        ((openImmersionLowerShriek A b).obj
          ((openImmersionLowerShriek A s).obj M)) ≫
      (upperStar A k).map
        (((sheafOpenComp A s b).hom ≫ (sheafOpenCongr A hk).hom).app M) =
    (openImmersionLowerShriekUpperStarAdjunction A k).unit.app M := by
  exact left_comp_unit_with_data
    (openImmersionLowerShriekUpperStarAdjunction A s)
    (openImmersionLowerShriekUpperStarAdjunction A b)
    (openImmersionLowerShriekUpperStarAdjunction A (s ≫ b))
    (openImmersionLowerShriekUpperStarAdjunction A k)
    (upperStarComp A s b).symm (upperStarCongr A hk)
    (sheafOpenComp A s b) (sheafOpenCongr A hk) (upperStarFactor A hk)
    rfl rfl rfl M

private theorem expanded_clopen_composite
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
    (I : A ⥤ E) (P : E ⥤ D) (Q : A ⥤ B) (S : B ⥤ C)
    (J : C ⥤ B) (B₀ : B ⥤ D) (K : C ⥤ D) (R : A ⥤ C)
    (β : I ⋙ P ⟶ Q ⋙ B₀) (π : 𝟭 B ⟶ S ⋙ J)
    (c : J ⋙ B₀ ⟶ K) (d : Q ⋙ S ⟶ R) :
    β ≫ Functor.whiskerRight (Functor.whiskerLeft Q π) B₀ ≫
      Functor.whiskerRight (Functor.associator Q S J).inv B₀ ≫
      (Functor.associator (Q ⋙ S) J B₀).hom ≫ Functor.whiskerLeft (Q ⋙ S) c ≫
      Functor.whiskerRight d K = clopenMateComposite I P Q S J B₀ K R β π c d := by
  apply NatTrans.ext
  funext M
  simp only [clopenMateComposite_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.comp_obj, Category.id_comp]
  erw [B₀.map_id]
  simp only [Category.id_comp]

private theorem factor_restriction
    {A B C D E : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E]
    (Gs : B ⥤ C) (Gb : D ⥤ B) (Gq : A ⥤ B) (Gp : E ⥤ D)
    (Gi : E ⥤ A) (Gk : D ⥤ C) (Gr : A ⥤ C)
    (Jb : B ⥤ D) (Ji : A ⥤ E) (Js : C ⥤ B) (Jk : C ⥤ D)
    (ηi : 𝟭 A ⟶ Ji ⋙ Gi) (ηb : 𝟭 B ⟶ Jb ⋙ Gb)
    (ηs : 𝟭 C ⟶ Js ⋙ Gs) (ηk : 𝟭 C ⟶ Jk ⋙ Gk)
    (κr : Gr ≅ Gq ⋙ Gs) (κk : Gk ≅ Gb ⋙ Gs)
    (a : Gi ⋙ Gr ≅ Gp ⋙ Gk) (b : Gi ⋙ Gq ≅ Gp ⋙ Gb)
    (β : Gq ⋙ Jb ≅ Ji ⋙ Gp) (π : 𝟭 B ⟶ Gs ⋙ Js)
    (c : Js ⋙ Jb ⟶ Jk)
    (ha : ∀ F, κr.hom.app (Gi.obj F) ≫ Gs.map (b.hom.app F) ≫
      κk.inv.app (Gp.obj F) = a.hom.app F)
    (hπ : ∀ F, Gs.map (π.app F) = ηs.app (Gs.obj F))
    (hc : ∀ F, ηs.app F ≫ Gs.map (ηb.app (Js.obj F)) ≫
      κk.inv.app (Jb.obj (Js.obj F)) ≫ Gk.map (c.app F) = ηk.app F)
    (hβ : ∀ F, ηb.app (Gq.obj F) ≫ Gb.map (β.hom.app F) =
      Gq.map (ηi.app F) ≫ b.hom.app (Ji.obj F)) (F : A) :
    Gr.map (ηi.app F) ≫ a.hom.app (Ji.obj F) ≫
      Gk.map (β.inv.app F ≫ Jb.map (π.app (Gq.obj F)) ≫
        c.app (Gs.obj (Gq.obj F)) ≫ Jk.map (κr.inv.app F)) =
      ηk.app (Gr.obj F) := by
  have hnat := κr.hom.naturality (ηi.app F)
  simp only [CategoryTheory.Functor.comp_map] at hnat
  rw [← ha]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnat]
  rw [← κk.inv.naturality_assoc, ← κk.inv.naturality_assoc]
  simp only [CategoryTheory.Functor.comp_map]
  have hb : Gq.map (ηi.app F) ≫ b.hom.app _ ≫ Gb.map (β.inv.app F) =
      ηb.app (Gq.obj F) := by
    rw [← reassoc_of% hβ F]
    simp only [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
    erw [Gb.map_id, Category.comp_id]
  rw [← Gs.map_comp_assoc, ← Gs.map_comp_assoc]
  simp only [Category.assoc]
  rw [hb]
  have hn := ηb.naturality (π.app (Gq.obj F))
  simp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map] at hn
  rw [← Gs.map_comp_assoc]
  erw [← hn]
  rw [Gs.map_comp, Category.assoc, hπ]
  erw [reassoc_of% hc]
  have ht := ηk.naturality (κr.inv.app F)
  simp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map] at ht
  erw [← ht]
  exact κr.hom_inv_id_app_assoc F (ηk.app (Gr.obj F))

private theorem factor_normalized
    {A B C D E : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E]
    (Gs : B ⥤ C) (Gb : D ⥤ B) (Gq : A ⥤ B) (Gp : E ⥤ D)
    (Gi : E ⥤ A) (Gk : D ⥤ C) (Gr : A ⥤ C)
    (Jb : B ⥤ D) (Ji : A ⥤ E) (Js : C ⥤ B) (Jk : C ⥤ D)
    (ηi : 𝟭 A ⟶ Ji ⋙ Gi) (ηb : 𝟭 B ⟶ Jb ⋙ Gb)
    (ηs : 𝟭 C ⟶ Js ⋙ Gs) (ηk : 𝟭 C ⟶ Jk ⋙ Gk)
    (κr : Gr ≅ Gq ⋙ Gs) (κk : Gk ≅ Gb ⋙ Gs)
    (a : Gi ⋙ Gr ≅ Gp ⋙ Gk) (b : Gi ⋙ Gq ≅ Gp ⋙ Gb)
    (β : Gq ⋙ Jb ≅ Ji ⋙ Gp) (π : 𝟭 B ⟶ Gs ⋙ Js)
    (c : Js ⋙ Jb ⟶ Jk)
    (ha : ∀ F, κr.hom.app (Gi.obj F) ≫ Gs.map (b.hom.app F) ≫
      κk.inv.app (Gp.obj F) = a.hom.app F)
    (hπ : ∀ F, Gs.map (π.app F) = ηs.app (Gs.obj F))
    (hc : ∀ F, ηs.app F ≫ Gs.map (ηb.app (Js.obj F)) ≫
      κk.inv.app (Jb.obj (Js.obj F)) ≫ Gk.map (c.app F) = ηk.app F)
    (hβ : ∀ F, ηb.app (Gq.obj F) ≫ Gb.map (β.hom.app F) =
      Gq.map (ηi.app F) ≫ b.hom.app (Ji.obj F)) (d : Gq ⋙ Gs ⟶ Gr) (hd : d = κr.inv) :
    restrictionNormalized Gr ηi a (fun F ↦ ηk.app (Gr.obj F))
      (clopenMateComposite Ji Gp Gq Gs Js Jb Jk Gr β.inv π c d) := by
  intro F
  rw [clopenMateComposite_app, hd]
  exact factor_restriction Gs Gb Gq Gp Gi Gk Gr Jb Ji Js Jk ηi ηb ηs ηk
    κr κk a b β π c ha hπ hc hβ F

private theorem sheaf_beta_inverse_unit
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (b : U' ⟶ X')
    (i : U ⟶ X) (p : X' ⟶ X) [IsOpenImmersion i] [IsOpenImmersion b]
    (sq : IsPullback a b i p) (M : Sheaf (Scheme.ProEt.topology U) A) :
    (openImmersionLowerShriekUpperStarAdjunction A b).unit.app
        ((upperStar A a).obj M) ≫
      (upperStar A b).map ((sheafBeta A a b i p sq).inv.app M) =
    (upperStar A a).map
        ((openImmersionLowerShriekUpperStarAdjunction A i).unit.app M) ≫
      (upperStarCompIso A sq.w).hom.app ((openImmersionLowerShriek A i).obj M) := by
  have he : (sheafBeta A a b i p sq).inv =
      openImmersionLowerShriekBaseChangeMap A sq.toCommSq :=
    conjugate_inverse_hom _ _ _
  rw [he]
  exact sheaf_beta_unit A a b i p sq M

private theorem sheaf_factor_normalized
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {U P V W Z : Scheme.{u}} (s : U ⟶ P) (b : P ⟶ V) (q : P ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) (k : U ⟶ V) (r : U ⟶ W)
    [IsOpenImmersion i] [IsOpenImmersion b] [IsOpenImmersion k]
    [IsOpenImmersion s] [IsClosedImmersion s]
    (hk : s ≫ b = k) (hr : s ≫ q = r) (sq : IsPullback q b i p)
    (h : k ≫ p = r ≫ i) :
    restrictionNormalized (upperStar A r)
      (openImmersionLowerShriekUpperStarAdjunction A i).unit (upperStarCompIso A h.symm)
      (fun M ↦ (openImmersionLowerShriekUpperStarAdjunction A k).unit.app
        ((upperStar A r).obj M))
      (clopenMateComposite (openImmersionLowerShriek A i) (upperStar A p)
        (upperStar A q) (upperStar A s) (openImmersionLowerShriek A s)
        (openImmersionLowerShriek A b) (openImmersionLowerShriek A k) (upperStar A r)
        (sheafBeta A q b i p sq).hom (sheafProjector A s)
        ((sheafOpenComp A s b).hom ≫ (sheafOpenCongr A hk).hom)
        ((upperStarComp A s q).inv ≫ (upperStarCongr A hr).hom)) := by
  have hd : (upperStarComp A s q).inv ≫ (upperStarCongr A hr).hom =
      (upperStarFactor A hr).inv := by rfl
  exact factor_normalized
    (upperStar A s) (upperStar A b) (upperStar A q) (upperStar A p)
    (upperStar A i) (upperStar A k) (upperStar A r)
    (openImmersionLowerShriek A b) (openImmersionLowerShriek A i)
    (openImmersionLowerShriek A s) (openImmersionLowerShriek A k)
    (openImmersionLowerShriekUpperStarAdjunction A i).unit
    (openImmersionLowerShriekUpperStarAdjunction A b).unit
    (openImmersionLowerShriekUpperStarAdjunction A s).unit
    (openImmersionLowerShriekUpperStarAdjunction A k).unit
    (upperStarFactor A hr) (upperStarFactor A hk)
    (upperStarCompIso A h.symm) (upperStarCompIso A sq.w)
    (sheafBeta A q b i p sq).symm (sheafProjector A s)
    ((sheafOpenComp A s b).hom ≫ (sheafOpenCongr A hk).hom)
    (sheaf_lift_square_unit A s b q p i k r hk hr sq.w h)
    (sheaf_projector_restrict A s) (sheaf_open_comp_unit_transport A s b k hk)
    (sheaf_beta_inverse_unit A q b i p sq)
    ((upperStarComp A s q).inv ≫ (upperStarCongr A hr).hom) hd

private theorem sheaf_alpha_normalized
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    sheafNormalized A k r p i h.symm (sheafAlpha A k r p i h) := by
  let : IsOpenImmersion (StrictTower.squareLift k r p i h) :=
    (StrictTower.squareLift_clopen k r p i h).1
  let : IsClosedImmersion (StrictTower.squareLift k r p i h) :=
    (StrictTower.squareLift_clopen k r p i h).2
  exact sheaf_factor_normalized A (StrictTower.squareLift k r p i h)
    (pullback.fst p i) (pullback.snd p i) p i k r
    (squareLift_fst k r p i h) (squareLift_snd k r p i h)
    (IsPullback.of_hasPullback p i).flip h

private theorem ordinary_alpha_normalized
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    Normalized Λ k r p i h (alpha Λ k r p i h) := by
  exact sheaf_alpha_normalized (ModuleCat.{u + 1} Λ) k r p i h

private theorem normalized_of_inverse
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {I : A ⥤ B} {T : B ⥤ A} {P : B ⥤ C} {J : D ⥤ C} {K : C ⥤ D}
    (R : A ⥤ D) (η : 𝟭 A ⟶ I ⋙ T) [IsIso η]
    (σ : T ⋙ R ≅ P ⋙ K) (υ : 𝟭 D ⟶ J ⋙ K) [IsIso υ]
    (a : I ⋙ P ⟶ R ⋙ J)
    (h : ∀ M, K.map (a.app M) ≫ inv (υ.app (R.obj M)) =
      σ.inv.app (I.obj M) ≫ R.map (inv (η.app M))) :
    restrictionNormalized R η σ (fun M ↦ υ.app (R.obj M)) a := by
  intro M
  apply (cancel_mono (inv (υ.app (R.obj M)))).mp
  simp only [Category.assoc]
  rw [h M]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp, IsIso.hom_inv_id]
  exact R.map_id _

private theorem system_alpha_normalized
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    Systems.Normalized C τ k r p i h (VaryingRing.moduleAlpha C τ k r p i h) := by
  have := VaryingRing.moduleJAdj_unit_isIso C τ i
  have := VaryingRing.moduleJAdj_unit_isIso C τ k
  exact normalized_of_inverse (VaryingRing.pull C τ r)
    (VaryingRing.moduleJAdj C τ i).unit (VaryingRing.moduleSquareG C τ k r p i h)
    (VaryingRing.moduleJAdj C τ k).unit _
    (VaryingRing.moduleAlpha_restriction C τ k r p i h)

private theorem system_normalized_unique
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (a b : VaryingRing.extension C τ i ⋙ VaryingRing.pull C τ p ⟶
      VaryingRing.pull C τ r ⋙ VaryingRing.extension C τ k)
    (ha : Systems.Normalized C τ k r p i h a)
    (hb : Systems.Normalized C τ k r p i h b) : a = b := by
  let : IsOpenImmersion (StrictTower.squareLift k r p i h) :=
    (StrictTower.squareLift_clopen k r p i h).1
  let : IsClosedImmersion (StrictTower.squareLift k r p i h) :=
    (StrictTower.squareLift_clopen k r p i h).2
  have := VaryingRing.moduleJAdj_unit_isIso C τ i
  apply NatTrans.ext
  funext M
  apply VaryingRing.module_clopen_factor_hom_ext C τ
    (StrictTower.squareLift k r p i h) (pullback.fst p i) k (squareLift_fst k r p i h)
    ((VaryingRing.moduleBeta C τ (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip).app M)
  apply (cancel_epi ((VaryingRing.moduleSquareG C τ k r p i h).hom.app
    ((VaryingRing.extension C τ i).obj M))).mp
  apply (cancel_epi ((VaryingRing.pull C τ r).map
    ((VaryingRing.moduleJAdj C τ i).unit.app M))).mp
  exact (ha M).trans (hb M).symm

private theorem mate_transport_with_data
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₁' : A ⥤ B} {R₁ R₁' : B ⥤ A}
    {L₂ L₂' : C ⥤ D} {R₂ R₂' : D ⥤ C}
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (a : L₁ ⊣ R₁) (a' : L₁' ⊣ R₁') (b : L₂ ⊣ R₂) (b' : L₂' ⊣ R₂')
    (e : L₁ ≅ L₁') (f : L₂ ≅ L₂') (g : G ≅ G') (h : H ≅ H')
    (α : G' ⋙ L₂' ⟶ L₁' ⋙ H') (γ : R₁ ⋙ G ⟶ H ⋙ R₂)
    (d₁ : R₁ ≅ R₁') (d₂ : R₂ ≅ R₂') (δ : R₁' ⋙ G' ⟶ H' ⋙ R₂')
    (t : G ⋙ L₂ ⟶ L₁ ⋙ H)
    (h₁ : d₁ = conjugateIsoEquiv a a' e.symm)
    (h₂ : d₂ = conjugateIsoEquiv b b' f.symm)
    (hδ : δ = (mateEquiv a' b' (TwoSquare.mk _ _ _ _ α)).natTrans)
    (ht : t = transportAlpha e f g h α) (M : B)
    (hc : γ.app M ≫ d₂.hom.app (H.obj M) ≫ R₂'.map (h.hom.app M) =
      g.hom.app (R₁.obj M) ≫ G'.map (d₁.hom.app M) ≫ δ.app M) :
    properMateFormula a b t γ M := by
  subst d₁
  subst d₂
  subst δ
  subst t
  exact mate_transport_formula a a' b b' e f g h α γ M hc

section NativeRealization
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] Functor.ofOpSequence Functor.ofSequence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {U V W Z : Scheme.{u}}

private def modelPull (f : U ⟶ V) : System l E V ⥤ System l E U :=
  SemilinearProperOpen.P (scalarRings l E) (scalarTransitions l E) f

private def modelPush (f : U ⟶ V) : System l E U ⥤ System l E V :=
  SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) f

private def modelShriek (j : U ⟶ V) [IsOpenImmersion j] : System l E U ⥤ System l E V :=
  SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) j

private def modelAdj (f : U ⟶ V) : modelPull l E f ⊣ modelPush l E f :=
  SemilinearProperOpen.adj (scalarRings l E) (scalarTransitions l E) f

variable (o : Operations l E) (b : CanonicalBridge l E o)

private def modelBridgePull (f : U ⟶ V) : pull l E f ≅ modelPull l E f :=
  b.pull l E f

private def modelBridgePush (f : U ⟶ V) : Operations.push l E o f ≅ modelPush l E f :=
  b.push l E f

private def modelBridgeShriek (j : U ⟶ V) [IsOpenImmersion j] :
    Operations.shriek l E o j ≅ modelShriek l E j :=
  b.shriek l E j

private theorem bridge_push_normalized (f : U ⟶ V) : modelBridgePush l E o b f =
    conjugateIsoEquiv (o.direct f).adj (modelAdj l E f)
      (modelBridgePull l E o b f).symm := by
  rfl

variable (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
  [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
  [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)

private def modelAlpha : modelShriek l E i ⋙ modelPull l E p ⟶
    modelPull l E r ⋙ modelShriek l E k :=
  SemilinearProperOpen.alpha (scalarRings l E) (scalarTransitions l E) k r p i h

private def modelGamma : modelPush l E r ⋙ modelShriek l E i ⟶
    modelShriek l E k ⋙ modelPush l E p :=
  SemilinearProperOpen.gamma (scalarRings l E) (scalarTransitions l E) k r p i h

private theorem intrinsic_gamma_normalized : modelGamma l E k r p i h =
    (mateEquiv (modelAdj l E r) (modelAdj l E p)
      (TwoSquare.mk _ _ _ _ (modelAlpha l E k r p i h))).natTrans := by
  rfl

private theorem realization_alpha_normalized : realizationAlpha l E o b k r p i h =
    transportAlpha (modelBridgePull l E o b r) (modelBridgePull l E o b p)
      (modelBridgeShriek l E o b i) (modelBridgeShriek l E o b k)
      (modelAlpha l E k r p i h) := by
  rfl

attribute [local irreducible] modelPull modelPush modelShriek modelAdj
  modelBridgePull modelBridgePush modelBridgeShriek modelAlpha modelGamma
  Direct.adj CanonicalBridge.push realizationAlpha SemilinearProperOpen.gamma

end NativeRealization

attribute [local irreducible] Functor.ofOpSequence Functor.ofSequence

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem realization_mate
    (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (∀ (o : Operations l E) (z : Realizations l E F o) (M : System l E U),
      properMateFormula (o.direct r).adj (o.direct p).adj
        (realizationAlpha l E o z.canonicalBridge k r p i h)
        (z.properOpen.gamma k r p i h) M) := by
  intro o z M
  have hc : (z.properOpen.gamma k r p i h).app M ≫
      (modelBridgePush l E o z.canonicalBridge p).hom.app
        ((Operations.shriek l E o k).obj M) ≫
      (modelPush l E p).map ((modelBridgeShriek l E o z.canonicalBridge k).hom.app M) =
    (modelBridgeShriek l E o z.canonicalBridge i).hom.app
        ((Operations.push l E o r).obj M) ≫
      (modelShriek l E i).map ((modelBridgePush l E o z.canonicalBridge r).hom.app M) ≫
      (modelGamma l E k r p i h).app M := z.properOpen.canonical k r p i h M
  exact @mate_transport_with_data
    (System l E W) (System l E U) (System l E Z) (System l E V)
    (inferInstanceAs (Category.{u + 2} (System l E W)))
    (inferInstanceAs (Category.{u + 2} (System l E U)))
    (inferInstanceAs (Category.{u + 2} (System l E Z)))
    (inferInstanceAs (Category.{u + 2} (System l E V)))
    (pull l E r) (modelPull l E r) (Operations.push l E o r) (modelPush l E r)
    (pull l E p) (modelPull l E p) (Operations.push l E o p) (modelPush l E p)
    (Operations.shriek l E o i) (modelShriek l E i)
    (Operations.shriek l E o k) (modelShriek l E k)
    (o.direct r).adj (modelAdj l E r) (o.direct p).adj (modelAdj l E p)
    (modelBridgePull l E o z.canonicalBridge r) (modelBridgePull l E o z.canonicalBridge p)
    (modelBridgeShriek l E o z.canonicalBridge i) (modelBridgeShriek l E o z.canonicalBridge k)
    (modelAlpha l E k r p i h) (z.properOpen.gamma k r p i h)
    (modelBridgePush l E o z.canonicalBridge r) (modelBridgePush l E o z.canonicalBridge p)
    (modelGamma l E k r p i h) (realizationAlpha l E o z.canonicalBridge k r p i h)
    (bridge_push_normalized l E o z.canonicalBridge r)
    (bridge_push_normalized l E o z.canonicalBridge p)
    (intrinsic_gamma_normalized l E k r p i h)
    (realization_alpha_normalized l E o z.canonicalBridge k r p i h) M hc

private theorem chosen_derived_adjunction_congr
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions B]
    (P Q : B ⥤ A) [P.IsRightAdjoint] [Q.IsRightAdjoint]
    [P.Additive] [Q.Additive] [P.leftAdjoint.Additive] [Q.leftAdjoint.Additive]
    [PreservesFiniteLimits P.leftAdjoint] [PreservesFiniteColimits P.leftAdjoint]
    [PreservesFiniteLimits Q.leftAdjoint] [PreservesFiniteColimits Q.leftAdjoint]
    (h : P = Q) :
    HEq (Adjunction.ofIsRightAdjoint P).mapDerivedCategoryRightDerivedAdjunction
      (Adjunction.ofIsRightAdjoint Q).mapDerivedCategoryRightDerivedAdjunction := by
  subst Q
  rfl

private theorem system_proper_adjunction_congr
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    HEq (VaryingRing.adj C τ f) (SemilinearProperOpen.adj C τ f) := by
  have := SemilinearProperOpen.push_isRightAdjoint C τ f
  have := SemilinearProperOpen.push_additive C τ f
  have := SemilinearProperOpen.pull_additive C τ f
  have := SemilinearProperOpen.pull_limits C τ f
  have := SemilinearProperOpen.pull_colimits C τ f
  unfold VaryingRing.adj VaryingRing.moduleAdj SemilinearProperOpen.adj
    SemilinearProperOpen.ordinaryAdj
  unfold VaryingRing.G VaryingRing.P SemilinearProperOpen.P SemilinearProperOpen.R
  exact chosen_derived_adjunction_congr (VaryingRing.push C τ f)
    (SemilinearProperOpen.push C τ f) (SemilinearProperOpen.push_eq C τ f).symm

private theorem mate_heq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₁' : A ⥤ B} {R₁ R₁' : B ⥤ A}
    {L₂ L₂' : C ⥤ D} {R₂ R₂' : D ⥤ C}
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (a : L₁ ⊣ R₁) (a' : L₁' ⊣ R₁') (b : L₂ ⊣ R₂) (b' : L₂' ⊣ R₂')
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (α' : G' ⋙ L₂' ⟶ L₁' ⋙ H')
    (e₁ : L₁ = L₁') (e₂ : R₁ = R₁') (e₃ : L₂ = L₂') (e₄ : R₂ = R₂')
    (e₅ : G = G') (e₆ : H = H') (ha : HEq a a') (hb : HEq b b') (hα : HEq α α') :
    HEq (mateEquiv a b (TwoSquare.mk _ _ _ _ α)).natTrans
      (mateEquiv a' b' (TwoSquare.mk _ _ _ _ α')).natTrans := by
  subst L₁'
  subst R₁'
  subst L₂'
  subst R₂'
  subst G'
  subst H'
  cases ha
  cases hb
  cases hα
  rfl

private theorem system_gamma_congr
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (ha : HEq (localizeSquare _ _ _ _ (VaryingRing.moduleAlpha C τ k r p i h))
      (SemilinearProperOpen.alpha C τ k r p i h)) :
    HEq (VaryingRing.gamma C τ k r p i h)
      (SemilinearProperOpen.gamma C τ k r p i h) := by
  exact mate_heq
    (VaryingRing.adj C τ r) (SemilinearProperOpen.adj C τ r)
    (VaryingRing.adj C τ p) (SemilinearProperOpen.adj C τ p)
    (VaryingRing.alpha C τ k r p i h) (SemilinearProperOpen.alpha C τ k r p i h)
    (SemilinearProperOpen.P_eq C τ r).symm (SemilinearProperOpen.R_eq C τ r).symm
    (SemilinearProperOpen.P_eq C τ p).symm (SemilinearProperOpen.R_eq C τ p).symm
    (SemilinearProperOpen.J_eq C τ i).symm (SemilinearProperOpen.J_eq C τ k).symm
    (system_proper_adjunction_congr C τ r) (system_proper_adjunction_congr C τ p) ha

private theorem ordinary_assertion
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    OrdinaryAssertion Λ k r p i h := by
  have hn := ordinary_alpha_normalized Λ k r p i h
  have hd := ordinary_alpha_localized Λ k r p i h
  refine ⟨hn, ?_, hd, ordinary_beta_localizes Λ _ _ i p _, ?_, ?_, ?_⟩
  · intro a ha
    exact ordinary_normalized_unique Λ k r p i h a _ ha hn
  · rw [ordinary_open_adjunction_exact]
    exact adjunction_on_complexes _
  · rw [ordinary_open_adjunction_exact]
    exact adjunction_on_complexes _
  · intro M
    rw [hd]
    simp only [properOpenMate, mateEquiv_apply, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.rightUnitor_inv_app,
      Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.comp_map, Functor.id_obj,
      Category.id_comp, Category.comp_id]

private theorem system_assertion
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    Systems.Assertion C τ k r p i h := by
  have hn := system_alpha_normalized C τ k r p i h
  have ha := system_alpha_localized C τ k r p i h
  refine ⟨hn, ?_, ha, system_beta_localized C τ _ _ i p _ _,
    adjunction_on_complexes _, adjunction_on_complexes _,
    system_open_adjunction_exact C τ i, system_open_adjunction_exact C τ k,
    system_gamma_congr C τ k r p i h ha, ?_⟩
  · intro a hh
    exact system_normalized_unique C τ k r p i h a _ hh hn
  · intro M
    simp only [VaryingRing.gamma, mateEquiv_apply, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.rightUnitor_inv_app,
      Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.comp_map, Functor.id_obj,
      Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The intrinsic clopen comparison is exactly the localization of the specified ordinary
comparison in both coefficient categories, and its proper mate has the specified
unit--comparison--counit normalization. Source: Stacks 0F7B and 07A7; exact localization
from derived.tex, Tag 015F; agent extension to the stated ambient categories
(blueprint: lem-sf-ambient-exact-clopen-comparison-localization).

Proof: The ordinary beta-unit equation, projector restriction and normalized open
compositor give the restriction equation; the open direct-image unit detects equality
and proves uniqueness. The existing system restriction theorem and clopen-factor Hom
extensionality give these assertions simultaneously for systems. Exact localization
of the specified ordinary adjunction gives both equations on arbitrary cochain
complexes. The separate ordinary and system localization theorems identify the
beta/projector/compositor words with the intrinsic alpha. Expanding the proper mate
bijection gives its unit--alpha--counit formula. Equality of the two chosen system
adjunctions transports gamma between presentations. Finally, naturality of that
bijection under the four canonical bridge isomorphisms gives the realization formula.
No equality of system transformations is deduced from finite evaluation. -/
theorem ambientExactClopenComparisonLocalizes
    (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U V W Z : Scheme.{u}}
    [U.Over (Spec (.of F.k))] [V.Over (Spec (.of F.k))]
    [W.Over (Spec (.of F.k))] [Z.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of F.k))] [QuasiCompact (U ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of F.k))] [QuasiCompact (V ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of F.k))] [QuasiCompact (Z ↘ Spec (.of F.k))]
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [k.IsOver (Spec (.of F.k))] [r.IsOver (Spec (.of F.k))]
    [p.IsOver (Spec (.of F.k))] [i.IsOver (Spec (.of F.k))]
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (∀ n : ℕ, OrdinaryAssertion (scalarRings l E n) k r p i h) ∧
      Systems.Assertion (scalarRings l E) (scalarTransitions l E) k r p i h ∧
      (∀ (o : Operations l E) (z : Realizations l E F o) (M : System l E U),
        properMateFormula (o.direct r).adj (o.direct p).adj
          (realizationAlpha l E o z.canonicalBridge k r p i h)
          (z.properOpen.gamma k r p i h) M) := by
  exact ⟨fun n ↦ ordinary_assertion (scalarRings l E n) k r p i h,
    system_assertion (scalarRings l E) (scalarTransitions l E) k r p i h,
    realization_mate F l E k r p i h⟩

end AlgebraicGeometry.ProEtale.AmbientClopen
