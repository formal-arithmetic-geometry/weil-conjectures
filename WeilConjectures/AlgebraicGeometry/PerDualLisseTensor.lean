/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructiblePushforwardRestriction
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeInternalHomColimits
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison
public import WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Comparison
public import WeilConjectures.ProperBaseChange.CondensedFiniteFreeTensorExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux

/-!
# Dual of a lisse tensor

Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
  sec-fourier-transform/sec-wft-perverse/sk-lem-wft-curve-heart/lem-per-dual-lisse-tensor.md`
(blueprint: lem-per-dual-lisse-tensor).

The statement uses the native module-object derived category.  The dualizing object is
the chosen bounded-constructible upper exceptional functor at the structure morphism,
applied to the coefficient unit.  The ordinary dual of a lisse module is its internal Hom
into the unit, placed in degree zero.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] CondensedRing.exceptionalInverseImageCompactification
attribute [local irreducible] CondensedRing.exceptionalInverseImageProperPushforward

private noncomputable def beta (K W : C) :
    tensorLeft ((ihom K).obj W) ⟶ tensorLeft W ⋙ ihom K where
  app N := ihomTensorToIhom K W N
  naturality {N N'} f := by
    change ((ihom K).obj W) ◁ f ≫ _ = _ ≫ (ihom K).map (W ◁ f)
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_natural_right]
    simp only [ihomTensorToIhom, uncurry_curry]
    rw [associator_inv_naturality_right_assoc, whisker_exchange]
    simp only [Functor.id_obj, Category.assoc]

private lemma beta_unit (K W : C) : IsIso ((beta K W).app (𝟙_ C)) := by
  exact isIso_ihomTensorToIhom K W isInvertible_unit

private lemma beta_finite {n : ℕ} (K W : C)
    [HasBiproduct (fun _ : Fin n ↦ 𝟙_ C)] :
    IsIso (ihomTensorToIhom K W (⨁ fun _ : Fin n ↦ 𝟙_ C)) := by
  exact NatTrans.isIso_app_biproduct (beta K W) _ fun _ ↦ beta_unit K W

private lemma alpha_naturality {X Y : C} (f : X ⟶ Y) (W : C) :
    ihomUnitTensorToIhom Y W ≫ (pre f).app W =
      (pre f).app (𝟙_ C) ▷ W ≫ ihomUnitTensorToIhom X W := by
  apply uncurry_injective
  rw [uncurry_eq, uncurry_eq, MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, id_tensor_pre_app_comp_ev,
    whiskerLeft_ihomUnitTensorToIhom_ev, whisker_exchange_assoc,
    whiskerLeft_ihomUnitTensorToIhom_ev, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, id_tensor_pre_app_comp_ev, comp_whiskerRight_assoc,
    associator_inv_naturality_left_assoc]

private lemma alpha_finite [HasFiniteBiproducts C] {n : ℕ} (P W : C)
    (e : P ≅ ⨁ fun _ : Fin n ↦ 𝟙_ C) : IsIso (ihomUnitTensorToIhom P W) := by
  classical
  let U := 𝟙_ C
  let i (j : Fin n) := biproduct.ι (fun _ : Fin n ↦ U) j ≫ e.inv
  let p (j : Fin n) := e.hom ≫ biproduct.π (fun _ : Fin n ↦ U) j
  have ht : ∑ j, p j ≫ i j = 𝟙 P := by
    simp only [p, i, Category.assoc, ← Preadditive.comp_sum]
    simp_rw [← Category.assoc]
    rw [← Preadditive.sum_comp, biproduct.total]
    rw [Category.id_comp]
    exact e.hom_inv_id
  have : IsIso (ihomUnitTensorToIhom U W) :=
    isIso_ihomUnitTensorToIhom U U W
  let q := ∑ j, (pre (i j)).app W ≫ inv (ihomUnitTensorToIhom U W) ≫
    (pre (p j)).app (𝟙_ C) ▷ W
  have h₁ : ihomUnitTensorToIhom P W ≫ q = 𝟙 _ := by
    dsimp only [q]
    rw [Preadditive.comp_sum]
    have hj (j : Fin n) : ihomUnitTensorToIhom P W ≫
        ((pre (i j)).app W ≫ inv (ihomUnitTensorToIhom U W) ≫
          (pre (p j)).app (𝟙_ C) ▷ W) =
        (pre (p j ≫ i j)).app (𝟙_ C) ▷ W := by
      rw [← Category.assoc, alpha_naturality (i j)]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
      rw [← comp_whiskerRight, ← NatTrans.comp_app, ← pre_map]
    simp only [hj]
    have h := _root_.map_sum (preAppAddHom P P (𝟙_ C))
      (fun j ↦ p j ≫ i j) Finset.univ
    simp only [preAppAddHom_apply] at h
    change ∑ j, (tensorRight W).map ((pre (p j ≫ i j)).app (𝟙_ C)) = _
    rw [← (tensorRight W).map_sum, ← h, ht, pre_id, NatTrans.id_app]
    exact (tensorRight W).map_id _
  have h₂ : q ≫ ihomUnitTensorToIhom P W = 𝟙 _ := by
    dsimp only [q]
    rw [Preadditive.sum_comp]
    simp only [Category.assoc, ← alpha_naturality (p _), IsIso.inv_hom_id_assoc]
    simp only [← NatTrans.comp_app, ← pre_map]
    have h := _root_.map_sum (preAppAddHom P P W)
      (fun j ↦ p j ≫ i j) Finset.univ
    simp only [preAppAddHom_apply] at h
    rw [← h, ht, pre_id, NatTrans.id_app]
  exact ⟨⟨q, h₁, h₂⟩⟩

private noncomputable def dualFiniteIso [HasFiniteBiproducts C] {n : ℕ} (P : C)
    (e : P ≅ ⨁ fun _ : Fin n ↦ 𝟙_ C) :
    (ihom P).obj (𝟙_ C) ≅ ⨁ fun _ : Fin n ↦ 𝟙_ C := by
  classical
  let U := 𝟙_ C
  let i (j : Fin n) := biproduct.ι (fun _ : Fin n ↦ U) j ≫ e.inv
  let p (j : Fin n) := e.hom ≫ biproduct.π (fun _ : Fin n ↦ U) j
  have ht : ∑ j, p j ≫ i j = 𝟙 P := by
    simp only [p, i, Category.assoc, ← Preadditive.comp_sum]
    simp_rw [← Category.assoc]
    rw [← Preadditive.sum_comp, biproduct.total]
    rw [Category.id_comp]
    exact e.hom_inv_id
  let f := biproduct.lift (fun j ↦ (pre (i j)).app U)
  let g := biproduct.desc (fun j ↦ (pre (p j)).app U)
  have hfg : f ≫ g = 𝟙 _ := by
    simp only [f, g, biproduct.lift_desc, ← NatTrans.comp_app, ← pre_map]
    have h := _root_.map_sum (preAppAddHom P P U) (fun j ↦ p j ≫ i j) Finset.univ
    simp only [preAppAddHom_apply] at h
    rw [← h, ht, pre_id, NatTrans.id_app]
  have hgf : g ≫ f = 𝟙 _ := by
    apply biproduct.hom_ext
    intro j
    apply biproduct.hom_ext'
    intro k
    simp only [Category.assoc, g, f, biproduct.lift_π, biproduct.ι_desc_assoc]
    rw [← NatTrans.comp_app, ← pre_map]
    dsimp only [i, p]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    by_cases h : k = j
    · subst j
      simp
    · simp [h, Ne.symm h]
  exact Iso.mk f g hfg hgf ≪≫
    biproduct.mapIso (fun _ ↦ (unitNatIso.app U).symm)

private lemma map_beta (K W N : C) :
    G.map (ihomTensorToIhom K W N) ≫ (ihomComparison G K).natTrans.app (W ⊗ N) ≫
      (ihom (G.obj K)).map (δ G W N) =
    δ G _ N ≫ (ihomComparison G K).natTrans.app W ▷ G.obj N ≫
      ihomTensorToIhom (G.obj K) (G.obj W) (G.obj N) := by
  apply uncurry_injective
  rw [uncurry_eq, uncurry_eq, MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, ihom.ev_naturality,
    ihomComparison_ev_assoc, μ_natural_right_assoc, ← G.map_comp_assoc,
    whiskerLeft_ihomTensorToIhom_ev]
  rw [MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, whiskerLeft_ihomTensorToIhom_ev,
    ]
  dsimp only [Functor.comp_obj]
  erw [associator_inv_naturality_middle_assoc (G.obj K)
    ((ihomComparison G K).natTrans.app W) (G.obj N)]
  dsimp only [Functor.comp_obj]
  erw [← comp_whiskerRight]
  rw [ihomComparison_ev]
  rw [← cancel_epi (G.obj K ◁ μ G _ N), ← MonoidalCategory.whiskerLeft_comp_assoc,
    μ_δ, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  simp only [Functor.map_comp, Functor.Monoidal.map_associator_inv,
    Functor.Monoidal.map_whiskerRight, Category.assoc, μ_δ_assoc, comp_whiskerRight]
  simp only [Functor.id_obj, curriedTensor_obj_obj, μ_δ, Category.comp_id, δ_natural_left,
    whiskerLeft_μ_δ_assoc, Iso.cancel_iso_inv_left]
  rw [← μ_natural_left_assoc, μ_δ, Category.comp_id]

private lemma isIso_map_beta (K W N : C)
    [IsIso (ihomComparison G K).natTrans]
    [IsIso (ihomTensorToIhom (G.obj K) (G.obj W) (G.obj N))] :
    IsIso (G.map (ihomTensorToIhom K W N)) := by
  have h := map_beta G K W N
  have : IsIso (G.map (ihomTensorToIhom K W N) ≫
      (ihomComparison G K).natTrans.app (W ⊗ N) ≫
      (ihom (G.obj K)).map (δ G W N)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((ihomComparison G K).natTrans.app (W ⊗ N) ≫
      (ihom (G.obj K)).map (δ G W N))

private lemma alpha_local (P W : C)
    [HasFiniteBiproducts C] {I : Type*}
    (D : I → Type*) [∀ i, Category (D i)] [∀ i, Preadditive (D i)]
    [∀ i, MonoidalCategory (D i)] [∀ i, MonoidalClosed (D i)]
    [∀ i, MonoidalPreadditive (D i)] [∀ i, HasFiniteBiproducts (D i)]
    (F : ∀ i, C ⥤ D i) [∀ i, (F i).Monoidal]
    (reflect : ∀ {A B : C} (f : A ⟶ B),
      (∀ i, IsIso ((F i).map f)) → IsIso f)
    [∀ i, IsIso (ihomComparison (F i) P).natTrans]
    (free : ∀ i, ∃ n : ℕ, Nonempty ((F i).obj P ≅ ⨁ fun _ : Fin n ↦ 𝟙_ _)) :
    IsIso (ihomUnitTensorToIhom P W) := by
  apply reflect
  intro i
  obtain ⟨n, ⟨e⟩⟩ := free i
  have := alpha_finite ((F i).obj P) ((F i).obj W) e
  exact Functor.Monoidal.isIso_map_ihomUnitTensorToIhom_of_ihomComparison (F i) P W

private lemma beta_local (P K W : C)
    [HasFiniteBiproducts C] {I : Type*}
    (D : I → Type*) [∀ i, Category (D i)] [∀ i, Preadditive (D i)]
    [∀ i, MonoidalCategory (D i)] [∀ i, MonoidalClosed (D i)]
    [∀ i, MonoidalPreadditive (D i)] [∀ i, HasFiniteBiproducts (D i)]
    (F : ∀ i, C ⥤ D i) [∀ i, (F i).Monoidal]
    (reflect : ∀ {A B : C} (f : A ⟶ B),
      (∀ i, IsIso ((F i).map f)) → IsIso f)
    [∀ i, IsIso (ihomComparison (F i) P).natTrans]
    [∀ i, IsIso (ihomComparison (F i) K).natTrans]
    (free : ∀ i, ∃ n : ℕ, Nonempty ((F i).obj P ≅ ⨁ fun _ : Fin n ↦ 𝟙_ _)) :
    IsIso (ihomTensorToIhom K W ((ihom P).obj (𝟙_ _))) := by
  apply reflect
  intro i
  obtain ⟨n, ⟨e⟩⟩ := free i
  let eD : (F i).obj ((ihom P).obj (𝟙_ _)) ≅ ⨁ fun _ : Fin n ↦ 𝟙_ _ :=
    asIso ((ihomComparison (F i) P).natTrans.app (𝟙_ _)) ≪≫
      (ihom ((F i).obj P)).mapIso (asIso (η (F i))) ≪≫
      dualFiniteIso ((F i).obj P) e
  have : IsIso (ihomTensorToIhom ((F i).obj K) ((F i).obj W)
      ((F i).obj ((ihom P).obj (𝟙_ _)))) :=
    (NatTrans.isIso_app_iff_of_iso (beta ((F i).obj K) ((F i).obj W)) eD).mpr
      (beta_finite ((F i).obj K) ((F i).obj W))
  exact isIso_map_beta (F i) K W _

private noncomputable def finiteMapIso [HasFiniteBiproducts C]
    (F : C ⥤ D) [F.Additive] {n : ℕ} {P U : C} {V : D}
    (e : P ≅ ⨁ fun _ : Fin n ↦ U) (v : F.obj U ≅ V) :
    F.obj P ≅ ⨁ fun _ : Fin n ↦ V :=
  F.mapIso e ≪≫ F.mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦ v)

private noncomputable def localSingleFree
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}}
    (g : Y ⟶ X) [WeaklyEtale g]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    {n : ℕ}
    (e : (CondensedRing.upperStar Λ g).obj L ≅ ⨁ fun _ : Fin n ↦ 𝟙_ _) :
    (L((g)^*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj L) ≅
      ⨁ fun _ : Fin n ↦ 𝟙_ _ :=

private theorem localAlpha
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hL : IsLisseCoefficientModule Λ L)
    (W : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    IsIso (ihomUnitTensorToIhom ((DerivedCategory.singleFunctor _ 0).obj L) W) := by
  obtain ⟨V, hV⟩ := hL
  have (i : V.I₀) : WeaklyEtale (V.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ V.mem₀ (.mk i)
  have (i : V.I₀) := isIso_ihomComparison_leftDerivedUpperStar_of_weaklyEtale
    Λ (V.f i) ((DerivedCategory.singleFunctor _ 0).obj L)
  exact alpha_local _ W
    (fun i ↦ DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (V.X i)) Ab.{u + 1})
      (condensedRingObj Λ (V.X i))))
    (fun i ↦ L((V.f i)^*⟦Λ⟧))
    (fun f hf ↦ isIso_of_forall_isIso_leftDerivedUpperStar_map V f hf)
    (fun i ↦ by
      obtain ⟨n, ⟨e⟩⟩ := hV i
      have e' : (CondensedRing.upperStar Λ (V.f i)).obj L ≅
          ⨁ fun _ : Fin n ↦ 𝟙_ _ := by
        with_unfolding_all exact e
      exact ⟨n, ⟨localSingleFree Λ (V.f i) L e'⟩⟩)

private theorem localBeta
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hL : IsLisseCoefficientModule Λ L)
    (K W : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    IsIso (ihomTensorToIhom K W
      ((ihom ((DerivedCategory.singleFunctor _ 0).obj L)).obj (𝟙_ _))) := by
  obtain ⟨V, hV⟩ := hL
  have (i : V.I₀) : WeaklyEtale (V.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ V.mem₀ (.mk i)
  have (i : V.I₀) := isIso_ihomComparison_leftDerivedUpperStar_of_weaklyEtale
    Λ (V.f i) ((DerivedCategory.singleFunctor _ 0).obj L)
  have (i : V.I₀) := isIso_ihomComparison_leftDerivedUpperStar_of_weaklyEtale Λ (V.f i) K
  exact beta_local _ K W
    (fun i ↦ DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (V.X i)) Ab.{u + 1})
      (condensedRingObj Λ (V.X i))))
    (fun i ↦ L((V.f i)^*⟦Λ⟧))
    (fun f hf ↦ isIso_of_forall_isIso_leftDerivedUpperStar_map V f hf)
    (fun i ↦ by
      obtain ⟨n, ⟨e⟩⟩ := hV i
      have e' : (CondensedRing.upperStar Λ (V.f i)).obj L ≅
          ⨁ fun _ : Fin n ↦ 𝟙_ _ := by
        with_unfolding_all exact e
      exact ⟨n, ⟨localSingleFree Λ (V.f i) L e'⟩⟩)

private theorem tensorLisseFormula
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hL : IsLisseCoefficientModule Λ L)
    (K W : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    Nonempty ((ihom (K ⊗ (DerivedCategory.singleFunctor _ 0).obj L)).obj W ≅
      (ihom K).obj W ⊗ (DerivedCategory.singleFunctor _ 0).obj ((ihom L).obj (𝟙_ _))) := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let _ := (DerivedCategory.nonempty_braidedCategory A).some
  let P := (DerivedCategory.singleFunctor A 0).obj L
  let V := (ihom P).obj (𝟙_ _)
  have := localAlpha Λ L hL W
  have := localBeta Λ L hL K W
  obtain ⟨e⟩ := singleDual Λ L hL
  exact ⟨((MonoidalClosed.internalHom).mapIso (β_ P K).op).app W ≪≫
    MonoidalClosed.ihomCurryIso P K W ≪≫
    (ihom K).mapIso (asIso (ihomUnitTensorToIhom P W)).symm ≪≫
    (ihom K).mapIso (β_ V W) ≪≫
    (asIso (ihomTensorToIhom K W V)).symm ≪≫ tensorIso (Iso.refl _) e⟩

private theorem singleDual
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hL : IsLisseCoefficientModule Λ L) :
    Nonempty ((ihom ((DerivedCategory.singleFunctor _ 0).obj L)).obj (𝟙_ _) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((ihom L).obj (𝟙_ _))) := by
  have hraw : IsLocallyFree (condensedRingObj Λ X) L := by
    exact (isLocallyFree_iff L).mpr hL
  have ht : PreservesFiniteLimits (Mod.tensorLeft L) :=
    condensed_locally_free_tensor_preservesFiniteLimits _ L hraw
  have hr : PreservesFiniteLimits (tensorRight L) :=
    preservesFiniteLimits_of_natIso (Mod.relativeTensorRightIso L)
  have hl : PreservesFiniteLimits (tensorLeft L) :=
    preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight L).symm
  have hf : ObjectProperty.flat L :=
    ⟨⟨hl, inferInstanceAs (PreservesFiniteColimits (tensorLeft L))⟩,
      ⟨hr, inferInstanceAs (PreservesFiniteColimits (tensorRight L))⟩⟩
  have hc : PreservesColimitsOfSize.{u + 1, u + 1} (Mod.ihom L) :=
    condensed_locally_free_ihom_preservesColimits _ L hraw
  let e := ordinaryIhomIso Λ L
  have : PreservesLimits (ihom L) := (ihom.adjunction L).rightAdjoint_preservesLimits
  have : PreservesFiniteColimits (ihom L) :=
    preservesFiniteColimits_of_natIso e.symm
  let a := (ihom.adjunction L).mapDerivedCategoryAdjunction
  let b := a.ofNatIsoLeft (flatSingleTensorModel Λ L hf).symm
  let v := (ihom.adjunction ((DerivedCategory.singleFunctor _ 0).obj L)).rightAdjointUniq b
  exact ⟨v.app (𝟙_ _) ≪≫
    (ihom L).mapDerivedCategory.mapIso (DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
    ((ihom L).mapDerivedCategorySingleFunctor 0).app (𝟙_ _)⟩

private def flatSingleTensorModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hL : ObjectProperty.flat L) :
    letI := hL.tensorLeft.preservesFiniteLimits
    tensorLeft ((DerivedCategory.singleFunctor _ 0).obj L) ≅
      (tensorLeft L).mapDerivedCategory := by
  letI := hL.tensorLeft.preservesFiniteLimits
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let q := HomotopyCategory.quotient C (.up ℤ)
  let P := (HomologicalComplex.single C (.up ℤ) 0).obj L
  have hP : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat (q.obj P) :=
    (HomotopyCategory.kFlat_quotient_obj_iff P).2
      ((CochainComplex.kFlat_single_obj_iff_flat L 0).2 hL)
  have : IsIso (DerivedCategory.tensorLeftCounit (q.obj P)) :=
    DerivedCategory.isIso_tensorLeftCounit (q.obj P) hP
  let e : (DerivedCategory.singleFunctor C 0).obj L ≅ DerivedCategory.Qh.obj (q.obj P) :=
    (DerivedCategory.singleFunctorIsoCompQ C 0).app L ≪≫
      (DerivedCategory.quotientCompQhIso C).symm.app P
  let d : q ⋙ tensorLeft (q.obj P) ≅ tensorLeft P ⋙ q :=
    Functor.Monoidal.commTensorLeft q P
  let c : DerivedCategory.Q ⋙ tensorLeft ((DerivedCategory.singleFunctor C 0).obj L) ≅
      DerivedCategory.Q ⋙ (tensorLeft L).mapDerivedCategory :=
    Functor.isoWhiskerLeft DerivedCategory.Q ((curriedTensor _).mapIso e) ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft q (asIso (DerivedCategory.tensorLeftCounit (q.obj P))) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight d DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (tensorLeft P) (DerivedCategory.quotientCompQhIso C) ≪≫
      Functor.isoWhiskerRight
        (CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor C) L)
        DerivedCategory.Q ≪≫
      (tensorLeft L).mapDerivedCategoryFactors.symm
  exact (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) _).preimageIso c

private def ordinaryIhomIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ihom L ≅ Mod.ihom L :=
  (ihom.adjunction L).rightAdjointUniq
    ((Mod.ihomAdjunction L).ofNatIsoLeft
      (Mod.relativeTensorRightIso L ≪≫ (BraidedCategory.tensorLeftIsoTensorRight L).symm))

/-- The Verdier dual of a bounded constructible complex tensored with a lisse module is
canonically the tensor of its Verdier dual with the ordinary module dual.

(blueprint: lem-per-dual-lisse-tensor)
Source: latest blueprint, `part-weights-riemann-hypothesis/sec-fourier-transform/`
`sec-wft-perverse/sk-lem-wft-curve-heart/lem-per-dual-lisse-tensor.md` and its proof
(`lem-per-dual-lisse-tensor.proof.md`), paragraphs 1--3.

Proof (the four DAG steps):
1. Work in the ordinary uncompleted derived category over the pulled-back condensed
   coefficient ring. The module-object/ringed-site comparison preserves tensor, internal
   Hom, evaluation and restriction. Tensor--Hom currying gives
   `RHom(K ⊗ᴸ L, omega) ≅ RHom(K, RHom(L, omega))`.
2. On a pro-etale cover trivializing `L` as a finite free module, strict-perfect Hom
   identifies `RHom(L, omega)` with the corresponding finite power of `omega`.
   The ordinary-to-derived dual map is locally the identity, and the evaluation map
   `L`'s ordinary dual tensored with `omega` to `RHom(L, omega)` is locally the
   finite-free coordinate isomorphism. Hom restriction and tensor pullback preserve it.
3. Put `V = Hom(L, B)`. Transpose evaluation, using symmetry, to obtain
   `beta : RHom(K, omega) ⊗ᴸ V → RHom(K, V ⊗ᴸ omega)`. On a trivializing slice
   both sides are the same finite power of `RHom(K, omega)` and `beta` is the identity.
   This uses finite products and adjunction and requires no perfectness of `K`.
4. Exact restriction commutes with cohomology. The comparison cones vanish on the cover,
   so sheaf descent makes them vanish globally. Invert the first comparison inside
   `RHom(K, -)` and invert `beta`; their composition with currying is the asserted
   canonical isomorphism. This is compatible with all slice restrictions.
-/
theorem per_dual_lisse_tensor
    (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (hpell : p ≠ ell)
    (hbase : Finite k ∨ IsAlgClosed k)
    {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (K : ProEtale.BoundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left))
    (L : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left))
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) L) :
    letI : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom :=
      inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k))))
    letI : QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
      inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))
    letI : IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
      inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))
    letI : Fact (ringChar k).Prime :=
      ⟨by rw [ringChar.eq k p]; exact Fact.out⟩
    letI : Fact (ringChar k ≠ ell) :=
      ⟨by rw [ringChar.eq k p]; exact hpell⟩
    let aX : X ⟶ Over.mk (𝟙 (Spec (.of k))) := Over.homMk X.hom
    let c := exceptionalInverseImageCompactification aX
    ∀ (H : PreservesBoundedConstructiblePushforwards
        (Profinite.padicAlgClRingObj ell) k)
      (hAdj : (exceptionalInverseImageProperPushforward
        (Profinite.padicAlgClRingObj ell) aX
        (H (X := c.overObj) (Y := Over.mk (𝟙 (Spec (.of k)))) c.overG)).IsLeftAdjoint),
    letI := hAdj
    let omega :=
      (CondensedRing.boundedConstructibleUpperShriekOfRightAdjoint
        (Profinite.padicAlgClRingObj ell) ell aX
        (H (X := c.overObj) (Y := Over.mk (𝟙 (Spec (.of k)))) c.overG)).obj
        ⟨𝟙_ _, CondensedRing.boundedConstructible_tensorUnit
          (Profinite.padicAlgClRingObj ell) (Spec (.of k))⟩
    let DK :=
      (CondensedRing.derivedHom (Profinite.padicAlgClRingObj ell) X.left).obj (op K.obj)
    Nonempty
      (((CondensedRing.derivedHom (Profinite.padicAlgClRingObj ell) X.left).obj
          (op (((CondensedRing.derivedTensor (Profinite.padicAlgClRingObj ell) X.left).obj
            K.obj).obj ((DerivedCategory.singleFunctor _ 0).obj L)))).obj
          omega.obj ≅
      ((CondensedRing.derivedTensor (Profinite.padicAlgClRingObj ell) X.left).obj
          (DK.obj omega.obj)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((ihom L).obj (𝟙_ _)))) := by
  sorry

end AlgebraicGeometry.ProEtale
