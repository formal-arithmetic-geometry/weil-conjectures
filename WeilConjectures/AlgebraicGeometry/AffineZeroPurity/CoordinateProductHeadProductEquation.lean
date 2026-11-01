/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateProductsAgree.CoordinateProductComparison
import WeilConjectures.AlgebraicGeometry.EtaleSingleCochainMonoidal
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
import all WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorSymmetry
import all WeilConjectures.SixFunctors.Etale.Derived.Invertible
import all WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import all WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorFactorization
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-! # Product equation after support interchange

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered exterior product and even shifts
(blueprint: lem-pur-coordinate-product-head-product-equation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [local instance] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Sheaf.braidedCategory DerivedCategory.braidedCategory'
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity AffineLinePurity

private def swapLast {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] (A B D : C) : (A ⊗ B) ⊗ D ≅ (A ⊗ D) ⊗ B :=
  α_ A B D ≪≫ whiskerLeftIso A (β_ B D) ≪≫ (α_ A D B).symm

@[reassoc]
private theorem swapLast_naturality {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] {A B D A' B' D' : C}
    (f : A ⟶ A') (g : B ⟶ B') (h : D ⟶ D') :
    ((f ⊗ₘ g) ⊗ₘ h) ≫ (swapLast A' B' D').hom =
      (swapLast A B D).hom ≫ ((f ⊗ₘ h) ⊗ₘ g) := by
  simp only [swapLast, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
    Category.assoc]
  rw [associator_naturality_assoc, ← associator_inv_naturality]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp,
    Category.comp_id, BraidedCategory.braiding_naturality]

private theorem swapLast_self {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] (A B : C) (h : (β_ B B).hom = 𝟙 _) :
    (swapLast A B B).hom = 𝟙 _ := by
  simp only [swapLast, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, h,
    whiskerLeft_id, Category.id_comp, Iso.hom_inv_id]

@[reassoc]
private theorem lax_swapLast {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) [F.LaxBraided] (A B E : C) :
    Functor.LaxMonoidal.μ F A B ▷ F.obj E ≫ Functor.LaxMonoidal.μ F (A ⊗ B) E ≫
        F.map (swapLast A B E).hom =
      (swapLast (F.obj A) (F.obj B) (F.obj E)).hom ≫
        Functor.LaxMonoidal.μ F A E ▷ F.obj B ≫
          Functor.LaxMonoidal.μ F (A ⊗ E) B := by
  simp only [swapLast, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
    Functor.map_comp, Category.assoc]
  rw [Functor.LaxMonoidal.associativity_assoc,
    ← Functor.LaxMonoidal.μ_natural_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    Functor.LaxBraided.braided,
    MonoidalCategory.whiskerLeft_comp_assoc,
    Functor.LaxMonoidal.associativity_inv]

@[instance_reducible]
private def laxBraidedOfIso {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    {F G : C ⥤ D} [F.LaxBraided] [G.LaxMonoidal] (e : F ≅ G)
    (hμ : ∀ A B, Functor.LaxMonoidal.μ G A B =
      (e.inv.app A ⊗ₘ e.inv.app B) ≫ Functor.LaxMonoidal.μ F A B ≫ e.hom.app (A ⊗ B)) :
    G.LaxBraided where
  braided A B := by
    rw [hμ, hμ]
    simp only [Category.assoc]
    rw [← e.hom.naturality, Functor.LaxBraided.braided_assoc,
      BraidedCategory.braiding_naturality_assoc]

private theorem single_lax_braided
    {C : Type*} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C] :
    ∃ m : (DerivedCategory.singleFunctor C 0).LaxBraided,
      ∀ L M : C, letI := m
        Functor.LaxMonoidal.μ (DerivedCategory.singleFunctor C 0) L M =
          cupSingleTensorMap L M := by
  let H := HomotopyCategory.quotient C (.up ℤ)
  let : H.LaxBraided :=
    { braided K M := by
        change (𝟙 _) ≫ H.map (β_ K M).hom = H.map (β_ K M).hom ≫ 𝟙 _
        simp only [Category.id_comp, Category.comp_id] }
  let : (DerivedCategory.Qh (C := C)).LaxBraided :=
    { braided := fun K M ↦ (DerivedMonoidal.braiding_hom_μ DerivedCategory.Qh
        (HomotopyCategory.quasiIso C (.up ℤ)) K M).symm }
  let : (DerivedCategory.Q (C := C)).LaxBraided :=
    laxBraidedOfIso (DerivedCategory.quotientCompQhIso C) (fun _ _ ↦ rfl)
  obtain ⟨ms, hms⟩ := Etale.exists_singleCochainMonoidal (C := C)
  let := ms
  let : (CochainComplex.singleFunctor C 0).LaxBraided :=
    { __ := ms.toLaxMonoidal
      braided L M := by
        rw [hms, hms]
        exact (Etale.singleCochainTensorIso_symmetry L M).symm }
  let e := DerivedCategory.singleFunctorIsoCompQ C 0
  let m := Functor.LaxMonoidal.transport e.symm
  let := m
  let b := laxBraidedOfIso e.symm (fun _ _ ↦ rfl)
  refine ⟨b, ?_⟩
  intro L M
  change (letI := m; Functor.LaxMonoidal.μ (DerivedCategory.singleFunctor C 0) L M) = _
  rw [Functor.LaxMonoidal.transport_μ e.symm]
  simp only [Functor.LaxMonoidal.comp_μ]
  have hμ : Functor.LaxMonoidal.μ (CochainComplex.singleFunctor C 0) L M =
      (Etale.singleCochainTensorIso L M).hom := hms L M
  rw [hμ]
  simp only [cupSingleTensorMap, Etale.singleCochainTensorIso, Iso.symm_inv,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, Iso.trans_hom,
    Category.assoc, tensorIso_hom, e]
  rfl

private theorem tensor_epi {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] [MonoidalClosed C] {A B D E : C}
    (f : A ⟶ B) (g : D ⟶ E) [Epi f] [Epi g] : Epi (f ⊗ₘ g) := by
  have : Epi (f ▷ D) := (tensorRight D).map_epi f
  have : Epi (B ◁ g) := (tensorLeft B).map_epi g
  rw [MonoidalCategory.tensorHom_def]
  infer_instance

@[reassoc]
private theorem triple_normalized (P : PurityFiniteSetting.{u})
    {A B C X : Scheme.{u}} (s : A ⟶ X) (j : B ⟶ X) (i : C ⟶ X)
    [IsClosedImmersion s] [IsClosedImmersion j] [IsClosedImmersion i] :
    ((cupCoefficientRestriction P s ⊗ₘ cupCoefficientRestriction P j) ⊗ₘ
        cupCoefficientRestriction P i) ≫
      cupCoefficientMap P s j ▷
        ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant C)) ≫
        cupCoefficientMap P (cupIntersection s j) i =
      cupCoefficientMultiplication P X ▷ P.constant X ≫ cupCoefficientMultiplication P X ≫
        cupCoefficientRestriction P (cupIntersection (cupIntersection s j) i) := by
  have h₁ := (cupCoefficientMap_existsUnique P s j).exists.choose_spec
  have h₂ := (cupCoefficientMap_existsUnique P (cupIntersection s j) i).exists.choose_spec
  change (cupCoefficientRestriction P s ⊗ₘ cupCoefficientRestriction P j) ≫
    cupCoefficientMap P s j = _ at h₁
  change (cupCoefficientRestriction P (cupIntersection s j) ⊗ₘ
    cupCoefficientRestriction P i) ≫ cupCoefficientMap P (cupIntersection s j) i = _ at h₂
  rw [← tensorHom_id (cupCoefficientMap P s j),
    tensorHom_comp_tensorHom_assoc, Category.comp_id, h₁]
  rw [← Category.id_comp (cupCoefficientRestriction P i)]
  rw [← tensorHom_comp_tensorHom (cupCoefficientMultiplication P X)
    (𝟙 (P.constant X)) (cupCoefficientRestriction P (cupIntersection s j))
    (cupCoefficientRestriction P i)]
  simp only [tensorHom_id, Category.assoc]
  rw [h₂]

private theorem constant_self_braiding (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    (β_ (P.constant X) (P.constant X)).hom = 𝟙 _ := by
  let e : P.constant X ≅ 𝟙_ (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient)) := cupConstantIso P X
  have hu : (β_ (𝟙_ (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient)))
      (𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))).hom =
      𝟙 _ := by
    simp only [braiding_tensorUnit_left, unitors_equal, Iso.hom_inv_id]
  apply (cancel_mono (e.hom ⊗ₘ e.hom)).mp
  rw [← BraidedCategory.braiding_naturality, hu]
  simp only [Category.id_comp, Category.comp_id]

set_option maxHeartbeats 2000000 in
-- Matching the two iterated pullbacks also compares their canonical sheaf structures.
private theorem triple_coefficient_swap (P : PurityFiniteSetting.{u})
    {A B C X : Scheme.{u}} (s : A ⟶ X) (j : B ⟶ X) (i : C ⟶ X)
    [IsClosedImmersion s] [IsClosedImmersion j] [IsClosedImmersion i]
    (g : pullback (cupIntersection s j) i ⟶ pullback (cupIntersection s i) j)
    (hg : g ≫ cupIntersection (cupIntersection s i) j =
      cupIntersection (cupIntersection s j) i) :
    cupCoefficientMap P s j ▷
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant C)) ≫
        cupCoefficientMap P (cupIntersection s j) i =
      (swapLast
        ((lowerStar (ModuleCat.{u + 1} P.Coefficient) s).obj (P.constant A))
        ((lowerStar (ModuleCat.{u + 1} P.Coefficient) j).obj (P.constant B))
        ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant C))).hom ≫
      cupCoefficientMap P s i ▷
        ((lowerStar (ModuleCat.{u + 1} P.Coefficient) j).obj (P.constant B)) ≫
        cupCoefficientMap P (cupIntersection s i) j ≫
          P.functorialCupSupportMap true (cupIntersection (cupIntersection s i) j)
            (cupIntersection (cupIntersection s j) i) g hg := by
  let t :
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection (cupIntersection s i) j)).obj
        (P.constant (pullback (cupIntersection s i) j)) ⟶
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection (cupIntersection s j) i)).obj
        (P.constant (pullback (cupIntersection s j) i)) :=
    P.functorialCupSupportMap true (cupIntersection (cupIntersection s i) j)
      (cupIntersection (cupIntersection s j) i) g hg
  change cupCoefficientMap P s j ▷ _ ≫ cupCoefficientMap P (cupIntersection s j) i =
    (swapLast _ _ _).hom ≫ cupCoefficientMap P s i ▷ _ ≫
      cupCoefficientMap P (cupIntersection s i) j ≫ t
  have : Epi (cupCoefficientRestriction P s) := cupRestriction_epi P s
  have : Epi (cupCoefficientRestriction P j) := cupRestriction_epi P j
  have : Epi (cupCoefficientRestriction P i) := cupRestriction_epi P i
  have : Epi (cupCoefficientRestriction P s ⊗ₘ cupCoefficientRestriction P j) :=
    tensor_epi _ _
  have : Epi ((cupCoefficientRestriction P s ⊗ₘ cupCoefficientRestriction P j) ⊗ₘ
      cupCoefficientRestriction P i) := tensor_epi _ _
  apply (cancel_epi ((cupCoefficientRestriction P s ⊗ₘ cupCoefficientRestriction P j) ⊗ₘ
    cupCoefficientRestriction P i)).mp
  rw [swapLast_naturality_assoc,
    swapLast_self _ _ (constant_self_braiding P X), Category.id_comp]
  rw [triple_normalized, triple_normalized_assoc]
  have ht : cupCoefficientRestriction P (cupIntersection (cupIntersection s i) j) ≫ t =
      cupCoefficientRestriction P (cupIntersection (cupIntersection s j) i) :=
    (P.functorialCupSupportMap_existsUnique true
      (cupIntersection (cupIntersection s i) j) (cupIntersection (cupIntersection s j) i)
        g hg).choose_spec.1
  simp only [ht]

private theorem lax_triple {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] {A B E AB N : C}
    (f : A ⊗ B ⟶ AB) (g : AB ⊗ E ⟶ N) :
    (Functor.LaxMonoidal.μ F A B ≫ F.map f) ▷ F.obj E ≫
        (Functor.LaxMonoidal.μ F AB E ≫ F.map g) =
      Functor.LaxMonoidal.μ F A B ▷ F.obj E ≫
        Functor.LaxMonoidal.μ F (A ⊗ B) E ≫ F.map (f ▷ E ≫ g) := by
  simp only [comp_whiskerRight, Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp]

private theorem lax_triple_swap {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) [F.LaxBraided] {A B E AB AE N M : C}
    (f : A ⊗ B ⟶ AB) (g : AB ⊗ E ⟶ N)
    (p : A ⊗ E ⟶ AE) (q : AE ⊗ B ⟶ M) (t : M ⟶ N)
    (h : f ▷ E ≫ g = (swapLast A B E).hom ≫ p ▷ B ≫ q ≫ t) :
    (Functor.LaxMonoidal.μ F A B ≫ F.map f) ▷ F.obj E ≫
        (Functor.LaxMonoidal.μ F AB E ≫ F.map g) =
      (swapLast (F.obj A) (F.obj B) (F.obj E)).hom ≫
        (Functor.LaxMonoidal.μ F A E ≫ F.map p) ▷ F.obj B ≫
          (Functor.LaxMonoidal.μ F AE B ≫ F.map q) ≫ F.map t := by
  rw [lax_triple, h]
  simp only [F.map_comp, Category.assoc]
  rw [lax_swapLast_assoc]
  simp only [comp_whiskerRight, Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc]

private theorem single_triple_swap
    {C : Type*} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    {A B E AB AE N M : C}
    (f : A ⊗ B ⟶ AB) (g : AB ⊗ E ⟶ N)
    (p : A ⊗ E ⟶ AE) (q : AE ⊗ B ⟶ M) (t : M ⟶ N)
    (h : f ▷ E ≫ g = (swapLast A B E).hom ≫ p ▷ B ≫ q ≫ t) :
    cupDerivedCoefficientMap f ▷ (DerivedCategory.singleFunctor C 0).obj E ≫
        cupDerivedCoefficientMap g =
      (swapLast ((DerivedCategory.singleFunctor C 0).obj A)
        ((DerivedCategory.singleFunctor C 0).obj B)
        ((DerivedCategory.singleFunctor C 0).obj E)).hom ≫
        cupDerivedCoefficientMap p ▷ (DerivedCategory.singleFunctor C 0).obj B ≫
          cupDerivedCoefficientMap q ≫ (DerivedCategory.singleFunctor C 0).map t := by
  obtain ⟨m, hm⟩ := single_lax_braided (C := C)
  let := m
  simpa only [cupDerivedCoefficientMap, hm] using
    lax_triple_swap (DerivedCategory.singleFunctor C 0) f g p q t h

private theorem inverse_product_cancel {C : Type*} [Category C] [MonoidalCategory C]
    {A B E AB N U V W : C} (f : A ⊗ B ⟶ AB) (g : AB ⊗ E ⟶ N)
    [IsIso f] [IsIso g] (a : A ⟶ U) (b : B ⟶ V) (c : E ⟶ W) :
    (f ▷ E ≫ g) ≫ inv g ≫ ((inv f ≫ (a ⊗ₘ b)) ⊗ₘ c) =
      ((a ⊗ₘ b) ⊗ₘ c) := by
  have ht : ((inv f ≫ (a ⊗ₘ b)) ⊗ₘ c) =
      (inv f ▷ E) ≫ ((a ⊗ₘ b) ⊗ₘ c) := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom]
    simp only [Category.id_comp]
  rw [ht]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc,
    ← comp_whiskerRight_assoc, IsIso.hom_inv_id, id_whiskerRight, Category.id_comp]

private theorem inverse_cup_swap {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] {A B E AB AE N M U V : C}
    (f : A ⊗ B ⟶ AB) (g : AB ⊗ E ⟶ N)
    (p : A ⊗ E ⟶ AE) (q : AE ⊗ B ⟶ M) (t : M ⟶ N)
    [IsIso f] [IsIso g] [IsIso p] [IsIso q]
    (h : f ▷ E ≫ g = (swapLast A B E).hom ≫ p ▷ B ≫ q ≫ t)
    (a : A ⟶ U) (b : B ⟶ V) (c : E ⟶ V)
    (hβ : (β_ V V).hom = 𝟙 _) :
    t ≫ inv g ≫ ((inv f ≫ (a ⊗ₘ b)) ⊗ₘ c) =
      inv q ≫ ((inv p ≫ (a ⊗ₘ c)) ⊗ₘ b) := by
  have ht : (p ▷ B ≫ q) ≫ t = (swapLast A B E).inv ≫ (f ▷ E ≫ g) := by
    rw [h]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hn := swapLast_naturality a b c
  rw [swapLast_self _ _ hβ, Category.comp_id] at hn
  apply (cancel_epi (p ▷ B ≫ q)).mp
  rw [← Category.assoc _ t, ht, Category.assoc, inverse_product_cancel,
    inverse_product_cancel, hn]
  simp only [Iso.inv_hom_id_assoc]

private theorem cupComposite_zero {C : Type*} [Category C] [MonoidalCategory C]
    [HasShift C ℤ] [∀ K : C, ((curriedTensor C).obj K).CommShift ℤ]
    [∀ K : C, ((curriedTensor C).flip.obj K).CommShift ℤ]
    {L M N F G : C} (θ : L ⊗ M ⟶ N) (hθ : IsIso θ)
    (a : L ⟶ F) (b : M ⟶ G) :
    cupComposite θ hθ 0 0
        (a ≫ (shiftFunctorZero C ℤ).inv.app F)
        (b ≫ (shiftFunctorZero C ℤ).inv.app G) ≫
        (shiftFunctorZero C ℤ).hom.app (F ⊗ G) =
      @inv _ _ _ _ θ hθ ≫ (a ⊗ₘ b) := by
  unfold cupComposite cupTensorShiftIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.commShiftIso_zero, Functor.CommShift.isoZero_hom_app,
    shiftFunctorAdd_zero_add_inv_app, eqToHom_refl, Category.comp_id,
    Functor.map_comp, Category.assoc]
  dsimp only [curriedTensor, Functor.flip, Functor.id_obj, Functor.id_map]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [(shiftFunctorZero C ℤ).hom.naturality]
  simp only [Functor.id_map, Functor.id_obj, Iso.inv_hom_id_app_assoc, Category.comp_id]
  rw [← MonoidalCategory.tensorHom_def', tensorHom_comp_tensorHom]
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.id_obj, Category.comp_id]

private theorem cupZero_eq (P : PurityFiniteSetting.{u})
    {Z W X : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
    (i : Z ⟶ X) (j : W ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (F G : CupPlus P X)
    (a : (cupSingle P X).obj ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
      (P.constant Z)) ⟶ F.obj)
    (b : (cupSingle P X).obj ((lowerStar (ModuleCat.{u + 1} P.Coefficient) j).obj
      (P.constant W)) ⟶ G.obj) :
    cupZero P aX i j F G a b =
      @inv _ _ _ _ (cupDerivedCoefficientMap (hD := cupHasDerivedCategory P X)
        (hDM := cupMonoidal P X) (cupCoefficientMap P i j))
          (cupDerivedCoefficientMap_isIso P i j) ≫ (a ⊗ₘ b) := by
  exact cupComposite_zero _ _ a b

private theorem productOnSupport_cons (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) (i : Fin c)
    (is : List (Fin c)) :
    coordinateProductOnSupport P n B aB c (i :: is) =
      cupZero (setting P n) (towerBase aB c) (supportMap B c is) (inclusion B c i)
        ⟨target P n (iteratedAffineLine B c) is.length,
          target_plus P n _ (towerBase aB c) is.length⟩
        ⟨shiftedLine (setting P n) (iteratedAffineLine B c), boundary_plus P n _⟩
        (coordinateProductOnSupport P n B aB c is) (boundary P n B aB c i) := by
  unfold coordinateProductOnSupport product coordinateProductFold
  dsimp only [coordinateProductTransport, coordinateProductStart]
  erw [← Category.assoc, ← Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp, eqToHom_refl, Category.comp_id]
  rfl

set_option maxHeartbeats 2000000 in
-- The final specialization checks large canonical sheaf and derived-category types.
end AlgebraicGeometry.ProEtale.AffineZeroPurity
