/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.Coinduced.SequentialSemilinearCoinducedComplexes

/-! # Localization preserves the specified coinduced augmentation and difference

Source: Stacks 015F, 0941. The generic transposition calculation is adapted from
`CoefficientSequenceCanonicalAugmentation` and `CoefficientSequenceCanonicalDifferenceComponent`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe uC uD vC vD wC wD u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.SequentialDerived.Coinduced.LocalizationCompatibility

private theorem exact_unit
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G)
    (X : CochainComplex C ℤ) :
    a.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app X) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj X) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app X) := by
  let : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory := ⟨F.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q G.mapDerivedCategory := ⟨G.mapDerivedCategoryFactors.symm⟩
  exact (a.mapHomologicalComplex (.up ℤ)).localization_unit_app
    DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso D (.up ℤ))
    F.mapDerivedCategory G.mapDerivedCategory X

private theorem product_unit_comparison
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {D : ℕ → Type uD} [∀ n, Category.{vD} (D n)] [∀ n, Abelian (D n)]
    [∀ n, HasDerivedCategory.{wD} (D n)]
    (F : ∀ n, C ⥤ D n) (G : ∀ n, D n ⥤ C)
    [∀ n, (F n).Additive] [∀ n, (G n).Additive]
    [∀ n, PreservesFiniteLimits (F n)] [∀ n, PreservesFiniteColimits (F n)]
    [∀ n, PreservesFiniteLimits (G n)] [∀ n, PreservesFiniteColimits (G n)]
    (a : ∀ n, F n ⊣ G n)
    [HasCountableProducts (CochainComplex C ℤ)]
    [HasCountableProducts (DerivedCategory C)] (K : CochainComplex C ℤ) :
    DerivedCategory.Q.map
        (Pi.lift fun n ↦ ((a n).mapHomologicalComplex (.up ℤ)).unit.app K) ≫
      (Pi.lift fun n ↦ DerivedCategory.Q.map
        (Pi.π (fun n ↦ ((G n).mapHomologicalComplex (.up ℤ)).obj
          (((F n).mapHomologicalComplex (.up ℤ)).obj K)) n) ≫
        (G n).mapDerivedCategoryFactors.inv.app
          (((F n).mapHomologicalComplex (.up ℤ)).obj K) ≫
        (G n).mapDerivedCategory.map ((F n).mapDerivedCategoryFactors.inv.app K)) =
      Pi.lift (fun n ↦ (a n).mapExactDerivedCategory.unit.app
        (DerivedCategory.Q.obj K)) := by
  have hc := Pi.lift_π
    (fun n ↦ ((a n).mapHomologicalComplex (.up ℤ)).unit.app K)
  apply Pi.hom_ext
  intro n
  dsimp only [Functor.comp_obj] at hc ⊢
  simp only [Category.assoc, Pi.lift_π]
  rw [← DerivedCategory.Q.map_comp_assoc, hc n]
  exact (exact_unit (a n) K).symm

-- Localization preserves adjunction transposition through the exact-functor factors.
private theorem exact_hom_fac
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G)
    (K : CochainComplex C ℤ) (L : CochainComplex D ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L) :
    a.mapExactDerivedCategory.homEquiv _ _
        (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
        G.mapDerivedCategoryFactors.inv.app L := by
  have hu : a.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
    simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_unit_app]
    rfl
  rw [Adjunction.homEquiv_unit, hu, G.mapDerivedCategory.map_comp]
  simp only [Category.assoc, ← G.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [G.mapDerivedCategory.map_id, Category.id_comp]
  have hn := G.mapDerivedCategoryFactors.inv.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← Functor.map_comp]
  rfl

private theorem exact_hom_symm_fac
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G)
    (K : CochainComplex C ℤ) (L : CochainComplex D ℤ)
    (f : K ⟶ (G.mapHomologicalComplex (.up ℤ)).obj L) :
    (a.mapExactDerivedCategory.homEquiv _ _).symm
        (DerivedCategory.Q.map f ≫ G.mapDerivedCategoryFactors.inv.app L) =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map (((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm f) := by
  apply (a.mapExactDerivedCategory.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, exact_hom_fac, Equiv.apply_symm_apply]

private theorem exact_hom_symm_fac_post
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G)
    (K : CochainComplex C ℤ) (L : CochainComplex D ℤ) {Y : DerivedCategory D}
    (f : K ⟶ (G.mapHomologicalComplex (.up ℤ)).obj L)
    (g : DerivedCategory.Q.obj L ⟶ Y) :
    (a.mapExactDerivedCategory.homEquiv _ _).symm
        (DerivedCategory.Q.map f ≫ G.mapDerivedCategoryFactors.inv.app L ≫
          G.mapDerivedCategory.map g) =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map (((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm f) ≫
          g := by
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm,
    exact_hom_symm_fac, Category.assoc]

-- Transport an additive compatibility defect using the exact-functor comparison isomorphisms.
private theorem transport_difference
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : C ⥤ E) (R : E ⥤ D)
    [F.Additive] [G.Additive] [R.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (P K : CochainComplex C ℤ)
    (c : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶
      (F.mapHomologicalComplex (.up ℤ)).obj K)
    (b : (G.mapHomologicalComplex (.up ℤ)).obj P ⟶
      (G.mapHomologicalComplex (.up ℤ)).obj K)
    (tP : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶
      (R.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj P))
    (tK : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶
      (R.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj K))
    (dP : F.mapDerivedCategory.obj (DerivedCategory.Q.obj P) ⟶
      R.mapDerivedCategory.obj (G.mapDerivedCategory.obj (DerivedCategory.Q.obj P)))
    (dK : F.mapDerivedCategory.obj (DerivedCategory.Q.obj K) ⟶
      R.mapDerivedCategory.obj (G.mapDerivedCategory.obj (DerivedCategory.Q.obj K)))
    (hP : dP ≫ R.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
      R.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) =
      F.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map tP)
    (hK : dK ≫ R.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
      R.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) =
      F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map tK)
    (d : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶
      (R.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj K))
    (hd : d = c ≫ tK - tP ≫ (R.mapHomologicalComplex (.up ℤ)).map b) :
    F.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map d ≫
        R.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
        R.mapDerivedCategory.map (G.mapDerivedCategoryFactors.inv.app K) =
      (show F.mapDerivedCategory.obj (DerivedCategory.Q.obj P) ⟶
          R.mapDerivedCategory.obj (G.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) from
        (F.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map c ≫
          F.mapDerivedCategoryFactors.inv.app K) ≫ dK) -
      (show F.mapDerivedCategory.obj (DerivedCategory.Q.obj P) ⟶
          R.mapDerivedCategory.obj (G.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) from
        dP ≫ R.mapDerivedCategory.map
          (G.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map b ≫
            G.mapDerivedCategoryFactors.inv.app K)) := by
  rw [hd]
  apply (cancel_mono (R.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
    R.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K))).mp
  simp only [Category.assoc, Preadditive.sub_comp]
  rw [hK]
  simp only [Functor.map_sub, Functor.map_comp, Category.assoc,
    Preadditive.comp_sub, Preadditive.sub_comp]
  simp only [← R.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    Iso.inv_hom_id_app_assoc]
  erw [R.mapDerivedCategory.map_id]
  simp only [Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  erw [R.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app,
    Category.comp_id]
  have hn := R.mapDerivedCategoryFactors.hom.naturality b
  dsimp only [Functor.comp_map] at hn
  rw [hn, reassoc_of% hP]
  erw [Category.comp_id]




section Generic
attribute [local implicit_reducible] CoinducedSequence.product CoinducedSequence.relations
attribute [local implicit_reducible] Functor.mapHomologicalComplex
variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : ℕ → Type uD} [∀ n, Category.{vD} (D n)] [∀ n, Abelian (D n)]
  [∀ n, HasDerivedCategory.{wD} (D n)]
  (F : ∀ n, C ⥤ D n) (G : ∀ n, D n ⥤ C)
  [∀ n, (F n).Additive] [∀ n, (G n).Additive]
  [∀ n, PreservesFiniteLimits (F n)] [∀ n, PreservesFiniteColimits (F n)]
  [∀ n, PreservesFiniteLimits (G n)] [∀ n, PreservesFiniteColimits (G n)]
  (a : ∀ n, F n ⊣ G n)
  (S : ∀ n, D n ⥤ D (n + 1))
  [∀ n, (S n).Additive]
  [∀ n, PreservesFiniteLimits (S n)] [∀ n, PreservesFiniteColimits (S n)]
  (t : ∀ n, F (n + 1) ⟶ F n ⋙ S n)

local notation "Fc" =>
  (fun n ↦ CategoryTheory.Functor.mapHomologicalComplex (F n) (ComplexShape.up ℤ))
local notation "Gc" =>
  (fun n ↦ CategoryTheory.Functor.mapHomologicalComplex (G n) (ComplexShape.up ℤ))
local notation "ac" =>
  (fun n ↦ CategoryTheory.Adjunction.mapHomologicalComplex (ComplexShape.up ℤ) (a n))
local notation "Sc" =>
  (fun n ↦ CategoryTheory.Functor.mapHomologicalComplex (S n) (ComplexShape.up ℤ))
local notation "tc" =>
  (fun n ↦ CategoryTheory.NatTrans.mapHomologicalComplex (t n) (ComplexShape.up ℤ))
local notation "Fd" => (fun n ↦ CategoryTheory.Functor.mapDerivedCategory (F n))
local notation "Gd" => (fun n ↦ CategoryTheory.Functor.mapDerivedCategory (G n))
local notation "ad" => (fun n ↦ CategoryTheory.Adjunction.mapExactDerivedCategory (a n))
local notation "Sd" => (fun n ↦ CategoryTheory.Functor.mapDerivedCategory (S n))

private def localizedTransition (n : ℕ) :
    (F (n + 1)).mapDerivedCategory ⟶
      (F n).mapDerivedCategory ⋙ (S n).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    _ _ (F (n + 1)).mapDerivedCategory (F n ⋙ S n).mapDerivedCategory
    (Functor.whiskerRight ((t n).mapHomologicalComplex (ComplexShape.up ℤ)) DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso (F n) (S n)).hom

private theorem localizedTransition_fac (n : ℕ) (K : CochainComplex C ℤ) :
    (localizedTransition F S t n).app (DerivedCategory.Q.obj K) ≫
      (S n).mapDerivedCategory.map ((F n).mapDerivedCategoryFactors.hom.app K) ≫
      (S n).mapDerivedCategoryFactors.hom.app ((Fc n).obj K) =
    (F (n + 1)).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((tc n).app K) := by
  unfold localizedTransition
  dsimp only [NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors]
  rw [Localization.liftNatTrans_app]
  change ((F (n + 1)).mapDerivedCategoryFactors.hom.app K ≫
    DerivedCategory.Q.map ((tc n).app K) ≫
    (F n ⋙ S n).mapDerivedCategoryFactors.inv.app K) ≫
    (F n ⋙ S n).mapDerivedCategoryFactors.hom.app K = _
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

variable [HasCountableProducts (CochainComplex C ℤ)]
  [HasCountableProducts (DerivedCategory C)]

private def productComparison (K : CochainComplex C ℤ) :
    DerivedCategory.Q.obj (CoinducedSequence.product Fc Gc K) ⟶
      CoinducedSequence.product Fd Gd (DerivedCategory.Q.obj K) :=
  Pi.lift fun n ↦ DerivedCategory.Q.map
    (Pi.π (fun n ↦ (Gc n).obj ((Fc n).obj K)) n) ≫
      (G n).mapDerivedCategoryFactors.inv.app ((Fc n).obj K) ≫
      (G n).mapDerivedCategory.map ((F n).mapDerivedCategoryFactors.inv.app K)

private def relationsComparison (K : CochainComplex C ℤ) :
    DerivedCategory.Q.obj (CoinducedSequence.relations Fc Gc Sc K) ⟶
      CoinducedSequence.relations Fd Gd Sd (DerivedCategory.Q.obj K) :=
  Pi.lift fun n ↦ DerivedCategory.Q.map
    (Pi.π (fun n ↦ (Gc (n + 1)).obj ((Sc n).obj ((Fc n).obj K))) n) ≫
      (G (n + 1)).mapDerivedCategoryFactors.inv.app ((Sc n).obj ((Fc n).obj K)) ≫
      (G (n + 1)).mapDerivedCategory.map
        ((S n).mapDerivedCategoryFactors.inv.app ((Fc n).obj K) ≫
          (S n).mapDerivedCategory.map ((F n).mapDerivedCategoryFactors.inv.app K))

-- The component calculation is independent of the concrete coefficient-site functors.
private theorem product_difference_component (K : CochainComplex C ℤ) (n : ℕ) :
    ((ad (n + 1)).homEquiv _ _).symm
      (DerivedCategory.Q.map (CoinducedSequence.difference Fc Gc ac Sc tc K) ≫
        relationsComparison F G S K ≫ Pi.π
          (fun k ↦ (Gd (k + 1)).obj ((Sd k).obj ((Fd k).obj
            (DerivedCategory.Q.obj K)))) n) =
    ((ad (n + 1)).homEquiv _ _).symm
      (productComparison F G K ≫
        CoinducedSequence.difference Fd Gd ad Sd (localizedTransition F S t)
          (DerivedCategory.Q.obj K) ≫ Pi.π
          (fun k ↦ (Gd (k + 1)).obj ((Sd k).obj ((Fd k).obj
            (DerivedCategory.Q.obj K)))) n) := by
  let : ∀ n, (Gd n).Additive := fun n ↦ (ad n).right_adjoint_additive
  have hl := exact_hom_symm_fac (a (n + 1)) (CoinducedSequence.product Fc Gc K)
    ((Sc n).obj ((Fc n).obj K))
    (CoinducedSequence.difference Fc Gc ac Sc tc K ≫
      Pi.π (fun k ↦ (Gc (k + 1)).obj ((Sc k).obj ((Fc k).obj K))) n)
  have hr := CoinducedSequence.difference_component Fd Gd ad Sd
    (localizedTransition F S t) (productComparison F G K) n
  have hc (k : ℕ) :
      CoinducedSequence.components Fd Gd ad (productComparison F G K) k =
        (F k).mapDerivedCategoryFactors.hom.app (CoinducedSequence.product Fc Gc K) ≫
          DerivedCategory.Q.map (((ac k).homEquiv _ _).symm
            (Pi.π (fun j ↦ (Gc j).obj ((Fc j).obj K)) k)) ≫
          (F k).mapDerivedCategoryFactors.inv.app K := by
    unfold CoinducedSequence.components productComparison
    rw [Pi.lift_π]
    exact exact_hom_symm_fac_post (a k) (CoinducedSequence.product Fc Gc K)
      ((Fc k).obj K) (Pi.π (fun j ↦ (Gc j).obj ((Fc j).obj K)) k)
      ((F k).mapDerivedCategoryFactors.inv.app K)
  simp only [relationsComparison, Pi.lift_π]
  rw [← DerivedCategory.Q.map_comp_assoc]
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm, hl, hr]
  rw [hc (n + 1), hc n]
  have hd := CoinducedSequence.difference_component Fc Gc ac Sc tc
    (𝟙 (CoinducedSequence.product Fc Gc K)) n
  have h := transport_difference (F (n + 1)) (F n) (S n)
    (CoinducedSequence.product Fc Gc K) K
    (((ac (n + 1)).homEquiv _ _).symm
      (Pi.π (fun j ↦ (Gc j).obj ((Fc j).obj K)) (n + 1)))
    (((ac n).homEquiv _ _).symm (Pi.π (fun j ↦ (Gc j).obj ((Fc j).obj K)) n))
    ((tc n).app (CoinducedSequence.product Fc Gc K)) ((tc n).app K)
    ((localizedTransition F S t n).app
      (DerivedCategory.Q.obj (CoinducedSequence.product Fc Gc K)))
    ((localizedTransition F S t n).app (DerivedCategory.Q.obj K))
    (localizedTransition_fac F S t n (CoinducedSequence.product Fc Gc K))
    (localizedTransition_fac F S t n K)
    (((ac (n + 1)).homEquiv _ _).symm
      (CoinducedSequence.difference Fc Gc ac Sc tc K ≫
        Pi.π (fun k ↦ (Gc (k + 1)).obj ((Sc k).obj ((Fc k).obj K))) n))
    (by simpa only [CoinducedSequence.components, Category.id_comp] using hd)
  simpa only [Category.assoc] using h
end Generic

end SheafOfModules.SequentialDerived.Coinduced.LocalizationCompatibility

namespace SheafOfModules.SequentialDerived.Coinduced

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- The canonical product comparison identifies the ordinary and derived augmentations.
Source: Stacks 015F, 0941
(blueprint: lem-sf-sequential-semilinear-coinduced-compatibility).
Proof: project to each factor. The localized adjunction unit is the ordinary unit
followed by the inverse exact-functor comparisons, precisely the canonical projection. -/
theorem augmentation_comparison (K : CochainComplex (StrictRingSystem B) ℤ) :
    DerivedCategory.Q.map ((complexAugmentationNat B).app K) ≫
      (productComparison B).app K = augmentation B (DerivedCategory.Q.obj K) := by
  have h := LocalizationCompatibility.product_unit_comparison
    (systemEvaluation B) (SequenceCoinduced.rightExtension B) (SequenceCoinduced.adjunction B) K
  dsimp only [productComparison, productComparisonComponent, productFactorComparison,
    complexAugmentationNat, complexProductFunctor, complexEvaluation, complexRight,
    complexAdjunction, CoinducedSequence.augmentationNat,
    CoinducedSequence.productProjection, CoinducedSequence.augmentation, augmentation,
    derivedAdjunction, derivedRight, derivedSystemEvaluation,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at h ⊢
  exact h

/-- The canonical comparisons identify the actual signed adjacent differences.
Source: Stacks 015F, 0941
(blueprint: lem-sf-sequential-semilinear-coinduced-compatibility).
Proof: project to a relation factor and transpose by the exact derived adjunction.
Localization of transposition and the representative formula for the actual derived
transition identify both expressions componentwise. Negating gives the specified sign. -/
theorem difference_comparison (K : CochainComplex (StrictRingSystem B) ℤ) :
    DerivedCategory.Q.map ((complexDifferenceNat B).app K) ≫
      (relationsComparison B).app K =
        (productComparison B).app K ≫ difference B (DerivedCategory.Q.obj K) := by
  have hc (n : ℕ) := LocalizationCompatibility.product_difference_component
    (systemEvaluation B) (SequenceCoinduced.rightExtension B) (SequenceCoinduced.adjunction B)
    (fun n ↦ systemRestriction B (Nat.le_succ n))
    (fun n ↦ strictSystemTransition B (Nat.le_succ n)) K n
  have he : DerivedCategory.Q.map (CoinducedSequence.difference
      (complexEvaluation B) (complexRight B) (complexAdjunction B)
      (complexRestriction B) (complexTransition B) K) ≫
      (relationsComparison B).app K =
    (productComparison B).app K ≫ CoinducedSequence.difference
      (derivedSystemEvaluation B) (derivedRight B) (derivedAdjunction B)
      (Helper.adjacentRestriction B)
      (fun n ↦ systemDerivedTransition B (Nat.le_succ n)) (DerivedCategory.Q.obj K) := by
    apply Pi.hom_ext
    intro n
    apply ((derivedAdjunction B (n + 1)).homEquiv _ _).symm.injective
    have h := hc n
    dsimp only [LocalizationCompatibility.productComparison,
      LocalizationCompatibility.relationsComparison, LocalizationCompatibility.localizedTransition,
      productComparison, productComparisonComponent, productFactorComparison,
      relationsComparison, relationsComparisonComponent, relationsFactorComparison,
      complexEvaluation, complexRight, complexRestriction, complexTransition, complexAdjunction,
      derivedRight, derivedAdjunction, derivedSystemEvaluation, Helper.adjacentRestriction,
      systemDerivedTransition, CoinducedSequence.productProjection,
      CoinducedSequence.relationsProjection,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] at h ⊢
    simp only [Functor.map_comp, Functor.comp_map, Functor.comp_obj,
      Category.assoc] at h ⊢
    convert h using 1 <;> rfl
  change DerivedCategory.Q.map (-CoinducedSequence.difference _ _ _ _ _ K) ≫ _ = _
  rw [Functor.map_neg, Preadditive.neg_comp, he]
  simp only [difference, Preadditive.comp_neg]

end SheafOfModules.SequentialDerived.Coinduced
