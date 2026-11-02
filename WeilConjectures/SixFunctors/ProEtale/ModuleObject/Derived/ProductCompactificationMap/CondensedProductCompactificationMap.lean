/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module


public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
public import WeilConjectures.AlgebraicGeometry.OpenExternalTensor.OpenExternalTensorNormalization
public import WeilConjectures.AlgebraicGeometry.ProductCompactification.ProductCompactificationIdentity
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenBaseChangeArbitrary
public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients

import all Mathlib.Logic.Small.Defs
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Iso
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided

/-!
# Native condensed product compactification comparison

Source: latest blueprint, sk-thm-sf-kunneth-relative, Coherence (i), reduction to proper
morphisms (blueprint: lem-sf-condensed-product-compactification-map).
The helpers spell out the canonical open comparison and the forward word, on ordinary
uncompleted module derived categories. No coefficient-system realization is involved.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing.ProductCompactificationMap
open CompactificationReindexing
open AlgebraicGeometry.ProEtale.OpenExternalTensor (Diagram Triple)

attribute [local irreducible] upperStarFromPoint ProEtale.upperStar
  upperStar Mod.monoidalClosed

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarTensor leftDerivedUpperStarComp pullbackSquareComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Stable ordinary functor evaluation.
Source: canonical operations in the open-product construction
(blueprint: lem-sf-condensed-product-compactification-map). -/
@[implicit_reducible] def fobj {C E : Type*} [Category C] [Category E] (F : C ⥤ E)
    (K : C) : E := F.obj K

/-- Stable ordinary morphism mapping.
Source: canonical operations in the open-product construction
(blueprint: lem-sf-condensed-product-compactification-map). -/
@[implicit_reducible] def fmap {C E : Type*} [Category C] [Category E] (F : C ⥤ E)
    {K L : C} (f : K ⟶ L) : fobj F K ⟶ fobj F L := F.map f

/-- Stable tensor object.
Source: canonical operations in the open-product construction
(blueprint: lem-sf-condensed-product-compactification-map). -/
@[implicit_reducible] def objTensor {C : Type*} [Category C] [MonoidalCategory C]
    (K L : C) : C := K ⊗ L

/-- Stable tensor morphism.
Source: canonical operations in the open-product construction
(blueprint: lem-sf-condensed-product-compactification-map). -/
@[implicit_reducible] def mapTensor {C : Type*} [Category C] [MonoidalCategory C] {K K' L L' : C}
    (f : K ⟶ K') (g : L ⟶ L') : objTensor K L ⟶ objTensor K' L' := f ⊗ₘ g

local infixr:70 " ⊗ₛ " => objTensor
local infixr:70 " ⊗ₛₘ " => mapTensor

/-- The unchanged canonical pullback.
Source: canonical operations in the open-product construction
(blueprint: lem-sf-condensed-product-compactification-map). -/
@[implicit_reducible] def pull {X Y : Scheme.{u}} (f : X ⟶ Y) : D Λ Y ⥤ D Λ X := P Λ f

/-- The unchanged canonical open extension.
Source: canonical operations in the open-product construction
(blueprint: lem-sf-condensed-product-compactification-map). -/
@[implicit_reducible] def shriek {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    D Λ X ⥤ D Λ Y := J Λ f

/-- The unchanged canonical open adjunction.
Source: canonical operations in the open-product construction
(blueprint: lem-sf-condensed-product-compactification-map). -/
@[implicit_reducible] def adj {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    shriek Λ f ⊣ pull Λ f := oa Λ f

private instance pullLaxMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pull Λ f).LaxMonoidal := inferInstanceAs (P Λ f).LaxMonoidal

private instance adjUnitIsIso {U Z : Scheme.{u}} (i : U ⟶ Z)
    [IsOpenImmersion i] : IsIso (adj Λ i).unit :=
  CompactificationReindexing.openUnit_isIso Λ i

/-- The unit component with its object endpoints explicit.
Source: adjunction unit in the open-product normalization
(blueprint: lem-sf-condensed-product-compactification-map). -/
@[implicit_reducible] def unitComponent {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (N : C) :
    N ⟶ fobj R (fobj L N) := a.unit.app N

/-- A natural transformation between composites, evaluated with explicit endpoints.
Source: the component maps in the canonical base-change construction
(blueprint: lem-sf-condensed-product-compactification-map). -/
@[implicit_reducible] def compositeComponent {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {I : C ⥤ D}
    (t : F ⋙ G ⟶ H ⋙ I) (N : A) : fobj G (fobj F N) ⟶ fobj I (fobj H N) :=
  t.app N

/-- The section unit of the canonical open adjunction, with explicit object
endpoints. Source: unit normalization in the open-product construction
(blueprint: lem-sf-condensed-product-compactification-map). -/
def openUnit {U Z : Scheme.{u}} (i : U ⟶ Z) [IsOpenImmersion i] (K : D Λ U) :
    K ⟶ fobj (pull Λ i) (fobj (shriek Λ i) K) := unitComponent (adj Λ i) K

/-- The canonical open base-change component.
Source: beta in the open-product construction
(blueprint: lem-sf-condensed-product-compactification-map). -/
def betaMap {A B A' B' : Scheme.{u}}
    {i : A ⟶ B} {i' : A' ⟶ B'} {w : A' ⟶ A} {v : B' ⟶ B}
    [IsOpenImmersion i] [IsOpenImmersion i'] (sq : IsPullback w i' i v)
    (K : D Λ A) : fobj (pull Λ v) (fobj (shriek Λ i) K) ⟶
      (shriek Λ i').obj (fobj (pull Λ w) K) := compositeComponent (beta Λ sq).hom K

/-- The inverse canonical pullback-square component.
Source: the pullback square in the open-product construction
(blueprint: lem-sf-condensed-product-compactification-map). -/
def pullSquareInv {A B A' B' : Scheme.{u}}
    {i : A ⟶ B} {i' : A' ⟶ B'} {w : A' ⟶ A} {v : B' ⟶ B}
    (sq : CommSq w i' i v) (K : D Λ B) :
    fobj (pull Λ w) (fobj (pull Λ i) K) ⟶ (pull Λ i').obj (fobj (pull Λ v) K) :=
  compositeComponent (pullbackSquareComparison Λ sq).inv K

/-- The native pullback compositor evaluated at an object, with its nested
object endpoints explicit. Source: canonical pullback composition
(blueprint: lem-sf-condensed-product-compactification-map). -/
def compIsoComponent {U V Z : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ Z)
    (N : D Λ Z) :
    fobj (pull Λ (i ≫ j)) N ≅ fobj (pull Λ i) (fobj (pull Λ j) N) :=
  (leftDerivedUpperStarComp Λ i j).app N

/-- The pullback composition identification with scalar endpoints.
Source: projection-composition in the open-product construction
(blueprint: lem-sf-condensed-product-compactification-map). -/
def compTo {U V Z : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ Z) (h : U ⟶ Z)
    (e : i ≫ j = h) (N : D Λ Z) :
    fobj (pull Λ i) (fobj (pull Λ j) N) ≅ fobj (pull Λ h) N :=
  (compIsoComponent Λ i j N).symm ≪≫
    eqToIso (congrArg (fun f ↦ fobj (pull Λ f) N) e)

/-- Evaluation of the functor-level equality transport is the scalar transport.
This certifies that the projection identifications in the displayed word are unchanged. -/
private theorem compTo_native_formula {U V Z : Scheme.{u}}
    (i : U ⟶ V) (j : V ⟶ Z) (h : U ⟶ Z) (e : i ≫ j = h) (N : D Λ Z) :
    compTo Λ i j h e N =
      ((leftDerivedUpperStarComp Λ i j).symm ≪≫
        eqToIso (congrArg (P Λ) e)).app N := by
  subst h
  simp only [compTo, compIsoComponent, eqToIso_refl, Iso.trans_refl]
  rfl


/-- Native tensor helper for the open-product comparison.
Source: the displayed open-product construction, blueprint Coherence (i)
(blueprint: lem-sf-condensed-product-compactification-map). -/
def tensor (X : Scheme.{u}) (K L : D Λ X) : D Λ X := K ⊗ₛ L

/-- Native tensorMap helper for the open-product comparison.
Source: the displayed open-product construction, blueprint Coherence (i)
(blueprint: lem-sf-condensed-product-compactification-map). -/
def tensorMap (X : Scheme.{u}) {K K' L L' : D Λ X}
    (a : K ⟶ K') (b : L ⟶ L') :
    tensor Λ X K L ⟶ tensor Λ X K' L' := a ⊗ₛₘ b

/-- Native tensorIsoMap helper for the open-product comparison.
Source: the displayed open-product construction, blueprint Coherence (i)
(blueprint: lem-sf-condensed-product-compactification-map). -/
def tensorIsoMap (X : Scheme.{u}) {K K' L L' : D Λ X}
    (a : K ≅ K') (b : L ≅ L') : K ⊗ₛ L ≅ K' ⊗ₛ L' := tensorIso a b

/-- Native sigma helper for the open-product comparison.
Source: the displayed open-product construction, blueprint Coherence (i)
(blueprint: lem-sf-condensed-product-compactification-map). -/
def sigma (X : Scheme.{u}) (K L : D Λ X) : K ⊗ₛ L ⟶ L ⊗ₛ K :=
  (@BraidedCategory.braiding _ _ _ (DerivedCategory.braidedCategory' _) K L).hom

/-- Native tensorPullIso helper for the open-product comparison.
Source: the displayed open-product construction, blueprint Coherence (i)
(blueprint: lem-sf-condensed-product-compactification-map). -/
def tensorPullIso {X Y : Scheme.{u}} (f : X ⟶ Y) (K L : D Λ Y) :
    fobj (pull Λ f) (K ⊗ₛ L) ≅ fobj (pull Λ f) K ⊗ₛ fobj (pull Λ f) L :=
  ((leftDerivedUpperStarTensorIso Λ f).app K).app L

/-- Native square helper for the open-product comparison.
Source: the displayed open-product construction, blueprint Coherence (i)
(blueprint: lem-sf-condensed-product-compactification-map). -/
def square {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Z)
    (h : T ⟶ Y) (i : Y ⟶ Z) (e : f ≫ g = h ≫ i) :
    pull Λ g ⋙ pull Λ f ≅ pull Λ i ⋙ pull Λ h :=
  (leftDerivedUpperStarComp Λ f g).symm ≪≫
    eqToIso (congrArg (pull Λ) e) ≪≫ leftDerivedUpperStarComp Λ h i

/-- The scalar inverse pullback-square comparison.
Source: the displayed restriction formula
(blueprint: lem-sf-condensed-product-compactification-map). -/
def squareInv {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Z)
    (h : T ⟶ Y) (i : Y ⟶ Z) (e : f ≫ g = h ≫ i) (N : D Λ Z) :
    fobj (pull Λ h) (fobj (pull Λ i) N) ⟶
      fobj (pull Λ f) (fobj (pull Λ g) N) :=
  compositeComponent (square Λ f g h i e).inv N

/-- Native shriekCongr helper for the open-product comparison.
Source: the displayed open-product construction, blueprint Coherence (i)
(blueprint: lem-sf-condensed-product-compactification-map). -/
def shriekCongr {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) : shriek Λ f ≅ shriek Λ g :=
  eqToIso (by cases h; rfl)

/-- Native gamma helper for the open-product comparison.
Source: the displayed open-product construction, blueprint Coherence (i)
(blueprint: lem-sf-condensed-product-compactification-map). -/
def gamma {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (K : D Λ X) (L : D Λ Y) :
    fobj (shriek Λ j) K ⊗ₛ L ⟶
      fobj (shriek Λ j) (K ⊗ₛ fobj (pull Λ j) L) :=
  inv (openImmersionProjectionComparison Λ j K L)

/-- Native rho helper for the open-product comparison.
Source: the displayed open-product construction, blueprint Coherence (i)
(blueprint: lem-sf-condensed-product-compactification-map). -/
def rho {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (K : D Λ Y) (L : D Λ X) :
    K ⊗ₛ fobj (shriek Λ j) L ⟶
      fobj (shriek Λ j) (fobj (pull Λ j) K ⊗ₛ L) :=
  sigma Λ Y K (fobj (shriek Λ j) L) ≫ gamma Λ j L K ≫
    fmap (shriek Λ j) (sigma Λ X L (fobj (pull Λ j) K))

private theorem fmap_comp {C E : Type*} [Category C] [Category E] (F : C ⥤ E)
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) :
    fmap F (f ≫ g) = fmap F f ≫ fmap F g := F.map_comp f g

private theorem fmap_id {C E : Type*} [Category C] [Category E] (F : C ⥤ E) (A : C) :
    fmap F (𝟙 A) = 𝟙 (fobj F A) := F.map_id A

private theorem raw_inv_projection_unit
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [R.LaxMonoidal] (a : L ⊣ R) (K : C) (N : D)
    [IsIso (a.projectionComparison K N)] :
    ((a.unit.app K ⊗ₘ 𝟙 (R.obj N)) ≫
      Functor.LaxMonoidal.μ R (L.obj K) N) ≫
      R.map (inv (a.projectionComparison K N)) = a.unit.app (K ⊗ R.obj N) := by
  have h : a.unit.app (K ⊗ R.obj N) ≫ R.map (a.projectionComparison K N) =
      (a.unit.app K ⊗ₘ 𝟙 (R.obj N)) ≫ Functor.LaxMonoidal.μ R (L.obj K) N := by
    calc
      _ = a.homEquiv _ _ (a.projectionComparison K N) := rfl
      _ = _ := by
        rw [Adjunction.projectionComparison, Equiv.apply_symm_apply]
        simp
  rw [← h]
  simp only [Category.assoc, ← R.map_comp, IsIso.hom_inv_id]
  rw [R.map_id]
  exact Category.comp_id _


private theorem raw_inverse_mate_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : A ⥤ B} {R₂ : B ⥤ A}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) {G : C ⥤ A} {H : D ⥤ B}
    (θ : TwoSquare R₁ H G R₂) (e : L₁ ⋙ H ≅ G ⋙ L₂)
    (he : e.inv = ((mateEquiv a₁ a₂).symm θ).natTrans) (K : C) :
    G.map (a₁.unit.app K) ≫ θ.app (L₁.obj K) ≫ R₂.map (e.hom.app K) =
      a₂.unit.app (G.obj K) := by
  have h := unit_mateEquiv_symm a₁ a₂ θ K
  change G.map (a₁.unit.app K) ≫ θ.app (L₁.obj K) =
    a₂.unit.app (G.obj K) ≫ R₂.map
      (((mateEquiv a₁ a₂).symm θ).natTrans.app K) at h
  rw [← he] at h
  rw [← Category.assoc, h, Category.assoc, ← R₂.map_comp]
  simp


private theorem raw_swapped_projection_unit
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    [SymmetricCategory C] [BraidedCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [R.LaxMonoidal] (a : L ⊣ R)
    (hβ : ∀ X Y, Functor.LaxMonoidal.μ R X Y ≫ R.map (β_ X Y).hom =
      (β_ (R.obj X) (R.obj Y)).hom ≫ Functor.LaxMonoidal.μ R Y X)
    (K : D) (N : C) [IsIso (a.projectionComparison N K)] :
    ((𝟙 (R.obj K) ⊗ₘ a.unit.app N) ≫ Functor.LaxMonoidal.μ R K (L.obj N)) ≫
      R.map ((β_ K (L.obj N)).hom ≫ inv (a.projectionComparison N K) ≫
        L.map (β_ N (R.obj K)).hom) = a.unit.app (R.obj K ⊗ N) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (hβ K (L.obj N))]
  rw [reassoc_of% (BraidedCategory.braiding_naturality
    (𝟙 (R.obj K)) (a.unit.app N))]
  rw [reassoc_of% (raw_inv_projection_unit a N K)]
  rw [a.unit_naturality]
  rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

private theorem raw_inverse_square {C : Type*} [Category C] {A B A' B' : C}
    (a : A ≅ A') (b : B ≅ B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : f ≫ b.hom = a.hom ≫ g) : a.inv ≫ f = g ≫ b.inv := by
  apply (cancel_mono b.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]


private theorem raw_normalized_transport_explicit
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {N N' : C} {E : D}
    (f : E ⟶ L.obj N) (r : N ⟶ R.obj E)
    (h : r ≫ R.map f = a.unit.app N) (c : N ≅ N') :
    (c.inv ≫ r) ≫ R.map (f ≫ L.map c.hom) = a.unit.app N' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h, a.unit_naturality]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]


private theorem raw_left_unit_explicit
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    (K : C) (N X : D) (α : K ⟶ R.obj X) (β : X ⟶ L.obj K)
    (hα : α ≫ R.map β = a.unit.app K)
    (m : R.obj X ⊗ R.obj N ⟶ R.obj (X ⊗ N))
    (m' : R.obj (L.obj K) ⊗ R.obj N ⟶ R.obj (L.obj K ⊗ N))
    (hm : m ≫ R.map (β ⊗ₘ 𝟙 N) = (R.map β ⊗ₘ 𝟙 (R.obj N)) ≫ m')
    (z : L.obj K ⊗ N ⟶ L.obj (K ⊗ R.obj N))
    (hz : ((a.unit.app K ⊗ₘ 𝟙 (R.obj N)) ≫ m') ≫ R.map z =
      a.unit.app (K ⊗ R.obj N)) :
    ((α ⊗ₘ 𝟙 (R.obj N)) ≫ m) ≫ R.map ((β ⊗ₘ 𝟙 N) ≫ z) =
      a.unit.app (K ⊗ R.obj N) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc m, hm]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, hα]
  exact hz


private theorem raw_right_unit_explicit
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    (K : D) (N : C) (X : D) (α : N ⟶ R.obj X) (β : X ⟶ L.obj N)
    (hα : α ≫ R.map β = a.unit.app N)
    (m : R.obj K ⊗ R.obj X ⟶ R.obj (K ⊗ X))
    (m' : R.obj K ⊗ R.obj (L.obj N) ⟶ R.obj (K ⊗ L.obj N))
    (hm : m ≫ R.map (𝟙 K ⊗ₘ β) = (𝟙 (R.obj K) ⊗ₘ R.map β) ≫ m')
    (z : K ⊗ L.obj N ⟶ L.obj (R.obj K ⊗ N))
    (hz : ((𝟙 (R.obj K) ⊗ₘ a.unit.app N) ≫ m') ≫ R.map z =
      a.unit.app (R.obj K ⊗ N)) :
    ((𝟙 (R.obj K) ⊗ₘ α) ≫ m) ≫ R.map ((𝟙 K ⊗ₘ β) ≫ z) =
      a.unit.app (R.obj K ⊗ N) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc m, hm]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, hα]
  exact hz


private theorem raw_left_unit_iso_explicit
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    (K : C) (N X : D) (α : K ⟶ R.obj X) (β : X ⟶ L.obj K)
    (hα : α ≫ R.map β = a.unit.app K)
    (m : R.obj X ⊗ R.obj N ⟶ R.obj (X ⊗ N))
    (m' : R.obj (L.obj K) ⊗ R.obj N ⟶ R.obj (L.obj K ⊗ N))
    (hm : m ≫ R.map (β ⊗ₘ 𝟙 N) = (R.map β ⊗ₘ 𝟙 (R.obj N)) ≫ m')
    (z : L.obj K ⊗ N ⟶ L.obj (K ⊗ R.obj N))
    (hz : ((a.unit.app K ⊗ₘ 𝟙 (R.obj N)) ≫ m') ≫ R.map z =
      a.unit.app (K ⊗ R.obj N)) {N' : C} (c : R.obj N ≅ N') :
    ((𝟙 K ⊗ₘ c.inv) ≫ (α ⊗ₘ 𝟙 (R.obj N)) ≫ m) ≫
      R.map ((β ⊗ₘ 𝟙 N) ≫ z ≫ L.map (𝟙 K ⊗ₘ c.hom)) =
      a.unit.app (K ⊗ N') := by
  have h := raw_left_unit_explicit a K N X α β hα m m' hm z hz
  have ht := raw_normalized_transport_explicit a _ _ h (tensorIso (Iso.refl K) c)
  simpa only [tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv,
    Functor.map_comp, Category.assoc] using ht


private theorem raw_right_unit_iso_explicit
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    (K : D) (N : C) (X : D) (α : N ⟶ R.obj X) (β : X ⟶ L.obj N)
    (hα : α ≫ R.map β = a.unit.app N)
    (m : R.obj K ⊗ R.obj X ⟶ R.obj (K ⊗ X))
    (m' : R.obj K ⊗ R.obj (L.obj N) ⟶ R.obj (K ⊗ L.obj N))
    (hm : m ≫ R.map (𝟙 K ⊗ₘ β) = (𝟙 (R.obj K) ⊗ₘ R.map β) ≫ m')
    (z : K ⊗ L.obj N ⟶ L.obj (R.obj K ⊗ N))
    (hz : ((𝟙 (R.obj K) ⊗ₘ a.unit.app N) ≫ m') ≫ R.map z =
      a.unit.app (R.obj K ⊗ N)) {K' : C} (c : R.obj K ≅ K') :
    ((c.inv ⊗ₘ α) ≫ m) ≫
      R.map ((𝟙 K ⊗ₘ β) ≫ z ≫ L.map (c.hom ⊗ₘ 𝟙 N)) =
      a.unit.app (K' ⊗ N) := by
  have h := raw_right_unit_explicit a K N X α β hα m m' hm z hz
  have ht := raw_normalized_transport_explicit a _ _ h (tensorIso c (Iso.refl N))
  simpa only [tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv,
    Functor.map_comp, ← Category.assoc, tensor_id_comp_id_tensor] using ht


private theorem raw_tensor_composition_explicit
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (R : C ⥤ D) (S : D ⥤ E)
    (A B : C) (A' B' : D) (A'' B'' : E)
    (α : A' ⟶ R.obj A) (ci : B' ⟶ R.obj B) (di : A'' ⟶ S.obj A')
    (β : B'' ⟶ S.obj B')
    (m : R.obj A ⊗ R.obj B ⟶ R.obj (A ⊗ B))
    (n₀ : S.obj A' ⊗ S.obj B' ⟶ S.obj (A' ⊗ B'))
    (n₁ : S.obj A' ⊗ S.obj (R.obj B) ⟶ S.obj (A' ⊗ R.obj B))
    (n₂ : S.obj (R.obj A) ⊗ S.obj (R.obj B) ⟶ S.obj (R.obj A ⊗ R.obj B))
    (h₁ : n₀ ≫ S.map (𝟙 A' ⊗ₘ ci) = (𝟙 (S.obj A') ⊗ₘ S.map ci) ≫ n₁)
    (h₂ : n₁ ≫ S.map (α ⊗ₘ 𝟙 (R.obj B)) = (S.map α ⊗ₘ 𝟙 (S.obj (R.obj B))) ≫ n₂) :
    ((di ⊗ₘ β) ≫ n₀) ≫ S.map ((𝟙 A' ⊗ₘ ci) ≫ (α ⊗ₘ 𝟙 (R.obj B)) ≫ m) =
      ((di ≫ S.map α) ⊗ₘ (β ≫ S.map ci)) ≫ n₂ ≫ S.map m := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc n₀, h₁]
  simp only [Category.assoc]
  rw [← Category.assoc n₁, h₂]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id,
    Category.id_comp]


private theorem raw_tensor_swap_explicit
    {C : Type*} [Category C] [MonoidalCategory C]
    {A B A' B' E F : C} (f : A ⟶ A') (g : B ⟶ B')
    (s₀ : A ⊗ B ⟶ B ⊗ A) (s₁ : A' ⊗ B' ⟶ B' ⊗ A')
    (m : A' ⊗ B' ⟶ E) (n : B' ⊗ A' ⟶ F) (s : E ⟶ F)
    (hn : s₀ ≫ (g ⊗ₘ f) = (f ⊗ₘ g) ≫ s₁)
    (hm : m ≫ s = s₁ ≫ n) :
    s₀ ≫ ((g ⊗ₘ f) ≫ n) = ((f ⊗ₘ g) ≫ m) ≫ s := by
  rw [← Category.assoc, hn, Category.assoc, ← hm, ← Category.assoc]


private theorem raw_normalized_of_presentations
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {N : C} {E : D}
    {r₀ : N ⟶ R.obj E} {f₀ : E ⟶ L.obj N}
    (h : r₀ ≫ R.map f₀ = a.unit.app N)
    (r : N ⟶ R.obj E) (f : E ⟶ L.obj N) (hr : r₀ = r) (hf : f₀ = f) :
    r ≫ R.map f = a.unit.app N := by
  rw [← hr, ← hf]
  exact h


/-- Scalar component of the specified open compositor.
Source: normalized open composition in the product comparison
(blueprint: lem-sf-condensed-product-compactification-map). -/
def openFactorComponent {U V Z : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ Z)
    (h : U ⟶ Z) [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion h]
    (e : i ≫ j = h) (K : D Λ U) :
    fobj (shriek Λ j) (fobj (shriek Λ i) K) ≅ fobj (shriek Λ h) K :=
  (CompactSupportComposition.openFactor Λ i j h e).app K

private theorem native_mu {U Z : Scheme.{u}} (i : U ⟶ Z) (A B : D Λ Z) :
    Functor.LaxMonoidal.μ (pull Λ i) A B = (tensorPullIso Λ i A B).inv := by
  rfl

private theorem native_projection {U Z : Scheme.{u}} (i : U ⟶ Z)
    [IsOpenImmersion i] (A : D Λ U) (B : D Λ Z) :
    (adj Λ i).projectionComparison A B = openImmersionProjectionComparison Λ i A B := by
  rfl

private theorem inv_projection_unit
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [R.LaxMonoidal] (a : L ⊣ R) (K : C) (N : D)
    [IsIso (a.projectionComparison K N)] :
    ((unitComponent a K ⊗ₛₘ 𝟙 (fobj R N)) ≫
      Functor.LaxMonoidal.μ R (fobj L K) N) ≫
      fmap R (inv (a.projectionComparison K N)) = unitComponent a (K ⊗ₛ fobj R N) := by
  simpa only [fobj, fmap, objTensor, mapTensor, unitComponent,
    compositeComponent] using
    (@raw_inv_projection_unit C D _ _ _ _ L R _ a K N _)

private theorem inverse_mate_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : A ⥤ B} {R₂ : B ⥤ A}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) {G : C ⥤ A} {H : D ⥤ B}
    (θ : TwoSquare R₁ H G R₂) (e : L₁ ⋙ H ≅ G ⋙ L₂)
    (he : e.inv = ((mateEquiv a₁ a₂).symm θ).natTrans) (K : C) :
    fmap G (unitComponent a₁ K) ≫ θ.app (fobj L₁ K) ≫ fmap R₂ (compositeComponent e.hom K) =
      unitComponent a₂ (fobj G K) := by
  simpa only [fobj, fmap, objTensor, mapTensor, unitComponent,
    compositeComponent] using
    (@raw_inverse_mate_unit A B C D _ _ _ _ L₁ R₁ L₂ R₂ a₁ a₂ G H θ e he K)

private theorem swapped_projection_unit
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    [SymmetricCategory C] [BraidedCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [R.LaxMonoidal] (a : L ⊣ R)
    (hβ : ∀ X Y, Functor.LaxMonoidal.μ R X Y ≫ fmap R (β_ X Y).hom =
      (β_ (fobj R X) (fobj R Y)).hom ≫ Functor.LaxMonoidal.μ R Y X)
    (K : D) (N : C) [IsIso (a.projectionComparison N K)] :
    ((𝟙 (fobj R K) ⊗ₛₘ unitComponent a N) ≫ Functor.LaxMonoidal.μ R K (fobj L N)) ≫
      fmap R ((β_ K (fobj L N)).hom ≫ inv (a.projectionComparison N K) ≫
        fmap L (β_ N (fobj R K)).hom) = unitComponent a (fobj R K ⊗ₛ N) := by
  simpa only [fobj, fmap, objTensor, mapTensor, unitComponent,
    compositeComponent] using
    (@raw_swapped_projection_unit C D _ _ _ _ _ _ L R _ a hβ K N _)

private theorem sigma_twice (Z : Scheme.{u}) (A B : D Λ Z) :
    sigma Λ Z A B ≫ sigma Λ Z B A = 𝟙 _ := by
  let : SymmetricCategory (D Λ Z) := DerivedCategory.symmetricCategory _
  exact SymmetricCategory.symmetry A B

private theorem gamma_unit {U Z : Scheme.{u}} (i : U ⟶ Z) [IsOpenImmersion i]
    (A : D Λ U) (B : D Λ Z) :
    (openUnit Λ i A ⊗ₛₘ 𝟙 (fobj (pull Λ i) B)) ≫
      (tensorPullIso Λ i (fobj (shriek Λ i) A) B).inv ≫
      fmap (pull Λ i) (gamma Λ i A B) =
      openUnit Λ i (A ⊗ₛ fobj (pull Λ i) B) := by
  let : IsIso ((adj Λ i).projectionComparison A B) :=
    inferInstanceAs (IsIso (openImmersionProjectionComparison Λ i A B))
  simpa only [openUnit, Category.assoc, native_mu Λ i (fobj (shriek Λ i) A) B,
    native_projection Λ i A B, gamma] using inv_projection_unit (adj Λ i) A B

private theorem beta_unit {A B A' B' : Scheme.{u}}
    {i : A ⟶ B} {i' : A' ⟶ B'} {w : A' ⟶ A} {v : B' ⟶ B}
    [IsOpenImmersion i] [IsOpenImmersion i'] (sq : IsPullback w i' i v)
    (K : D Λ A) :
    fmap (pull Λ w) (openUnit Λ i K) ≫
      pullSquareInv Λ sq.toCommSq (fobj (shriek Λ i) K) ≫
      (pull Λ i').map (betaMap Λ sq K) =
      openUnit Λ i' (fobj (pull Λ w) K) := by
  unfold pullSquareInv betaMap openUnit
  exact inverse_mate_unit (adj Λ i) (adj Λ i')
    (TwoSquare.mk _ _ _ _ (pullbackSquareComparison Λ sq.toCommSq).inv)
    (beta Λ sq) (by unfold beta openMate; rfl) K

private theorem inverse_square {C : Type*} [Category C] {A B A' B' : C}
    (a : A ≅ A') (b : B ≅ B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : f ≫ b.hom = a.hom ≫ g) : a.inv ≫ f = g ≫ b.inv := by
  simpa only [fobj, fmap, objTensor, mapTensor, unitComponent,
    compositeComponent] using
    (@raw_inverse_square C _ A B A' B' a b f g h)

private theorem tensorPullIso_inv_braiding {U Z : Scheme.{u}} (i : U ⟶ Z)
    (A B : D Λ Z) :
    (tensorPullIso Λ i A B).inv ≫ fmap (pull Λ i) (sigma Λ Z A B) =
      sigma Λ U (fobj (pull Λ i) A) (fobj (pull Λ i) B) ≫ (tensorPullIso Λ i B A).inv := by
  let : SymmetricCategory (D Λ U) := DerivedCategory.symmetricCategory _
  let : SymmetricCategory (D Λ Z) := DerivedCategory.symmetricCategory _
  exact inverse_square (tensorPullIso Λ i A B) (tensorPullIso Λ i B A)
    (fmap (pull Λ i) (sigma Λ Z A B))
    (sigma Λ U (fobj (pull Λ i) A) (fobj (pull Λ i) B))
    (leftDerivedUpperStarTensor_braiding Λ i A B)

private theorem rho_unit {U Z : Scheme.{u}} (i : U ⟶ Z) [IsOpenImmersion i]
    (A : D Λ Z) (B : D Λ U) :
    (𝟙 (fobj (pull Λ i) A) ⊗ₛₘ openUnit Λ i B) ≫
      (tensorPullIso Λ i A (fobj (shriek Λ i) B)).inv ≫
      fmap (pull Λ i) (rho Λ i A B) =
      openUnit Λ i (fobj (pull Λ i) A ⊗ₛ B) := by
  let : SymmetricCategory (D Λ U) := DerivedCategory.symmetricCategory _
  let : SymmetricCategory (D Λ Z) := DerivedCategory.symmetricCategory _
  let : IsIso ((adj Λ i).projectionComparison B A) :=
    inferInstanceAs (IsIso (openImmersionProjectionComparison Λ i B A))
  simpa only [openUnit, Category.assoc, native_mu Λ i A (fobj (shriek Λ i) B),
    native_projection Λ i B A, rho, gamma, sigma] using
    swapped_projection_unit (adj Λ i) (tensorPullIso_inv_braiding Λ i) A B


variable {X Y Xb Yb T Tb : Scheme.{u}} {j : X ⟶ Xb} {k : Y ⟶ Yb}
  [IsOpenImmersion j] [IsOpenImmersion k]

/-- The ambient external product of the two extensions.
Source: the definition of H in proof step 6
(blueprint: lem-sf-condensed-product-compactification-map). -/
def ambient (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) : D Λ Tb :=
  tensor Λ Tb
    (fobj (pull Λ d.pb) (fobj (shriek Λ j) K))
    (fobj (pull Λ d.qb) (fobj (shriek Λ k) L))

/-- The external product on the open.
Source: D in the statement (blueprint: lem-sf-condensed-product-compactification-map). -/
def inside (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) : D Λ T :=
  tensor Λ T
    (fobj (pull Λ d.p) K) (fobj (pull Λ d.q) L)

/-- The prescribed first-factor construction: beta for j, gamma for j₁, beta for k,
then signed symmetry, gamma for k₁, signed symmetry inside k₁!, and the normalized
composition comparison. All equalities are transported by pullback composition.
Source: proof steps 3 and 4, Stacks 03S6 and 0GL1
(blueprint: lem-sf-condensed-product-compactification-map). -/
def comparison (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) :
    ambient Λ d K L ⟶ fobj (shriek Λ d.u) (inside Λ d K L) :=
  tensorMap Λ Tb
      (betaMap Λ d.first K) (𝟙 _) ≫
    gamma Λ d.j₁ (fobj (pull Λ d.r) K)
      (fobj (pull Λ d.qb) (fobj (shriek Λ k) L)) ≫
    fmap (shriek Λ d.j₁)
      (tensorMap Λ d.S (𝟙 _)
        ((compTo Λ d.j₁ d.qb d.s d.j₁_qb (fobj (shriek Λ k) L)).hom)) ≫
    fmap (shriek Λ d.j₁)
      (tensorMap Λ d.S (𝟙 _)
        (betaMap Λ d.second L)) ≫
    fmap (shriek Λ d.j₁)
      (rho Λ d.k₁
        (fobj (pull Λ d.r) K) (fobj (pull Λ d.q) L) ≫
        fmap (shriek Λ d.k₁)
          (tensorMap Λ T
            ((compTo Λ d.k₁ d.r d.p d.k₁_r K).hom) (𝟙 _))) ≫
    (openFactorComponent Λ d.k₁ d.j₁ d.u d.factor (inside Λ d K L)).hom

/-- Identify D with the restriction of H by the inverse tensor comparison, the two
projection squares and the section-normalized open units.
Source: proof step 5 (blueprint: lem-sf-condensed-product-compactification-map). -/
def restriction (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) :
    inside Λ d K L ⟶ fobj (pull Λ d.u) (ambient Λ d K L) :=
  tensorMap Λ T
    (fmap (pull Λ d.p) (openUnit Λ j K) ≫
      squareInv Λ _ _ _ _ d.left (fobj (shriek Λ j) K))
    (fmap (pull Λ d.q) (openUnit Λ k L) ≫
      squareInv Λ _ _ _ _ d.right (fobj (shriek Λ k) L)) ≫
    (tensorPullIso Λ d.u _ _).inv

/-- The other factorization, with both signed interchanges in the specified places.
Source: proof step 6 (blueprint: lem-sf-condensed-product-compactification-map). -/
def oppositeComparison (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) :
    ambient Λ d K L ⟶ fobj (shriek Λ d.u) (inside Λ d K L) :=
  sigma Λ Tb _ _ ≫ comparison Λ d.swap L K ≫
    fmap (shriek Λ d.u) (sigma Λ T _ _)

/-- The binary normalization, opposite-factorization and signed-symmetry equations.
The symmetry is written after transporting the swapped products to the same cones.
Source: proof steps 5--7 (blueprint: lem-sf-condensed-product-compactification-map). -/
def BinaryAssertion (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) : Prop :=
  IsIso (comparison Λ d K L) ∧ IsIso (oppositeComparison Λ d K L) ∧
    (restriction Λ d K L ≫ fmap (pull Λ d.u) (comparison Λ d K L) =
      openUnit Λ d.u (inside Λ d K L)) ∧
    (oppositeComparison Λ d K L = comparison Λ d K L) ∧
    (comparison Λ d K L ≫ fmap (shriek Λ d.u)
        (sigma Λ T
          (fobj (pull Λ d.p) K) (fobj (pull Λ d.q) L)) =
      sigma Λ Tb
          (fobj (pull Λ d.pb) (fobj (shriek Λ j) K))
          (fobj (pull Λ d.qb) (fobj (shriek Λ k) L)) ≫
        comparison Λ d.swap L K)


private def firstOpenComparison (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) :
    ambient Λ d K L ⟶ fobj (shriek Λ d.j₁)
      ((fobj (pull Λ d.r) K) ⊗ₛ fobj (pull Λ d.s) (fobj (shriek Λ k) L)) :=
  tensorMap Λ Tb (betaMap Λ d.first K) (𝟙 _) ≫
    gamma Λ d.j₁ (fobj (pull Λ d.r) K) (fobj (pull Λ d.qb) (fobj (shriek Λ k) L)) ≫
    fmap (shriek Λ d.j₁)
      (tensorMap Λ d.S (𝟙 _)
        ((compTo Λ d.j₁ d.qb d.s d.j₁_qb (fobj (shriek Λ k) L)).hom))

private def secondOpenComparison (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) :
    (fobj (pull Λ d.r) K ⊗ₛ fobj (pull Λ d.s) (fobj (shriek Λ k) L)) ⟶
      fobj (shriek Λ d.k₁) (inside Λ d K L) :=
  tensorMap Λ d.S (𝟙 _) (betaMap Λ d.second L) ≫
    rho Λ d.k₁ (fobj (pull Λ d.r) K) (fobj (pull Λ d.q) L) ≫
    fmap (shriek Λ d.k₁)
      (tensorMap Λ T
        ((compTo Λ d.k₁ d.r d.p d.k₁_r K).hom) (𝟙 _))

private theorem comparison_factorization
    (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) :
    comparison Λ d K L = firstOpenComparison Λ d K L ≫
      fmap (shriek Λ d.j₁) (secondOpenComparison Λ d K L) ≫
      (openFactorComponent Λ d.k₁ d.j₁ d.u d.factor (inside Λ d K L)).hom := by
  simp only [firstOpenComparison, secondOpenComparison, comparison,
    fmap_comp, Category.assoc]

private def firstOpenRestriction (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) :
    (fobj (pull Λ d.r) K ⊗ₛ fobj (pull Λ d.s) (fobj (shriek Λ k) L)) ⟶
      fobj (pull Λ d.j₁) (ambient Λ d K L) :=
  (𝟙 _ ⊗ₛₘ
    ((compTo Λ d.j₁ d.qb d.s d.j₁_qb (fobj (shriek Λ k) L)).inv)) ≫
    ((fmap (pull Λ d.r) (openUnit Λ j K) ≫
      pullSquareInv Λ d.first.toCommSq (fobj (shriek Λ j) K)) ⊗ₛₘ 𝟙 _) ≫
    (tensorPullIso Λ d.j₁ (fobj (pull Λ d.pb) (fobj (shriek Λ j) K))
      (fobj (pull Λ d.qb) (fobj (shriek Λ k) L))).inv

private def secondOpenRestriction (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) :
    inside Λ d K L ⟶ fobj (pull Λ d.k₁)
      ((fobj (pull Λ d.r) K) ⊗ₛ fobj (pull Λ d.s) (fobj (shriek Λ k) L)) :=
  (((compTo Λ d.k₁ d.r d.p d.k₁_r K).inv) ⊗ₛₘ
    (fmap (pull Λ d.q) (openUnit Λ k L) ≫
      pullSquareInv Λ d.second.toCommSq (fobj (shriek Λ k) L))) ≫
    (tensorPullIso Λ d.k₁ (fobj (pull Λ d.r) K)
      (fobj (pull Λ d.s) (fobj (shriek Λ k) L))).inv

private theorem left_unit_iso_explicit
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    (K : C) (N X : D) (α : K ⟶ fobj R X) (β : X ⟶ fobj L K)
    (hα : α ≫ fmap R β = unitComponent a K)
    (m : fobj R X ⊗ₛ fobj R N ⟶ fobj R (X ⊗ₛ N))
    (m' : fobj R (fobj L K) ⊗ₛ fobj R N ⟶ fobj R (fobj L K ⊗ₛ N))
    (hm : m ≫ fmap R (β ⊗ₛₘ 𝟙 N) = (fmap R β ⊗ₛₘ 𝟙 (fobj R N)) ≫ m')
    (z : fobj L K ⊗ₛ N ⟶ fobj L (K ⊗ₛ fobj R N))
    (hz : ((unitComponent a K ⊗ₛₘ 𝟙 (fobj R N)) ≫ m') ≫ fmap R z =
      unitComponent a (K ⊗ₛ fobj R N)) {N' : C} (c : fobj R N ≅ N') :
    ((𝟙 K ⊗ₛₘ c.inv) ≫ (α ⊗ₛₘ 𝟙 (fobj R N)) ≫ m) ≫
      fmap R ((β ⊗ₛₘ 𝟙 N) ≫ z ≫ fmap L (𝟙 K ⊗ₛₘ c.hom)) =
      unitComponent a (K ⊗ₛ N') := by
  simpa only [fobj, fmap, objTensor, mapTensor, unitComponent,
    compositeComponent] using
    (@raw_left_unit_iso_explicit C D _ _ _ _ L R a K N X α β hα m m' hm z hz N' c)

private theorem right_unit_iso_explicit
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    (K : D) (N : C) (X : D) (α : N ⟶ fobj R X) (β : X ⟶ fobj L N)
    (hα : α ≫ fmap R β = unitComponent a N)
    (m : fobj R K ⊗ₛ fobj R X ⟶ fobj R (K ⊗ₛ X))
    (m' : fobj R K ⊗ₛ fobj R (fobj L N) ⟶ fobj R (K ⊗ₛ fobj L N))
    (hm : m ≫ fmap R (𝟙 K ⊗ₛₘ β) = (𝟙 (fobj R K) ⊗ₛₘ fmap R β) ≫ m')
    (z : K ⊗ₛ fobj L N ⟶ fobj L (fobj R K ⊗ₛ N))
    (hz : ((𝟙 (fobj R K) ⊗ₛₘ unitComponent a N) ≫ m') ≫ fmap R z =
      unitComponent a (fobj R K ⊗ₛ N)) {K' : C} (c : fobj R K ≅ K') :
    ((c.inv ⊗ₛₘ α) ≫ m) ≫
      fmap R ((𝟙 K ⊗ₛₘ β) ≫ z ≫ fmap L (c.hom ⊗ₛₘ 𝟙 N)) =
      unitComponent a (K' ⊗ₛ N) := by
  simpa only [fobj, fmap, objTensor, mapTensor, unitComponent,
    compositeComponent] using
    (@raw_right_unit_iso_explicit C D _ _ _ _ L R a K N X α β hα m m' hm z hz K' c)

private theorem tensor_composition_explicit
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (R : C ⥤ D) (S : D ⥤ E)
    (A B : C) (A' B' : D) (A'' B'' : E)
    (α : A' ⟶ fobj R A) (ci : B' ⟶ fobj R B) (di : A'' ⟶ fobj S A')
    (β : B'' ⟶ fobj S B')
    (m : fobj R A ⊗ₛ fobj R B ⟶ fobj R (A ⊗ₛ B))
    (n₀ : fobj S A' ⊗ₛ fobj S B' ⟶ fobj S (A' ⊗ₛ B'))
    (n₁ : fobj S A' ⊗ₛ fobj S (fobj R B) ⟶ fobj S (A' ⊗ₛ fobj R B))
    (n₂ : fobj S (fobj R A) ⊗ₛ fobj S (fobj R B) ⟶ fobj S (fobj R A ⊗ₛ fobj R B))
    (h₁ : n₀ ≫ fmap S (𝟙 A' ⊗ₛₘ ci) = (𝟙 (fobj S A') ⊗ₛₘ fmap S ci) ≫ n₁)
    (h₂ : n₁ ≫ fmap S (α ⊗ₛₘ 𝟙 (fobj R B)) = (fmap S α ⊗ₛₘ 𝟙 (fobj S (fobj R B))) ≫ n₂) :
    ((di ⊗ₛₘ β) ≫ n₀) ≫ fmap S ((𝟙 A' ⊗ₛₘ ci) ≫ (α ⊗ₛₘ 𝟙 (fobj R B)) ≫ m) =
      ((di ≫ fmap S α) ⊗ₛₘ (β ≫ fmap S ci)) ≫ n₂ ≫ fmap S m := by
  simpa only [fobj, fmap, objTensor, mapTensor, unitComponent,
    compositeComponent] using
    (@raw_tensor_composition_explicit C D E _ _ _ _ _ _ R S A B A' B' A'' B''
      α ci di β m n₀ n₁ n₂ h₁ h₂)

private theorem tensor_swap_explicit
    {C : Type*} [Category C] [MonoidalCategory C]
    {A B A' B' E F : C} (f : A ⟶ A') (g : B ⟶ B')
    (s₀ : A ⊗ₛ B ⟶ B ⊗ₛ A) (s₁ : A' ⊗ₛ B' ⟶ B' ⊗ₛ A')
    (m : A' ⊗ₛ B' ⟶ E) (n : B' ⊗ₛ A' ⟶ F) (s : E ⟶ F)
    (hn : s₀ ≫ (g ⊗ₛₘ f) = (f ⊗ₛₘ g) ≫ s₁)
    (hm : m ≫ s = s₁ ≫ n) :
    s₀ ≫ ((g ⊗ₛₘ f) ≫ n) = ((f ⊗ₛₘ g) ≫ m) ≫ s := by
  simpa only [fobj, fmap, objTensor, mapTensor, unitComponent,
    compositeComponent] using
    (@raw_tensor_swap_explicit C _ _ A B A' B' E F f g s₀ s₁ m n s hn hm)

private theorem tensorPull_inv_natural {U Z : Scheme.{u}} (i : U ⟶ Z)
    {A A' B B' : D Λ Z} (f : A ⟶ A') (g : B ⟶ B') :
    (tensorPullIso Λ i A B).inv ≫ fmap (pull Λ i) (f ⊗ₛₘ g) =
      (fmap (pull Λ i) f ⊗ₛₘ fmap (pull Λ i) g) ≫ (tensorPullIso Λ i A' B').inv := by
  exact inverse_square (tensorPullIso Λ i A B) (tensorPullIso Λ i A' B')
    (fmap (pull Λ i) (f ⊗ₛₘ g)) (fmap (pull Λ i) f ⊗ₛₘ fmap (pull Λ i) g)
    (leftDerivedUpperStarTensor_naturality Λ i f g).symm

private theorem tensorPull_inv_natural_left {U Z : Scheme.{u}} (i : U ⟶ Z)
    {A A' : D Λ Z} (f : A ⟶ A') (B : D Λ Z) :
    (tensorPullIso Λ i A B).inv ≫ fmap (pull Λ i) (f ⊗ₛₘ 𝟙 B) =
      (fmap (pull Λ i) f ⊗ₛₘ 𝟙 (fobj (pull Λ i) B)) ≫ (tensorPullIso Λ i A' B).inv := by
  simpa only [fmap_id (pull Λ i)] using tensorPull_inv_natural Λ i f (𝟙 B)

private theorem tensorPull_inv_natural_right {U Z : Scheme.{u}} (i : U ⟶ Z)
    (A : D Λ Z) {B B' : D Λ Z} (g : B ⟶ B') :
    (tensorPullIso Λ i A B).inv ≫ fmap (pull Λ i) (𝟙 A ⊗ₛₘ g) =
      (𝟙 (fobj (pull Λ i) A) ⊗ₛₘ fmap (pull Λ i) g) ≫ (tensorPullIso Λ i A B').inv := by
  simpa only [fmap_id (pull Λ i)] using tensorPull_inv_natural Λ i (𝟙 A) g

private theorem sigma_natural (Z : Scheme.{u}) {A A' B B' : D Λ Z}
    (f : A ⟶ A') (g : B ⟶ B') :
    sigma Λ Z A B ≫ (g ⊗ₛₘ f) = (f ⊗ₛₘ g) ≫ sigma Λ Z A' B' := by
  let : BraidedCategory (D Λ Z) := DerivedCategory.braidedCategory' _
  exact (BraidedCategory.braiding_naturality f g).symm

private theorem normalized_of_presentations
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {N : C} {E : D}
    {r₀ : N ⟶ fobj R E} {f₀ : E ⟶ fobj L N}
    (h : r₀ ≫ fmap R f₀ = unitComponent a N)
    (r : N ⟶ fobj R E) (f : E ⟶ fobj L N) (hr : r₀ = r) (hf : f₀ = f) :
    r ≫ fmap R f = unitComponent a N := by
  simpa only [fobj, fmap, objTensor, mapTensor, unitComponent,
    compositeComponent] using
    (@raw_normalized_of_presentations C D _ _ L R a N E r₀ f₀ h r f hr hf)

private theorem native_left_unit {U Z : Scheme.{u}}
    (i : U ⟶ Z) [IsOpenImmersion i] (K : D Λ U) (N X : D Λ Z)
    (α : K ⟶ fobj (pull Λ i) X) (β : X ⟶ fobj (shriek Λ i) K)
    (hα : α ≫ fmap (pull Λ i) β = openUnit Λ i K)
    {N' : D Λ U} (c : fobj (pull Λ i) N ≅ N') :
    ((𝟙 K ⊗ₛₘ c.inv) ≫ (α ⊗ₛₘ 𝟙 (fobj (pull Λ i) N)) ≫
        (tensorPullIso Λ i X N).inv) ≫
      fmap (pull Λ i) ((β ⊗ₛₘ 𝟙 N) ≫ gamma Λ i K N ≫
        fmap (shriek Λ i) (𝟙 K ⊗ₛₘ c.hom)) = openUnit Λ i (K ⊗ₛ N') := by
  exact left_unit_iso_explicit (adj Λ i) K N X α β hα
    (tensorPullIso Λ i X N).inv (tensorPullIso Λ i (fobj (shriek Λ i) K) N).inv
    (tensorPull_inv_natural_left Λ i β N) (gamma Λ i K N)
    ((Category.assoc _ _ _).trans (gamma_unit Λ i K N)) c

private theorem native_right_unit {U Z : Scheme.{u}}
    (i : U ⟶ Z) [IsOpenImmersion i] (K : D Λ Z) (N : D Λ U) (X : D Λ Z)
    (α : N ⟶ fobj (pull Λ i) X) (β : X ⟶ fobj (shriek Λ i) N)
    (hα : α ≫ fmap (pull Λ i) β = openUnit Λ i N)
    {K' : D Λ U} (c : fobj (pull Λ i) K ≅ K') :
    ((c.inv ⊗ₛₘ α) ≫ (tensorPullIso Λ i K X).inv) ≫
      fmap (pull Λ i) ((𝟙 K ⊗ₛₘ β) ≫ rho Λ i K N ≫
        fmap (shriek Λ i) (c.hom ⊗ₛₘ 𝟙 N)) = openUnit Λ i (K' ⊗ₛ N) := by
  exact right_unit_iso_explicit (adj Λ i) K N X α β hα
    (tensorPullIso Λ i K X).inv (tensorPullIso Λ i K (fobj (shriek Λ i) N)).inv
    (tensorPull_inv_natural_right Λ i K β) (rho Λ i K N)
    ((Category.assoc _ _ _).trans (rho_unit Λ i K N)) c

attribute [local irreducible] tensorPullIso square gamma rho

set_option maxHeartbeats 4000000 in
-- Native derived functor endpoints require a larger checking limit.
private theorem firstOpen_unit (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) :
    firstOpenRestriction Λ d K L ≫ fmap (pull Λ d.j₁) (firstOpenComparison Λ d K L) =
      openUnit Λ d.j₁
        (fobj (pull Λ d.r) K ⊗ₛ fobj (pull Λ d.s) (fobj (shriek Λ k) L)) := by
  have h := native_left_unit Λ d.j₁ (fobj (pull Λ d.r) K)
    (fobj (pull Λ d.qb) (fobj (shriek Λ k) L)) (fobj (pull Λ d.pb) (fobj (shriek Λ j) K))
    (fmap (pull Λ d.r) (openUnit Λ j K) ≫
      pullSquareInv Λ d.first.toCommSq (fobj (shriek Λ j) K))
    (betaMap Λ d.first K)
    ((Category.assoc _ _ _).trans (beta_unit Λ d.first K))
    (compTo Λ d.j₁ d.qb d.s d.j₁_qb (fobj (shriek Λ k) L))
  refine normalized_of_presentations (adj Λ d.j₁) h
    (firstOpenRestriction Λ d K L) (firstOpenComparison Λ d K L) ?_ ?_
  · rfl
  · rfl

set_option maxHeartbeats 4000000 in
-- Native derived functor endpoints require a larger checking limit.
private theorem secondOpen_unit (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) :
    secondOpenRestriction Λ d K L ≫ fmap (pull Λ d.k₁) (secondOpenComparison Λ d K L) =
      openUnit Λ d.k₁ (inside Λ d K L) := by
  have h := native_right_unit Λ d.k₁ (fobj (pull Λ d.r) K)
    (fobj (pull Λ d.q) L) (fobj (pull Λ d.s) (fobj (shriek Λ k) L))
    (fmap (pull Λ d.q) (openUnit Λ k L) ≫
      pullSquareInv Λ d.second.toCommSq (fobj (shriek Λ k) L))
    (betaMap Λ d.second L)
    ((Category.assoc _ _ _).trans (beta_unit Λ d.second L))
    (compTo Λ d.k₁ d.r d.p d.k₁_r K)
  refine normalized_of_presentations (adj Λ d.k₁) h
    (secondOpenRestriction Λ d K L) (secondOpenComparison Λ d K L) ?_ ?_
  · rfl
  · rfl
private theorem compTo_inv_natural {U V Z : Scheme.{u}}
    (i : U ⟶ V) (j : V ⟶ Z) (h : U ⟶ Z) (e : i ≫ j = h)
    {K L : D Λ Z} (f : K ⟶ L) :
    (compTo Λ i j h e K).inv ≫ fmap (pull Λ i) (fmap (pull Λ j) f) =
      fmap (pull Λ h) f ≫ (compTo Λ i j h e L).inv := by
  subst h
  simpa only [compTo, compIsoComponent, fmap, fobj, pull, eqToIso_refl, Iso.trans_refl,
    Iso.symm_inv, Iso.app_hom,
    Functor.comp_map] using (leftDerivedUpperStarComp Λ i j).hom.naturality f |>.symm


private theorem inverse_path {C : Type*} [Category C]
    {A B C' D E : C} (a : A ≅ B) (b : B ≅ C') (c : A ≅ D)
    (d : D ≅ E) (e : E ≅ C')
    (h : a.hom ≫ b.hom = c.hom ≫ d.hom ≫ e.hom) :
    e.inv ≫ d.inv ≫ c.inv = b.inv ≫ a.inv := by
  have hi : a ≪≫ b = c ≪≫ d ≪≫ e := Iso.ext h
  have h' := congrArg Iso.inv hi
  simpa only [Iso.trans_inv, Category.assoc] using h'.symm



-- Native derived pullback coherence needs the larger checking limit.
set_option maxHeartbeats 4000000 in
-- Native derived functor endpoints require a larger checking limit.
private theorem tensorPull_comp_inv {U V Z : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ Z)
    (A B : D Λ Z) :
    (tensorPullIso Λ i ((P Λ j).obj A) ((P Λ j).obj B)).inv ≫
        (P Λ i).map (tensorPullIso Λ j A B).inv ≫
        (leftDerivedUpperStarComp Λ i j).inv.app (A ⊗ B) =
      ((leftDerivedUpperStarComp Λ i j).inv.app A ⊗ₘ
        (leftDerivedUpperStarComp Λ i j).inv.app B) ≫
        (tensorPullIso Λ (i ≫ j) A B).inv := by
  exact inverse_path (tensorPullIso Λ (i ≫ j) A B)
    (tensorIso ((leftDerivedUpperStarComp Λ i j).app A)
      ((leftDerivedUpperStarComp Λ i j).app B))
    ((leftDerivedUpperStarComp Λ i j).app (A ⊗ B))
    ((P Λ i).mapIso (tensorPullIso Λ j A B))
    (tensorPullIso Λ i ((P Λ j).obj A) ((P Λ j).obj B))
    (by simpa only [tensorPullIso, leftDerivedUpperStarTensorIso, Iso.app_hom,
      asIso_hom, tensorIso_hom, Functor.mapIso_hom, fobj, objTensor, pull] using
      leftDerivedUpperStarTensor_comp Λ i j A B)



-- Native derived pullback coherence needs the larger checking limit.
set_option maxHeartbeats 4000000 in
-- Native derived functor endpoints require a larger checking limit.
private theorem pullback_path {A B A' B' U : Scheme.{u}}
    {r : A' ⟶ A} {i' : A' ⟶ B'} {i : A ⟶ B} {v : B' ⟶ B}
    (sq : CommSq r i' i v) (t : U ⟶ A') (N : D Λ B) :
    (leftDerivedUpperStarComp Λ t r).hom.app ((P Λ i).obj N) ≫
        (P Λ t).map ((pullbackSquareComparison Λ sq).inv.app N) ≫
        (leftDerivedUpperStarComp Λ t i').inv.app ((P Λ v).obj N) =
      (square Λ (t ≫ i') v (t ≫ r) i
        (by rw [Category.assoc, ← sq.w, Category.assoc])).inv.app N := by
  apply (cancel_mono ((leftDerivedUpperStarComp Λ t i').hom.app
    ((P Λ v).obj N))).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  apply (cancel_epi ((leftDerivedUpperStarComp Λ (t ≫ r) i).hom.app N)).1
  erw [← Category.assoc, leftDerivedUpperStarComp_assoc_app]
  simp only [Category.assoc]
  have hs := congrArg (fun e ↦ e.hom.app N) (pullbackSquareComparison_flip Λ sq)
  simp only [Iso.symm_hom] at hs
  erw [← hs, reassoc_of% (map_pullbackSquareComparison_hom_app Λ sq.flip t N)]
  have ha := leftDerivedUpperStarComp_assoc_app Λ t i' v N
  rw [← Category.assoc] at ha
  simp only [square, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    eqToIso.inv, Iso.hom_inv_id_app_assoc, Category.assoc]
  erw [ha]
  simp




-- Native derived pullback coherence needs the larger checking limit.
set_option maxHeartbeats 4000000 in
-- Native derived functor endpoints require a larger checking limit.
private theorem pullback_post_path {Y Yb S T Tb : Scheme.{u}}
    (q : T ⟶ Y) (k : Y ⟶ Yb) (t : T ⟶ S) (i : S ⟶ Tb) (v : Tb ⟶ Yb)
    (sq : CommSq q t k (i ≫ v)) (N : D Λ Yb) :
    (pullbackSquareComparison Λ sq).inv.app N ≫
        (P Λ t).map ((leftDerivedUpperStarComp Λ i v).hom.app N) ≫
        (leftDerivedUpperStarComp Λ t i).inv.app ((P Λ v).obj N) =
      (square Λ (t ≫ i) v q k
        (by rw [Category.assoc, ← sq.w])).inv.app N := by
  apply (cancel_mono ((leftDerivedUpperStarComp Λ t i).hom.app
    ((P Λ v).obj N))).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  have hs := congrArg (fun e ↦ e.hom.app N) (pullbackSquareComparison_flip Λ sq)
  simp only [Iso.symm_hom] at hs
  erw [← hs, pullbackSquareComparison_hom_app]
  simp only [square, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    eqToIso.inv, Category.assoc]
  have ha := leftDerivedUpperStarComp_assoc_app Λ t i v N
  rw [← Category.assoc] at ha
  erw [ha]
  simp




private theorem scalar_object_transport_path
    {E : Type*} {A B : Type*} [Category E]
    (F : A → E) (G : B → E) {a₀ : A} {b₀ : B} {X Y : E}
    (ca : F a₀ ≅ X) (cb : G b₀ ≅ Y) (m : X ⟶ Y)
    (R : A → B → Prop) (h₀ : R a₀ b₀)
    (H : ∀ a b, R a b → (F a ⟶ G b))
    (h : ca.hom ≫ m ≫ cb.inv = H a₀ b₀ h₀)
    (a : A) (b : B) (ea : a₀ = a) (eb : b₀ = b) (hr : R a b) :
    (ca.symm ≪≫ eqToIso (congrArg F ea)).inv ≫ m ≫
      (cb.symm ≪≫ eqToIso (congrArg G eb)).hom = H a b hr := by
  cases ea
  cases eb
  simpa only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl,
    Iso.symm_inv, Iso.symm_hom] using h



private theorem scalar_tensorPull_factor {U V Z : Scheme.{u}}
    (i : U ⟶ V) (j : V ⟶ Z) (h : U ⟶ Z) (e : i ≫ j = h) (A B : D Λ Z) :
    (tensorPullIso Λ i (fobj (pull Λ j) A) (fobj (pull Λ j) B)).inv ≫
        fmap (pull Λ i) (tensorPullIso Λ j A B).inv ≫
        (compTo Λ i j h e (A ⊗ₛ B)).hom =
      ((compTo Λ i j h e A).hom ⊗ₛₘ (compTo Λ i j h e B).hom) ≫
        (tensorPullIso Λ h A B).inv := by
  subst h
  simpa only [compTo, compIsoComponent, eqToIso_refl, Iso.trans_refl, Iso.symm_hom, Iso.app_inv,
    fmap, fobj, objTensor, mapTensor, pull] using tensorPull_comp_inv Λ i j A B


private theorem scalar_pullback_path {A B A' B' U : Scheme.{u}}
    {r : A' ⟶ A} {i' : A' ⟶ B'} {i : A ⟶ B} {v : B' ⟶ B}
    (sq : CommSq r i' i v) (t : U ⟶ A')
    (w : U ⟶ A) (z : U ⟶ B') (er : t ≫ r = w) (ei : t ≫ i' = z)
    (ew : z ≫ v = w ≫ i) (N : D Λ B) :
    (compTo Λ t r w er (fobj (pull Λ i) N)).inv ≫
      fmap (pull Λ t) (pullSquareInv Λ sq N) ≫
      (compTo Λ t i' z ei (fobj (pull Λ v) N)).hom =
      squareInv Λ z v w i ew N := by
  let ca := compIsoComponent Λ t r (fobj (pull Λ i) N)
  let cb := compIsoComponent Λ t i' (fobj (pull Λ v) N)
  have hc : ca.hom ≫ fmap (pull Λ t) (pullSquareInv Λ sq N) ≫ cb.inv =
      squareInv Λ (t ≫ i') v (t ≫ r) i
        (by rw [Category.assoc, ← sq.w, Category.assoc]) N := by
    simpa only [ca, cb, compIsoComponent, squareInv, pullSquareInv, compositeComponent,
      fmap, fobj, pull, Iso.app_hom, Iso.app_inv] using pullback_path Λ sq t N
  exact scalar_object_transport_path
    (fun a : U ⟶ A ↦ fobj (pull Λ a) (fobj (pull Λ i) N))
    (fun b : U ⟶ B' ↦ fobj (pull Λ b) (fobj (pull Λ v) N))
    ca cb (fmap (pull Λ t) (pullSquareInv Λ sq N))
    (fun a b ↦ b ≫ v = a ≫ i)
    (by rw [Category.assoc, ← sq.w, Category.assoc])
    (fun a b he ↦ squareInv Λ b v a i he N)
    hc w z er ei ew


private theorem compIsoComponent_inv {U V Z Q : Scheme.{u}}
    (i : U ⟶ V) (j : V ⟶ Z) (v : Z ⟶ Q) (N : D Λ Q) :
    (compIsoComponent Λ i j (fobj (pull Λ v) N)).inv =
      (leftDerivedUpperStarComp Λ i j).inv.app ((P Λ v).obj N) := by
  rfl



private theorem map_compIsoComponent_hom {U V Z Q : Scheme.{u}}
    (t : U ⟶ V) (i : V ⟶ Z) (j : Z ⟶ Q) (N : D Λ Q) :
    fmap (pull Λ t) (compIsoComponent Λ i j N).hom =
      (P Λ t).map ((leftDerivedUpperStarComp Λ i j).hom.app N) := by
  rfl



private theorem pullSquareInv_eq_component {A B A' B' : Scheme.{u}}
    {i : A ⟶ B} {i' : A' ⟶ B'} {w : A' ⟶ A} {v : B' ⟶ B}
    (sq : CommSq w i' i v) (N : D Λ B) :
    pullSquareInv Λ sq N = (pullbackSquareComparison Λ sq).inv.app N := by
  rfl



private theorem squareInv_eq_component {T X Y Z : Scheme.{u}}
    (f : T ⟶ X) (g : X ⟶ Z) (h : T ⟶ Y) (i : Y ⟶ Z)
    (e : f ≫ g = h ≫ i) (N : D Λ Z) :
    squareInv Λ f g h i e N = (square Λ f g h i e).inv.app N := by
  rfl


private theorem heq_comp {C : Type*} [Category C]
    {A B D A' B' D' : C} (ha : A = A') (hb : B = B') (hd : D = D')
    (f : A ⟶ B) (f' : A' ⟶ B') (g : B ⟶ D) (g' : B' ⟶ D')
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  cases ha
  cases hb
  cases hd
  cases hf
  cases hg
  rfl



private theorem scalar_post_word {Y Yb S T Tb : Scheme.{u}}
    (q : T ⟶ Y) (k : Y ⟶ Yb) (t : T ⟶ S) (i : S ⟶ Tb) (v : Tb ⟶ Yb)
    (sq : CommSq q t k (i ≫ v)) (N : D Λ Yb) :
    pullSquareInv Λ sq N ≫ fmap (pull Λ t) (compIsoComponent Λ i v N).hom ≫
      (compIsoComponent Λ t i (fobj (pull Λ v) N)).inv =
    (pullbackSquareComparison Λ sq).inv.app N ≫
      (P Λ t).map ((leftDerivedUpperStarComp Λ i v).hom.app N) ≫
      (leftDerivedUpperStarComp Λ t i).inv.app ((P Λ v).obj N) := by
  have hab := heq_comp rfl rfl rfl
    (fmap (pull Λ t) (compIsoComponent Λ i v N).hom)
    ((P Λ t).map ((leftDerivedUpperStarComp Λ i v).hom.app N))
    (compIsoComponent Λ t i (fobj (pull Λ v) N)).inv
    ((leftDerivedUpperStarComp Λ t i).inv.app ((P Λ v).obj N))
    (heq_of_eq (map_compIsoComponent_hom Λ t i v N))
    (heq_of_eq (compIsoComponent_inv Λ t i v N))
  have hw := heq_comp rfl rfl rfl
    (pullSquareInv Λ sq N) ((pullbackSquareComparison Λ sq).inv.app N)
    (fmap (pull Λ t) (compIsoComponent Λ i v N).hom ≫
      (compIsoComponent Λ t i (fobj (pull Λ v) N)).inv)
    ((P Λ t).map ((leftDerivedUpperStarComp Λ i v).hom.app N) ≫
      (leftDerivedUpperStarComp Λ t i).inv.app ((P Λ v).obj N))
    (heq_of_eq (pullSquareInv_eq_component Λ sq N)) hab
  exact eq_of_heq hw



private theorem scalar_post_core {Y Yb S T Tb : Scheme.{u}}
    (q : T ⟶ Y) (k : Y ⟶ Yb) (t : T ⟶ S) (i : S ⟶ Tb) (v : Tb ⟶ Yb)
    (sq : CommSq q t k (i ≫ v)) (N : D Λ Yb) :
    pullSquareInv Λ sq N ≫ fmap (pull Λ t) (compIsoComponent Λ i v N).hom ≫
      (compIsoComponent Λ t i (fobj (pull Λ v) N)).inv =
        squareInv Λ (t ≫ i) v q k
          (by rw [Category.assoc, ← sq.w]) N := by
  refine (scalar_post_word Λ q k t i v sq N).trans
    ((pullback_post_path Λ q k t i v sq N).trans ?_)
  exact (squareInv_eq_component Λ (t ≫ i) v q k _ N).symm



private theorem scalar_object_transport_post_path
    {C E : Type*} {A B : Type*} [Category C] [Category E]
    (P : A → C) (Q : B → E) {a₀ : A} {b₀ : B} {Y : C}
    (T : C ⥤ E) (ca : P a₀ ≅ Y) (cb : Q b₀ ≅ fobj T Y) (X : E)
    (R : A → Prop) (S : B → Prop)
    (m : ∀ a, R a → (X ⟶ fobj T (P a)))
    (H : ∀ b, S b → (X ⟶ Q b))
    (h : ∀ ha : R a₀, ∀ hb : S b₀,
      m a₀ ha ≫ fmap T ca.hom ≫ cb.inv = H b₀ hb)
    (a : A) (b : B) (ea : a₀ = a) (eb : b₀ = b) (ha : R a) (hb : S b) :
    m a ha ≫ fmap T ((ca.symm ≪≫ eqToIso (congrArg P ea)).inv) ≫
      (cb.symm ≪≫ eqToIso (congrArg Q eb)).hom = H b hb := by
  cases ea
  cases eb
  simpa only [eqToIso_refl, Iso.trans_refl, Iso.symm_inv, Iso.symm_hom] using h ha hb



-- Native derived pullback coherence needs the larger checking limit.
set_option maxHeartbeats 4000000 in
-- Native derived functor endpoints require a larger checking limit.
private theorem scalar_pullback_post_path {Y Yb S T Tb : Scheme.{u}}
    (q : T ⟶ Y) (k : Y ⟶ Yb) (t : T ⟶ S) (i : S ⟶ Tb) (v : Tb ⟶ Yb)
    (s : S ⟶ Yb) (h : T ⟶ Tb) (es : i ≫ v = s) (eh : t ≫ i = h)
    (sq : CommSq q t k s) (ew : h ≫ v = q ≫ k) (N : D Λ Yb) :
    pullSquareInv Λ sq N ≫
      fmap (pull Λ t) (compTo Λ i v s es N).inv ≫
      (compTo Λ t i h eh (fobj (pull Λ v) N)).hom = squareInv Λ h v q k ew N := by
  let ca : fobj (pull Λ (i ≫ v)) N ≅
      fobj (pull Λ i) (fobj (pull Λ v) N) :=
    compIsoComponent Λ i v N
  let cb : fobj (pull Λ (t ≫ i)) (fobj (pull Λ v) N) ≅
      fobj (pull Λ t) (fobj (pull Λ i) (fobj (pull Λ v) N)) :=
    compIsoComponent Λ t i (fobj (pull Λ v) N)
  have hc (ha : q ≫ k = t ≫ (i ≫ v)) (hb : (t ≫ i) ≫ v = q ≫ k) :
      pullSquareInv Λ (⟨ha⟩ : CommSq q t k (i ≫ v)) N ≫
        fmap (pull Λ t) ca.hom ≫ cb.inv = squareInv Λ (t ≫ i) v q k hb N := by
    exact scalar_post_core Λ q k t i v (⟨ha⟩ : CommSq q t k (i ≫ v)) N
  exact scalar_object_transport_post_path
    (Y := fobj (pull Λ i) (fobj (pull Λ v) N))
    (fun a : S ⟶ Yb ↦ fobj (pull Λ a) N)
    (fun b : T ⟶ Tb ↦ fobj (pull Λ b) (fobj (pull Λ v) N))
    (pull Λ t) ca cb (fobj (pull Λ q) (fobj (pull Λ k) N))
    (fun a ↦ q ≫ k = t ≫ a) (fun b ↦ b ≫ v = q ≫ k)
    (fun a ha ↦ pullSquareInv Λ (⟨ha⟩ : CommSq q t k a) N)
    (fun b hb ↦ squareInv Λ b v q k hb N)
    hc s h es eh sq.w ew





private theorem tensor_factor {C : Type*} [Category C] [MonoidalCategory C]
    {A B A' B' U V W Z : C} (x : A ⟶ A') (y : B ⟶ B')
    (m : A' ⊗ₛ B' ⟶ W) (n : U ⊗ₛ V ⟶ Z)
    (px : A' ⟶ U) (qy : B' ⟶ V)
    (r : A ⊗ₛ B ⟶ W) (s : W ⟶ Z)
    (h12 : r = (x ⊗ₛₘ y) ≫ m)
    (hm : m ≫ s = (px ⊗ₛₘ qy) ≫ n) :
    r ≫ s = ((x ≫ px) ⊗ₛₘ (y ≫ qy)) ≫ n := by
  dsimp only [fobj, fmap, objTensor, mapTensor, unitComponent] at *
  rw [h12, Category.assoc, hm, ← Category.assoc, tensorHom_comp_tensorHom]


private theorem native_tensor_composition {U V Z : Scheme.{u}}
    (i : U ⟶ V) (j : V ⟶ Z) (A B : D Λ Z) (A' B' : D Λ V) (A'' B'' : D Λ U)
    (α : A' ⟶ fobj (pull Λ j) A) (ci : B' ⟶ fobj (pull Λ j) B)
    (di : A'' ⟶ fobj (pull Λ i) A') (β : B'' ⟶ fobj (pull Λ i) B') :
    ((di ⊗ₛₘ β) ≫ (tensorPullIso Λ i A' B').inv) ≫
      fmap (pull Λ i) ((𝟙 A' ⊗ₛₘ ci) ≫ (α ⊗ₛₘ 𝟙 (fobj (pull Λ j) B)) ≫
        (tensorPullIso Λ j A B).inv) =
      ((di ≫ fmap (pull Λ i) α) ⊗ₛₘ (β ≫ fmap (pull Λ i) ci)) ≫
        (tensorPullIso Λ i (fobj (pull Λ j) A) (fobj (pull Λ j) B)).inv ≫
          fmap (pull Λ i) (tensorPullIso Λ j A B).inv := by
  exact tensor_composition_explicit (pull Λ j) (pull Λ i) A B A' B' A'' B'' α ci di β
    (tensorPullIso Λ j A B).inv (tensorPullIso Λ i A' B').inv
    (tensorPullIso Λ i A' (fobj (pull Λ j) B)).inv
    (tensorPullIso Λ i (fobj (pull Λ j) A) (fobj (pull Λ j) B)).inv
    (tensorPull_inv_natural_right Λ i A' ci)
    (tensorPull_inv_natural_left Λ i α (fobj (pull Λ j) B))


set_option maxHeartbeats 4000000 in
-- Native derived functor endpoints require a larger checking limit.
private theorem restriction_composition (d : Diagram j k T Tb)
    (K : D Λ X) (L : D Λ Y) :
    (secondOpenRestriction Λ d K L ≫
      fmap (pull Λ d.k₁) (firstOpenRestriction Λ d K L)) ≫
        (compTo Λ d.k₁ d.j₁ d.u d.factor (ambient Λ d K L)).hom =
      restriction Λ d K L := by
  let A := fobj (pull Λ d.pb) (fobj (shriek Λ j) K)
  let B := fobj (pull Λ d.qb) (fobj (shriek Λ k) L)
  let cA := compTo Λ d.k₁ d.r d.p d.k₁_r K
  let cB := compTo Λ d.j₁ d.qb d.s d.j₁_qb (fobj (shriek Λ k) L)
  let a := fmap (pull Λ d.r) (openUnit Λ j K) ≫
    pullSquareInv Λ d.first.toCommSq (fobj (shriek Λ j) K)
  let b := fmap (pull Λ d.q) (openUnit Λ k L) ≫
    pullSquareInv Λ d.second.toCommSq (fobj (shriek Λ k) L)
  have h12 : secondOpenRestriction Λ d K L ≫
      fmap (pull Λ d.k₁) (firstOpenRestriction Λ d K L) =
      ((cA.inv ≫ fmap (pull Λ d.k₁) a) ⊗ₛₘ
        (b ≫ fmap (pull Λ d.k₁) cB.inv)) ≫
        (tensorPullIso Λ d.k₁ (fobj (pull Λ d.j₁) A) (fobj (pull Λ d.j₁) B)).inv ≫
          fmap (pull Λ d.k₁) (tensorPullIso Λ d.j₁ A B).inv := by
    dsimp only [firstOpenRestriction, secondOpenRestriction, tensorMap]
    exact native_tensor_composition Λ d.k₁ d.j₁ A B
      (fobj (pull Λ d.r) K) (fobj (pull Λ d.s) (fobj (shriek Λ k) L))
      (fobj (pull Λ d.p) K) (fobj (pull Λ d.q) L) a cB.inv cA.inv b
  have hl : (cA.inv ≫ fmap (pull Λ d.k₁) a) ≫
        (compTo Λ d.k₁ d.j₁ d.u d.factor A).hom =
      fmap (pull Λ d.p) (openUnit Λ j K) ≫
        squareInv Λ d.u d.pb d.p j d.left (fobj (shriek Λ j) K) := by
    have hn := compTo_inv_natural Λ d.k₁ d.r d.p d.k₁_r (openUnit Λ j K)
    dsimp only [a, A, cA]
    simp only [fmap_comp, Category.assoc]
    rw [← Category.assoc, hn, Category.assoc]
    exact congrArg (fmap (pull Λ d.p) (openUnit Λ j K) ≫ ·)
      (scalar_pullback_path Λ d.first.toCommSq d.k₁ d.p d.u
        d.k₁_r d.factor d.left (fobj (shriek Λ j) K))
  have hr : (b ≫ fmap (pull Λ d.k₁) cB.inv) ≫
        (compTo Λ d.k₁ d.j₁ d.u d.factor B).hom =
      fmap (pull Λ d.q) (openUnit Λ k L) ≫
        squareInv Λ d.u d.qb d.q k d.right (fobj (shriek Λ k) L) := by
    dsimp only [b, B, cB]
    simp only [Category.assoc]
    exact congrArg (fmap (pull Λ d.q) (openUnit Λ k L) ≫ ·)
      (scalar_pullback_post_path Λ d.q k d.k₁ d.j₁ d.qb d.s d.u
        d.j₁_qb d.factor d.second.toCommSq d.right (fobj (shriek Λ k) L))
  have ht := tensor_factor
    (cA.inv ≫ fmap (pull Λ d.k₁) a) (b ≫ fmap (pull Λ d.k₁) cB.inv)
    ((tensorPullIso Λ d.k₁ (fobj (pull Λ d.j₁) A) (fobj (pull Λ d.j₁) B)).inv ≫
      fmap (pull Λ d.k₁) (tensorPullIso Λ d.j₁ A B).inv)
    (tensorPullIso Λ d.u A B).inv
    (compTo Λ d.k₁ d.j₁ d.u d.factor A).hom
    (compTo Λ d.k₁ d.j₁ d.u d.factor B).hom
    (secondOpenRestriction Λ d K L ≫ fmap (pull Λ d.k₁) (firstOpenRestriction Λ d K L))
    (compTo Λ d.k₁ d.j₁ d.u d.factor (A ⊗ₛ B)).hom
    (by simpa only [Category.assoc] using h12)
    (by simpa only [Category.assoc] using
      scalar_tensorPull_factor Λ d.k₁ d.j₁ d.u d.factor A B)
  rw [hl, hr] at ht
  simpa only [restriction, tensorMap, inside, ambient, tensor, A, B] using ht


open CategoryTheory.Functor

private theorem compTo_hom_natural {U V Z : Scheme.{u}}
    (i : U ⟶ V) (j : V ⟶ Z) (h : U ⟶ Z) (e : i ≫ j = h)
    {K L : D Λ Z} (f : K ⟶ L) :
    (compTo Λ i j h e K).hom ≫ fmap (pull Λ h) f =
      fmap (pull Λ i) (fmap (pull Λ j) f) ≫ (compTo Λ i j h e L).hom := by
  subst h
  simpa only [compTo, compIsoComponent, fmap, fobj, pull, eqToIso_refl, Iso.trans_refl,
    Iso.symm_hom, Iso.app_inv,
    Functor.comp_map] using (leftDerivedUpperStarComp Λ i j).inv.naturality f |>.symm


private def compositionUnit {C E G : Type*} [Category C] [Category E] [Category G]
    {L : C ⥤ E} {R : E ⥤ C} {M : E ⥤ G} {S : G ⥤ E}
    (a : L ⊣ R) (b : M ⊣ S) (K : C) :
    K ⟶ fobj R (fobj S (fobj M (fobj L K))) :=
  unitComponent a K ≫ fmap R (unitComponent b (fobj L K))


private theorem comp_unit_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R R' : D ⥤ C} {M : D ⥤ E} {S S' : E ⥤ D}
    (a : L ⊣ R) (b : M ⊣ S) (t : R ≅ R') (v : S ≅ S') (K : C) :
    ((a.ofNatIsoRight t).comp (b.ofNatIsoRight v)).unit.app K =
      (a.comp b).unit.app K ≫
        (isoWhiskerRight v R ≪≫ isoWhiskerLeft S' t).hom.app ((L ⋙ M).obj K) := by
  simp only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, whiskerLeft_app, Iso.trans_hom, isoWhiskerRight_hom,
    whiskerRight_app, isoWhiskerLeft_hom, Functor.map_comp, Category.assoc]
  rw [← t.hom.naturality_assoc]
  rw [← t.hom.naturality]
  rfl


private theorem composed_unique_unit
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R R' : D ⥤ C} {M : D ⥤ E} {S S' : E ⥤ D}
    {N : C ⥤ E} {T T' : E ⥤ C}
    (a : L ⊣ R) (b : M ⊣ S) (c : N ⊣ T)
    (t : R ≅ R') (v : S ≅ S') (w : T ≅ T') (e : T ≅ S ⋙ R) (K : C) :
    ((a.ofNatIsoRight t).comp (b.ofNatIsoRight v)).unit.app K ≫
        (S' ⋙ R').map ((Adjunction.leftAdjointUniq (a.comp b)
          (c.ofNatIsoRight e)).hom.app K) =
      (c.ofNatIsoRight w).unit.app K ≫
        (w.symm ≪≫ e ≪≫ isoWhiskerRight v R ≪≫ isoWhiskerLeft S' t).hom.app
          (N.obj K) := by
  rw [comp_unit_transport]
  rw [Category.assoc, ← NatTrans.naturality]
  rw [← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app]
  simp [Adjunction.ofNatIsoRight_unit]


private theorem pComp_formula {U V Z : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ Z) :
    (leftDerivedUpperStarComp Λ i j).hom =
      (leftDerivedUpperStarIsoMapDerivedCategory Λ (i ≫ j)).hom ≫
        (Functor.mapDerivedCategoryNatIso (upperStarComp Λ i j)).hom ≫
        (Functor.mapDerivedCategoryCompIso _ _).hom ≫
        Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ j).inv
          D((i)^*⟦Λ⟧) ≫
        Functor.whiskerLeft (P Λ j) (leftDerivedUpperStarIsoMapDerivedCategory Λ i).inv := by
  simp [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory]


private theorem openComp_unit {U V Z : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ Z)
    [IsOpenImmersion i] [IsOpenImmersion j] (K : D Λ U) :
    ((oa Λ i).comp (oa Λ j)).unit.app K ≫
        (P Λ j ⋙ P Λ i).map ((CompactSupportComposition.openComp Λ i j).hom.app K) =
      (oa Λ (i ≫ j)).unit.app K ≫
        (leftDerivedUpperStarComp Λ i j).hom.app ((J Λ (i ≫ j)).obj K) := by
  have h := composed_unique_unit
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (i ≫ j))
    (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ i).symm
    (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm
    (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ (i ≫ j)).symm
    (Functor.mapDerivedCategoryNatIso (upperStarComp Λ i j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _) K
  rw [pComp_formula]
  simpa only [CompactSupportComposition.openComp, oa,
    derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction,
    leftDerivedUpperStarIsoMapDerivedCategory, P, J, D,
    leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion,
    Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.assoc] using h


private theorem scalarOpenFactor_unit {U V Z : Scheme.{u}}
    (i : U ⟶ V) (j : V ⟶ Z) (h : U ⟶ Z)
    [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion h]
    (e : i ≫ j = h) (K : D Λ U) :
    compositionUnit (adj Λ i) (adj Λ j) K ≫
      fmap (pull Λ i) (fmap (pull Λ j) (openFactorComponent Λ i j h e K).hom) =
    openUnit Λ h K ≫ (compTo Λ i j h e (fobj (shriek Λ h) K)).inv := by
  subst h
  simpa only [compositionUnit, openUnit, unitComponent, fmap, fobj,
    adj, pull, shriek, openFactorComponent, CompactSupportComposition.openFactor,
    compTo, compIsoComponent, eqToIso_refl, Iso.trans_refl, Iso.refl_hom, Iso.refl_inv,
    Iso.trans_hom, Iso.trans_inv, Category.comp_id, Category.id_comp,
    Iso.symm_inv, Iso.app_hom, Functor.comp_map, Adjunction.comp_unit_app] using
    openComp_unit Λ i j K


private theorem twoStageUnit
    {C E G : Type*} [Category C] [Category E] [Category G]
    {L : C ⥤ E} {R : E ⥤ C} {M : E ⥤ G} {S : G ⥤ E}
    (a : L ⊣ R) (b : M ⊣ S) {W : G} {X : E} {Y : C}
    (e : W ⟶ fobj M X) (r : X ⟶ fobj S W)
    (f : X ⟶ fobj L Y) (s : Y ⟶ fobj R X)
    (he : r ≫ fmap S e = unitComponent b X)
    (hf : s ≫ fmap R f = unitComponent a Y) :
    (s ≫ fmap R r) ≫ fmap R (fmap S (e ≫ fmap M f)) = compositionUnit a b Y := by
  dsimp only [compositionUnit, unitComponent, fmap, fobj] at *
  simp only [Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc, he]
  rw [← R.map_comp, b.unit_naturality, R.map_comp, ← Category.assoc, hf]

private theorem normalized_composition_scalar
    {C E G : Type*} [Category C] [Category E] [Category G]
    {L : C ⥤ E} {R : E ⥤ C} {M : E ⥤ G} {S : G ⥤ E}
    {N : C ⥤ G} {T : G ⥤ C}
    (a : L ⊣ R) (b : M ⊣ S) (c : N ⊣ T) {W : G} {Y : C}
    (e : W ⟶ fobj M (fobj L Y)) (r : Y ⟶ fobj R (fobj S W))
    (u : fobj M (fobj L Y) ⟶ fobj N Y)
    (qW : fobj R (fobj S W) ≅ fobj T W)
    (qN : fobj R (fobj S (fobj N Y)) ≅ fobj T (fobj N Y))
    (h : r ≫ fmap R (fmap S e) = compositionUnit a b Y)
    (hu : compositionUnit a b Y ≫ fmap R (fmap S u) = unitComponent c Y ≫ qN.inv)
    (hn : qW.hom ≫ fmap T (e ≫ u) = fmap R (fmap S (e ≫ u)) ≫ qN.hom) :
    (r ≫ qW.hom) ≫ fmap T (e ≫ u) = unitComponent c Y := by
  rw [Category.assoc, hn]
  simp only [fmap_comp, Category.assoc]
  rw [← Category.assoc r, h]
  rw [← Category.assoc (compositionUnit a b Y), hu]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option maxHeartbeats 4000000 in
-- Native derived functor endpoints require a larger checking limit.
private theorem comparison_unit (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) :
    restriction Λ d K L ≫ fmap (pull Λ d.u) (comparison Λ d K L) =
      openUnit Λ d.u (inside Λ d K L) := by
  rw [comparison_factorization, ← restriction_composition]
  have h := normalized_composition_scalar
    (adj Λ d.k₁) (adj Λ d.j₁) (adj Λ d.u)
    (firstOpenComparison Λ d K L ≫ fmap (shriek Λ d.j₁) (secondOpenComparison Λ d K L))
    (secondOpenRestriction Λ d K L ≫ fmap (pull Λ d.k₁) (firstOpenRestriction Λ d K L))
    (openFactorComponent Λ d.k₁ d.j₁ d.u d.factor (inside Λ d K L)).hom
    (compTo Λ d.k₁ d.j₁ d.u d.factor (ambient Λ d K L))
    (compTo Λ d.k₁ d.j₁ d.u d.factor (fobj (shriek Λ d.u) (inside Λ d K L)))
    (twoStageUnit (adj Λ d.k₁) (adj Λ d.j₁)
      (firstOpenComparison Λ d K L) (firstOpenRestriction Λ d K L)
      (secondOpenComparison Λ d K L) (secondOpenRestriction Λ d K L)
      (firstOpen_unit Λ d K L) (secondOpen_unit Λ d K L))
    (scalarOpenFactor_unit Λ d.k₁ d.j₁ d.u d.factor (inside Λ d K L))
    (compTo_hom_natural Λ d.k₁ d.j₁ d.u d.factor
      ((firstOpenComparison Λ d K L ≫
        fmap (shriek Λ d.j₁) (secondOpenComparison Λ d K L)) ≫
        (openFactorComponent Λ d.k₁ d.j₁ d.u d.factor (inside Λ d K L)).hom))
  simpa only [openUnit, Category.assoc] using h

variable {W Wb T₁₂ T₂₃ Tb₁₂ Tb₂₃ : Scheme.{u}} {l : W ⟶ Wb}
  [IsOpenImmersion l]

private instance fmapIsIso {C E : Type*} [Category C] [Category E] (F : C ⥤ E)
    {A B : C} (f : A ⟶ B) [IsIso f] : IsIso (fmap F f) := by
  unfold fmap
  infer_instance

private instance mapTensorIsIso {C : Type*} [Category C] [MonoidalCategory C]
    {A B A' B' : C} (f : A ⟶ A') (g : B ⟶ B') [IsIso f] [IsIso g] :
    IsIso (mapTensor f g) := by
  unfold mapTensor
  infer_instance

private instance unitComponentIsIso {C E : Type*} [Category C] [Category E]
    {L : C ⥤ E} {R : E ⥤ C} (a : L ⊣ R) [IsIso a.unit] (N : C) :
    IsIso (unitComponent a N) := by
  unfold unitComponent
  infer_instance

private instance openUnitComponentIsIso {U Z : Scheme.{u}} (i : U ⟶ Z)
    [IsOpenImmersion i] (N : D Λ U) : IsIso (openUnit Λ i N) := by
  unfold openUnit
  infer_instance

private instance betaMapIsIso {A B A' B' : Scheme.{u}}
    {i : A ⟶ B} {i' : A' ⟶ B'} {w : A' ⟶ A} {v : B' ⟶ B}
    [IsOpenImmersion i] [IsOpenImmersion i'] (sq : IsPullback w i' i v)
    (K : D Λ A) : IsIso (betaMap Λ sq K) := by
  unfold betaMap compositeComponent
  infer_instance

private instance squareInvIsIso {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Z)
    (h : T ⟶ Y) (i : Y ⟶ Z) (e : f ≫ g = h ≫ i) (N : D Λ Z) :
    IsIso (squareInv Λ f g h i e N) := by
  unfold squareInv compositeComponent
  infer_instance

private theorem sigma_isIso (Z : Scheme.{u}) (A B : D Λ Z) :
    IsIso (sigma Λ Z A B) := by
  unfold sigma
  infer_instance


private theorem gamma_isIso {U Z : Scheme.{u}} (i : U ⟶ Z) [IsOpenImmersion i]
    (A : D Λ U) (B : D Λ Z) : IsIso (gamma Λ i A B) := by
  unfold gamma
  infer_instance


private theorem rho_isIso {U Z : Scheme.{u}} (i : U ⟶ Z) [IsOpenImmersion i]
    (A : D Λ Z) (B : D Λ U) : IsIso (rho Λ i A B) := by
  have := sigma_isIso Λ Z A (fobj (shriek Λ i) B)
  have := gamma_isIso Λ i B A
  have := sigma_isIso Λ U B (fobj (pull Λ i) A)
  unfold rho
  infer_instance


private theorem comparison_isIso
    (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) :
    IsIso (comparison Λ d K L) := by
  have := gamma_isIso Λ d.j₁ (fobj (pull Λ d.r) K)
    (fobj (pull Λ d.qb) (fobj (shriek Λ k) L))
  have := rho_isIso Λ d.k₁ (fobj (pull Λ d.r) K) (fobj (pull Λ d.q) L)
  unfold comparison tensorMap mapTensor
  infer_instance


private theorem oppositeComparison_isIso
    (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) :
    IsIso (oppositeComparison Λ d K L) := by
  have := comparison_isIso Λ d.swap L K
  have := sigma_isIso Λ Tb (fobj (pull Λ d.pb) (fobj (shriek Λ j) K))
    (fobj (pull Λ d.qb) (fobj (shriek Λ k) L))
  have := sigma_isIso Λ T (fobj (pull Λ d.q) L) (fobj (pull Λ d.p) K)
  change IsIso (sigma Λ Tb (fobj (pull Λ d.pb) (fobj (shriek Λ j) K))
    (fobj (pull Λ d.qb) (fobj (shriek Λ k) L)) ≫ comparison Λ d.swap L K ≫
      fmap (shriek Λ d.u) (sigma Λ T (fobj (pull Λ d.q) L) (fobj (pull Λ d.p) K)))
  infer_instance


private theorem restriction_isIso
    (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) :
    IsIso (restriction Λ d K L) := by
  have := openUnit_isIso Λ j
  have := openUnit_isIso Λ k
  unfold restriction tensorMap mapTensor
  infer_instance


private theorem supported_restriction_injective
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {E F : D} {N : C} (e : E ≅ fobj L N)
    {f g : E ⟶ F} (h : fmap R f = fmap R g) : f = g := by
  dsimp only [fobj, fmap, objTensor, mapTensor, unitComponent] at *
  apply (cancel_epi e.inv).1
  apply (a.homEquiv N F).injective
  change a.unit.app N ≫ R.map (e.inv ≫ f) = a.unit.app N ≫ R.map (e.inv ≫ g)
  simp only [Functor.map_comp, h]


private theorem native_tensor_swap_restriction {U Z : Scheme.{u}} (i : U ⟶ Z)
    (A B : D Λ Z) {K L : D Λ U}
    (f : K ⟶ fobj (pull Λ i) A) (g : L ⟶ fobj (pull Λ i) B) :
    sigma Λ U K L ≫ ((g ⊗ₛₘ f) ≫ (tensorPullIso Λ i B A).inv) =
      ((f ⊗ₛₘ g) ≫ (tensorPullIso Λ i A B).inv) ≫
        fmap (pull Λ i) (sigma Λ Z A B) := by
  exact tensor_swap_explicit f g (sigma Λ U K L)
    (sigma Λ U (fobj (pull Λ i) A) (fobj (pull Λ i) B))
    (tensorPullIso Λ i A B).inv (tensorPullIso Λ i B A).inv
    (fmap (pull Λ i) (sigma Λ Z A B))
    (sigma_natural Λ U f g) (tensorPullIso_inv_braiding Λ i A B)


set_option maxHeartbeats 4000000 in
-- Native derived functor endpoints require a larger checking limit.
private theorem restriction_swap (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) :
    sigma Λ T (fobj (pull Λ d.p) K) (fobj (pull Λ d.q) L) ≫ restriction Λ d.swap L K =
      restriction Λ d K L ≫
        fmap (pull Λ d.u) (sigma Λ Tb
          (fobj (pull Λ d.pb) (fobj (shriek Λ j) K))
          (fobj (pull Λ d.qb) (fobj (shriek Λ k) L))) := by
  let A := fobj (pull Λ d.pb) (fobj (shriek Λ j) K)
  let B := fobj (pull Λ d.qb) (fobj (shriek Λ k) L)
  let f := fmap (pull Λ d.p) (openUnit Λ j K) ≫
    squareInv Λ d.u d.pb d.p j d.left (fobj (shriek Λ j) K)
  let g := fmap (pull Λ d.q) (openUnit Λ k L) ≫
    squareInv Λ d.u d.qb d.q k d.right (fobj (shriek Λ k) L)
  have ht := native_tensor_swap_restriction Λ d.u A B f g
  dsimp only [restriction, tensorMap]
  exact ht



private theorem opposite_unit
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {E E' : D} {N N' : C}
    (g : E' ⟶ fobj L N') (r : N ⟶ fobj R E) (r' : N' ⟶ fobj R E')
    (s : E ⟶ E') (t : N ⟶ N') (t' : N' ⟶ N)
    (hr : t ≫ r' = r ≫ fmap R s)
    (hg : r' ≫ fmap R g = unitComponent a N') (ht : t ≫ t' = 𝟙 N) :
    r ≫ fmap R (s ≫ g ≫ fmap L t') = unitComponent a N := by
  dsimp only [fobj, fmap, objTensor, mapTensor, unitComponent] at *
  simp only [Functor.map_comp]
  rw [← Category.assoc r, ← hr, Category.assoc, reassoc_of% hg,
    a.unit_naturality, ← Category.assoc, ht, Category.id_comp]


private theorem signed_from_opposite
    {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {E E' : D} {N N' : C}
    (f : E ⟶ fobj L N) (g : E' ⟶ fobj L N') (s : E ⟶ E')
    (t : N ⟶ N') (t' : N' ⟶ N)
    (he : s ≫ g ≫ fmap L t' = f) (ht : t' ≫ t = 𝟙 N') :
    f ≫ fmap L t = s ≫ g := by
  dsimp only [fobj, fmap, objTensor, mapTensor, unitComponent] at *
  rw [← he, Category.assoc, Category.assoc, ← L.map_comp, ht, L.map_id,
    Category.comp_id]


set_option maxHeartbeats 4000000 in
-- Native derived functor endpoints require a larger checking limit.
private theorem binary_of_normalization (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y)
    (h : restriction Λ d K L ≫ fmap (pull Λ d.u) (comparison Λ d K L) =
      openUnit Λ d.u (inside Λ d K L))
    (hs : restriction Λ d.swap L K ≫ fmap (pull Λ d.u) (comparison Λ d.swap L K) =
      openUnit Λ d.u (inside Λ d.swap L K)) : BinaryAssertion Λ d K L := by
  have hi := comparison_isIso Λ d K L
  have hr := restriction_isIso Λ d K L
  have ho : restriction Λ d K L ≫ fmap (pull Λ d.u) (oppositeComparison Λ d K L) =
      openUnit Λ d.u (inside Λ d K L) := by
    exact opposite_unit (adj Λ d.u) (comparison Λ d.swap L K)
      (restriction Λ d K L) (restriction Λ d.swap L K)
      (sigma Λ Tb _ _) (sigma Λ T _ _) (sigma Λ T _ _)
      (restriction_swap Λ d K L) hs (sigma_twice Λ T _ _)
  have he : oppositeComparison Λ d K L = comparison Λ d K L := by
    apply supported_restriction_injective (adj Λ d.u) (asIso (comparison Λ d K L))
    apply (cancel_epi (restriction Λ d K L)).1
    exact ho.trans h.symm
  refine ⟨hi, oppositeComparison_isIso Λ d K L, h, he, ?_⟩
  exact signed_from_opposite (shriek Λ d.u) (comparison Λ d K L)
    (comparison Λ d.swap L K) (sigma Λ Tb _ _) (sigma Λ T _ _) (sigma Λ T _ _)
    he (sigma_twice Λ T _ _)


/-- The native open product is invertible, restricts to identity, and is independent
of the factorization with the signed swap equation.
Source: Coherence (i), open-product normalization
(blueprint: lem-sf-condensed-product-compactification-map).
Proof: open base change and the open projection maps are invertible. Their normalized
units show term by term that comparison restricts to identity. The opposite chain has
the same restriction. The invertible open unit makes extension fully faithful, so the
two maps agree. Apply the same argument after signed factor interchange. The two Koszul
signs cancel on restriction. No reduction of coefficients is used. -/
theorem openProduct_normalization
    (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) : BinaryAssertion Λ d K L := by
  exact binary_of_normalization Λ d K L (comparison_unit Λ d K L)
    (comparison_unit Λ d.swap L K)

end AlgebraicGeometry.ProEtale.CondensedRing.ProductCompactificationMap
