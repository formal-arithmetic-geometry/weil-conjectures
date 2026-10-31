/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSix
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.RootTowerCoordinateFace
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.ScalarModuleMonoidalClosed
import WeilConjectures.AlgebraicGeometry.ScalarModuleBraidedCategory
import WeilConjectures.AlgebraicGeometry.ScalarModuleDerivedMonoidal
import all WeilConjectures.AlgebraicGeometry.ScalarGeometricExchangeRectangle
import WeilConjectures.AlgebraicGeometry.CondensedCtfSixFunctorStability

/-! # Scalar preservation and the exact-pullback exchange rectangle -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

/-! The private helpers are elaborated with transparency respected and the canonical scalar
module instances registered locally; the public theorem below is elaborated outside this
section, so its statement keeps the global instance terms of the frozen statement. -/
section Helpers
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
  scalarDirectImageMate scalarDirectImagePullbackData scalarSixChange upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  CondensedRing.upperStar AlgebraicGeometry.ProEtale.upperStar
attribute [local implicit_reducible] scalarSixPull TwoSquare moduleObjectDerivedPushforward

attribute [local instance] scalarModuleMonoidalClosed scalarModuleBraidedCategory
  scalarModuleHasDerivedMonoidalCategory

private theorem scalarCompInverse {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {U V W : Scheme.{u}} (i : U ⟶ V) (h : V ⟶ W)
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X W)) :
    (scalarSixPullComp Λ' i h).hom.app ((scalarSixChange a W).obj N) ≫
        (scalarSixPull Λ' i).map ((scalarDirectImagePullbackData.theta a h).inv.app N) ≫
        (scalarDirectImagePullbackData.theta a i).inv.app ((scalarSixPull Λ h).obj N) =
      (scalarDirectImagePullbackData.theta a (i ≫ h)).inv.app N ≫
        (scalarSixChange a U).map ((scalarSixPullComp Λ i h).hom.app N) := by
  have ho := IsIso.inv_eq_inv.mpr (scalarDirectImagePullbackData.composition a i h N)
  simp only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app] at ho
  apply (cancel_mono ((scalarSixChange a U).map
    ((scalarSixPullComp Λ i h).inv.app N))).mp
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  have ht := congrArg (fun z ↦ (scalarSixPullComp Λ' i h).hom.app
      ((scalarSixChange a W).obj N) ≫ z) ho
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc] at ht
  rw [← ht]
  rw [(scalarSixChange a U).map_id ((scalarSixPull Λ (i ≫ h)).obj N)]
  exact (Category.comp_id ((scalarDirectImagePullbackData.theta a (i ≫ h)).inv.app N)).symm

private theorem scalarCongrInverse {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {U V : Scheme.{u}} {h j : U ⟶ V} (w : h = j)
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X V)) :
    (eqToIso (congrArg (scalarSixPull Λ') w)).hom.app ((scalarSixChange a V).obj N) ≫
        (scalarDirectImagePullbackData.theta a j).inv.app N =
      (scalarDirectImagePullbackData.theta a h).inv.app N ≫
        (scalarSixChange a U).map
          ((eqToIso (congrArg (scalarSixPull Λ) w)).hom.app N) := by
  subst j
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rw [(scalarSixChange a U).map_id ((scalarSixPull Λ h).obj N)]
  exact (Category.comp_id (obj :=
    DerivedCategory (ModuleRingedComparison.internalModules Λ'.X U)) _).symm

private theorem scalarSquareNormalization (Λ : ScalarSixRing.{u})
    {X' X Y' Y : Scheme.{u}} (u : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (w : u ≫ f = f' ≫ g) :
    RootCoordinateFace.squareUpper Λ.X u f' f g w =
      (scalarSixPullComp Λ f' g).symm ≪≫
        eqToIso (congrArg (scalarSixPull Λ) w.symm) ≪≫ scalarSixPullComp Λ u f := by
  rfl

private theorem pointwiseSquare
    {C D : Type*} [Category C] [Category D] (T : C ⥤ D)
    {P Q R S : C} {P' Q' R' S' Z Z' : D}
    (c : P ⟶ Q) (ci : Q ⟶ P) (d : R ⟶ S) (t : P ⟶ R)
    (c' : P' ⟶ Q') (ci' : Q' ⟶ P') (d' : R' ⟶ S') (t' : P' ⟶ R')
    (p₀ : Q' ⟶ Z) (p₁ : Z ⟶ T.obj Q)
    (q₀ : S' ⟶ Z') (q₁ : Z' ⟶ T.obj S)
    (k : P' ⟶ T.obj P) (l : R' ⟶ T.obj R)
    (s : Q ⟶ S) (s' : Q' ⟶ S')
    (hs : s = ci ≫ t ≫ d) (hs' : s' = ci' ≫ t' ≫ d')
    (hc : c' ≫ p₀ ≫ p₁ = k ≫ T.map c)
    (hd : d' ≫ q₀ ≫ q₁ = l ≫ T.map d)
    (ht : t' ≫ l = k ≫ T.map t)
    (hci : c ≫ ci = 𝟙 P) (hc'i : c' ≫ ci' = 𝟙 P')
    (hic' : ci' ≫ c' = 𝟙 Q') :
    p₀ ≫ p₁ ≫ T.map s = s' ≫ q₀ ≫ q₁ := by
  have h : c' ≫ p₀ ≫ p₁ ≫ T.map s = c' ≫ s' ≫ q₀ ≫ q₁ := by
    rw [hs, hs']
    simp only [Category.assoc, T.map_comp]
    rw [reassoc_of% hc, reassoc_of% hc'i, hd, reassoc_of% ht]
    rw [← T.map_comp_assoc, hci, T.map_id, Category.id_comp]
  have h' := congrArg (fun z ↦ ci' ≫ z) h
  simpa only [← Category.assoc, hic', Category.id_comp] using h'

private theorem compositorHom
    {A B : Type*} [Category A] [Category B]
    {F₀ F₁ F₂ F₃ : A ⥤ B} (c : F₀ ≅ F₁) (d : F₂ ≅ F₃) (t : F₀ ≅ F₂)
    (N : A) :
    ((c.symm ≪≫ t ≪≫ d).hom.app N) =
      c.inv.app N ≫ t.hom.app N ≫ d.hom.app N := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]

private theorem scalarSquareHomNormalization (Λ : ScalarSixRing.{u})
    {X' X Y' Y : Scheme.{u}} (u : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (w : u ≫ f = f' ≫ g)
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (RootCoordinateFace.squareUpper Λ.X u f' f g w).hom.app N =
      (scalarSixPullComp Λ f' g).inv.app N ≫
        (eqToIso (congrArg (scalarSixPull Λ) w.symm)).hom.app N ≫
          (scalarSixPullComp Λ u f).hom.app N := by
  exact (congrArg (fun e ↦ e.hom.app N)
    (scalarSquareNormalization Λ u f' f g w)).trans
      (compositorHom (scalarSixPullComp Λ f' g) (scalarSixPullComp Λ u f)
        (eqToIso (congrArg (scalarSixPull Λ) w.symm)) N)

private theorem scalarComparisonEndpoints
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hcd : BaseFieldFiniteCD ell k) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a)
    {X' X Y' Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (_sq : ChosenCartesianSquare u.left f'.left f.left g.left)
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    (constantModelBoundedConstructible Λ'.X Y'.left ⊓
        DerivedCategory.finiteTorAmplitude _)
      ((scalarSixChange a Y'.left).obj
        ((scalarSixPull Λ g.left).obj
          ((RootCoordinateFace.lower Λ.X f.left).obj K.obj))) ∧
    (constantModelBoundedConstructible Λ'.X Y'.left ⊓
        DerivedCategory.finiteTorAmplitude _)
      ((RootCoordinateFace.lower Λ'.X f'.left).obj
        ((scalarSixPull Λ' u.left).obj
          ((scalarSixChange a X.left).obj K.obj))) ∧
    IsIso ((scalarSixPullHom a g.left).app
      ((RootCoordinateFace.lower Λ.X f.left).obj K.obj)) ∧
    IsIso ((scalarDirectImageMate a f.left).app K.obj) ∧
    IsIso ((scalarDirectImageMate a f'.left).app
      ((scalarSixPull Λ u.left).obj K.obj)) ∧
    IsIso ((scalarSixPullHom a u.left).app K.obj) := by
  have hs := scalarSixCoefficientComparison ell k hcd a ha
  have hΛ := listedCoefficientCtf ell a ha
  have hpush := (condensedCtfSixFunctorStability Λ.X ell k hcd f hΛ.1).2.1 K
  let R : ConstantModelConstructibleFiniteTor Λ.X Y.left :=
    ⟨(RootCoordinateFace.lower Λ.X f.left).obj K.obj, hpush⟩
  have pullMem : ∀ {S T : Over (Spec (.of k))}
      [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
      [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
      (v : S ⟶ T) (L : ConstantModelConstructibleFiniteTor Λ.X T.left),
      (constantModelBoundedConstructible Λ.X S.left ⊓
        DerivedCategory.finiteTorAmplitude _) ((scalarSixPull Λ v.left).obj L.obj) := by
    intro S T _ _ _ _ _ _ v L
    have := (constantModelConstructibleFiniteTor_wellDefined Λ.X S.left).2.1
    have := (constantModelConstructibleFiniteTor_wellDefined Λ.X S.left).2.2.2.1
    exact ObjectProperty.prop_of_iso _
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ.X v.left).app L.obj)
      ((condensedCtfSixFunctorStability Λ.X ell k hcd v hΛ.1).1 L)
  let U : ConstantModelConstructibleFiniteTor Λ.X X'.left :=
    ⟨(scalarSixPull Λ u.left).obj K.obj, pullMem u K⟩
  let G : ConstantModelConstructibleFiniteTor Λ.X Y'.left :=
    ⟨(scalarSixPull Λ g.left).obj R.obj, pullMem g R⟩
  refine ⟨hs.1 Y' G, ?_, (hs.2.1 Y' Y g).1 R,
    ((hs.2.1 X Y f).2.1 K).1, ((hs.2.1 X' Y' f').2.1 U).1,
    (hs.2.1 X' X u).1 K⟩
  · have := (constantModelConstructibleFiniteTor_wellDefined Λ'.X X'.left).2.1
    have := (constantModelConstructibleFiniteTor_wellDefined Λ'.X X'.left).2.2.2.1
    have hU := ObjectProperty.prop_of_iso
      (constantModelBoundedConstructible Λ'.X X'.left ⊓
        DerivedCategory.finiteTorAmplitude _)
      ((scalarDirectImagePullbackData.theta a u.left).app K.obj) (hs.1 X' U)
    exact (condensedCtfSixFunctorStability Λ'.X ell k hcd f' hΛ.2.1).2.1
      ⟨_, hU⟩

private theorem pull_eqRoot (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarSixPull Λ f = RootCoordinateFace.upper Λ.X f := by
  rfl

private theorem mateHEq
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ : F ⥤ E}
    {G G' : C ⥤ E} {H H' : D ⥤ F}
    (h₁ : L₁ = L₁') (h₂ : L₂ = L₂') (hG : G = G') (hH : H = H')
    (a₁ : L₁ ⊣ R₁) (a₁' : L₁' ⊣ R₁) (ha₁ : HEq a₁ a₁')
    (a₂ : L₂ ⊣ R₂) (a₂' : L₂' ⊣ R₂) (ha₂ : HEq a₂ a₂')
    (s : TwoSquare G L₁ L₂ H) (s' : TwoSquare G' L₁' L₂' H') (hs : HEq s s') :
    HEq ((mateEquiv a₁ a₂ s).natTrans) ((mateEquiv a₁' a₂' s').natTrans) := by
  subst L₁' L₂' G' H'
  cases (eq_of_heq ha₁)
  cases (eq_of_heq ha₂)
  cases (eq_of_heq hs)
  rfl

private theorem directImageMate_root {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarDirectImageMate a f =
      (mateEquiv (RootCoordinateFace.adjunction Λ.X f)
        (RootCoordinateFace.adjunction Λ'.X f)
        (TwoSquare.mk _ _ _ _ (scalarDirectImagePullbackData.theta a f).inv)).natTrans := by
  simp only [scalarDirectImageMate]

private theorem directImageMate_native {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarDirectImageMate a f =
      (mateEquiv (L₁ := scalarSixPull Λ f) (L₂ := scalarSixPull Λ' f)
        (RootCoordinateFace.adjunction Λ.X f)
        (RootCoordinateFace.adjunction Λ'.X f)
        (TwoSquare.mk _ _ _ _ (scalarDirectImagePullbackData.theta a f).inv)).natTrans := by
  exact (directImageMate_root a f).trans (eq_of_heq
    (mateHEq (pull_eqRoot Λ f).symm (pull_eqRoot Λ' f).symm rfl rfl
      (RootCoordinateFace.adjunction Λ.X f) (RootCoordinateFace.adjunction Λ.X f) HEq.rfl
      (RootCoordinateFace.adjunction Λ'.X f) (RootCoordinateFace.adjunction Λ'.X f) HEq.rfl
      (TwoSquare.mk _ _ _ _ (scalarDirectImagePullbackData.theta a f).inv)
      (TwoSquare.mk _ _ _ _ (scalarDirectImagePullbackData.theta a f).inv) HEq.rfl))

private theorem natAppHEq
    {C D : Type*} [Category C] [Category D] {F F' G G' : C ⥤ D}
    (hF : F = F') (hG : G = G') (t : F ⟶ G) (t' : F' ⟶ G') (ht : HEq t t')
    (N : C) : HEq (t.app N) (t'.app N) := by
  subst F' G'
  cases (eq_of_heq ht)
  rfl

private def nativeSquare (Λ : ScalarSixRing.{u})
    {X' X Y' Y : Scheme.{u}} (u : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (w : u ≫ f = f' ≫ g) :
    scalarSixPull Λ g ⋙ scalarSixPull Λ f' ⟶ scalarSixPull Λ f ⋙ scalarSixPull Λ u :=
  (RootCoordinateFace.squareUpper Λ.X u f' f g w).hom

private theorem nativeSquare_app (Λ : ScalarSixRing.{u})
    {X' X Y' Y : Scheme.{u}} (u : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (w : u ≫ f = f' ≫ g)
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (nativeSquare Λ u f' f g w).app N =
      (RootCoordinateFace.squareUpper Λ.X u f' f g w).hom.app N := by
  exact eq_of_heq (natAppHEq
    (congrArg₂ (fun P Q ↦ P ⋙ Q) (pull_eqRoot Λ g) (pull_eqRoot Λ f'))
    (congrArg₂ (fun P Q ↦ P ⋙ Q) (pull_eqRoot Λ f) (pull_eqRoot Λ u))
    (nativeSquare Λ u f' f g w)
    (RootCoordinateFace.squareUpper Λ.X u f' f g w).hom HEq.rfl N)

private def nativeExchange (Λ : ScalarSixRing.{u})
    {X' X Y' Y : Scheme.{u}} (u : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (w : u ≫ f = f' ≫ g) :
    RootCoordinateFace.lower Λ.X f ⋙ scalarSixPull Λ g ⟶
      scalarSixPull Λ u ⋙ RootCoordinateFace.lower Λ.X f' :=
  RootCoordinateFace.exchange Λ.X u f' f g w

private theorem nativeExchange_app (Λ : ScalarSixRing.{u})
    {X' X Y' Y : Scheme.{u}} (u : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (w : u ≫ f = f' ≫ g)
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (nativeExchange Λ u f' f g w).app N =
      (RootCoordinateFace.exchange Λ.X u f' f g w).app N := by
  exact eq_of_heq (natAppHEq
    (congrArg (fun P ↦ RootCoordinateFace.lower Λ.X f ⋙ P) (pull_eqRoot Λ g))
    (congrArg (fun P ↦ P ⋙ RootCoordinateFace.lower Λ.X f') (pull_eqRoot Λ u))
    (nativeExchange Λ u f' f g w)
    (RootCoordinateFace.exchange Λ.X u f' f g w) HEq.rfl N)

private theorem exchange_root (Λ : ScalarSixRing.{u})
    {X' X Y' Y : Scheme.{u}} (u : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (w : u ≫ f = f' ≫ g) :
    RootCoordinateFace.exchange Λ.X u f' f g w =
      (mateEquiv (RootCoordinateFace.adjunction Λ.X f)
        (RootCoordinateFace.adjunction Λ.X f')
        (TwoSquare.mk _ _ _ _ (RootCoordinateFace.squareUpper Λ.X u f' f g w).hom)).natTrans := by
  rfl

private theorem exchange_native (Λ : ScalarSixRing.{u})
    {X' X Y' Y : Scheme.{u}} (u : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (w : u ≫ f = f' ≫ g) :
    nativeExchange Λ u f' f g w =
      (mateEquiv (L₁ := scalarSixPull Λ f) (L₂ := scalarSixPull Λ f')
        (G := scalarSixPull Λ g) (H := scalarSixPull Λ u)
        (RootCoordinateFace.adjunction Λ.X f)
        (RootCoordinateFace.adjunction Λ.X f')
        (TwoSquare.mk _ _ _ _ (nativeSquare Λ u f' f g w))).natTrans := by
  exact (exchange_root Λ u f' f g w).trans (eq_of_heq
    (mateHEq (pull_eqRoot Λ f).symm (pull_eqRoot Λ f').symm
      (pull_eqRoot Λ g).symm (pull_eqRoot Λ u).symm
      (RootCoordinateFace.adjunction Λ.X f) (RootCoordinateFace.adjunction Λ.X f) HEq.rfl
      (RootCoordinateFace.adjunction Λ.X f') (RootCoordinateFace.adjunction Λ.X f') HEq.rfl
      (TwoSquare.mk _ _ _ _ (RootCoordinateFace.squareUpper Λ.X u f' f g w).hom)
      (TwoSquare.mk _ _ _ _ (nativeSquare Λ u f' f g w)) HEq.rfl))


private theorem mapHEq
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    (v : X ⟶ Y) (v' : X' ⟶ Y') (hv : HEq v v') : HEq (F.map v) (F.map v') := by
  subst X' Y'
  cases (eq_of_heq hv)
  rfl

private theorem nativeExchange_map (Λ : ScalarSixRing.{u})
    {X' X Y' Y : Scheme.{u}} (u : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (w : u ≫ f = f' ≫ g)
    {D : Type*} [Category D]
    (T : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y') ⥤ D)
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    T.map ((nativeExchange Λ u f' f g w).app N) =
      T.map ((RootCoordinateFace.exchange Λ.X u f' f g w).app N) := by
  exact eq_of_heq (mapHEq T
    (congrArg (fun P ↦ P.obj ((RootCoordinateFace.lower Λ.X f).obj N)) (pull_eqRoot Λ g))
    (congrArg (fun P ↦ (RootCoordinateFace.lower Λ.X f').obj (P.obj N)) (pull_eqRoot Λ u))
    ((nativeExchange Λ u f' f g w).app N)
    ((RootCoordinateFace.exchange Λ.X u f' f g w).app N)
    (natAppHEq
      (congrArg (fun P ↦ RootCoordinateFace.lower Λ.X f ⋙ P) (pull_eqRoot Λ g))
      (congrArg (fun P ↦ P ⋙ RootCoordinateFace.lower Λ.X f') (pull_eqRoot Λ u))
      (nativeExchange Λ u f' f g w)
      (RootCoordinateFace.exchange Λ.X u f' f g w) HEq.rfl N))

private theorem nativeSquareHomNormalization (Λ : ScalarSixRing.{u})
    {X' X Y' Y : Scheme.{u}} (u : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (w : u ≫ f = f' ≫ g)
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (nativeSquare Λ u f' f g w).app N =
      (scalarSixPullComp Λ f' g).inv.app N ≫
        (eqToIso (congrArg (scalarSixPull Λ) w.symm)).hom.app N ≫
          (scalarSixPullComp Λ u f).hom.app N := by
  exact (nativeSquare_app Λ u f' f g w N).trans
    (scalarSquareHomNormalization Λ u f' f g w N)

private theorem nativeScalarSquareInverse {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X' X Y' Y : Scheme.{u}} (u : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (w : u ≫ f = f' ≫ g)
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (scalarSixPull Λ' f').map ((scalarDirectImagePullbackData.theta a g).inv.app N) ≫
        (scalarDirectImagePullbackData.theta a f').inv.app ((scalarSixPull Λ g).obj N) ≫
        (scalarSixChange a X').map ((nativeSquare Λ u f' f g w).app N)
      = (nativeSquare Λ' u f' f g w).app
          ((scalarSixChange a Y).obj N) ≫
        (scalarSixPull Λ' u).map ((scalarDirectImagePullbackData.theta a f).inv.app N) ≫
        (scalarDirectImagePullbackData.theta a u).inv.app ((scalarSixPull Λ f).obj N) := by
  exact pointwiseSquare (scalarSixChange a X')
    ((scalarSixPullComp Λ f' g).hom.app N)
    ((scalarSixPullComp Λ f' g).inv.app N)
    ((scalarSixPullComp Λ u f).hom.app N)
    ((eqToIso (congrArg (scalarSixPull Λ) w.symm)).hom.app N)
    ((scalarSixPullComp Λ' f' g).hom.app ((scalarSixChange a Y).obj N))
    ((scalarSixPullComp Λ' f' g).inv.app ((scalarSixChange a Y).obj N))
    ((scalarSixPullComp Λ' u f).hom.app ((scalarSixChange a Y).obj N))
    ((eqToIso (congrArg (scalarSixPull Λ') w.symm)).hom.app
      ((scalarSixChange a Y).obj N))
    ((scalarSixPull Λ' f').map ((scalarDirectImagePullbackData.theta a g).inv.app N))
    ((scalarDirectImagePullbackData.theta a f').inv.app ((scalarSixPull Λ g).obj N))
    ((scalarSixPull Λ' u).map ((scalarDirectImagePullbackData.theta a f).inv.app N))
    ((scalarDirectImagePullbackData.theta a u).inv.app ((scalarSixPull Λ f).obj N))
    ((scalarDirectImagePullbackData.theta a (f' ≫ g)).inv.app N)
    ((scalarDirectImagePullbackData.theta a (u ≫ f)).inv.app N)
    ((nativeSquare Λ u f' f g w).app N)
    ((nativeSquare Λ' u f' f g w).app
      ((scalarSixChange a Y).obj N))
    (nativeSquareHomNormalization Λ u f' f g w N)
    (nativeSquareHomNormalization Λ' u f' f g w ((scalarSixChange a Y).obj N))
    (scalarCompInverse a f' g N) (scalarCompInverse a u f N)
    (scalarCongrInverse a w.symm N)
    ((scalarSixPullComp Λ f' g).hom_inv_id_app N)
    ((scalarSixPullComp Λ' f' g).hom_inv_id_app ((scalarSixChange a Y).obj N))
    ((scalarSixPullComp Λ' f' g).inv_hom_id_app ((scalarSixChange a Y).obj N))

private theorem forwardNamedMateRectangle
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Type*}
    [cA₀ : Category* A₀] [cA₁ : Category* A₁] [cA₂ : Category* A₂]
    [cA₃ : Category* A₃] [cB₀ : Category* B₀] [cB₁ : Category* B₁]
    [cB₂ : Category* B₂] [cB₃ : Category* B₃]
    {T₀ : A₀ ⥤ B₀} {T₁ : A₁ ⥤ B₁} {T₂ : A₂ ⥤ B₂} {T₃ : A₃ ⥤ B₃}
    {f : A₀ ⥤ A₁} {rf : A₁ ⥤ A₀} {g : A₂ ⥤ A₃} {rg : A₃ ⥤ A₂}
    {fb : B₀ ⥤ B₁} {rfb : B₁ ⥤ B₀} {gb : B₂ ⥤ B₃} {rgb : B₃ ⥤ B₂}
    (af : f ⊣ rf) (ag : g ⊣ rg) (bf : fb ⊣ rfb) (bg : gb ⊣ rgb)
    {a : A₁ ⥤ A₃} {c : A₀ ⥤ A₂} {ab : B₁ ⥤ B₃} {cb : B₀ ⥤ B₂}
    (lf : T₀ ⋙ fb ⟶ f ⋙ T₁) (lg : T₂ ⋙ gb ⟶ g ⋙ T₃)
    (la : a ⋙ T₃ ≅ T₁ ⋙ ab) (lc : c ⋙ T₂ ≅ T₀ ⋙ cb)
    (sa : c ⋙ g ⟶ f ⋙ a) (sb : cb ⋙ gb ⟶ fb ⋙ ab)
    (coh : ∀ M, gb.map (lc.inv.app M) ≫ lg.app (c.obj M) ≫ T₃.map (sa.app M) =
      sb.app (T₀.obj M) ≫ ab.map (lf.app M) ≫ la.inv.app (f.obj M))
    (r : rf ⋙ T₀ ⟶ T₁ ⋙ rfb) (t : rg ⋙ T₂ ⟶ T₃ ⋙ rgb)
    (e : rf ⋙ c ⟶ a ⋙ rg) (eb : rfb ⋙ cb ⟶ ab ⋙ rgb)
    (hr : r = (mateEquiv af bf (TwoSquare.mk _ _ _ _ lf)).natTrans)
    (ht : t = (mateEquiv ag bg (TwoSquare.mk _ _ _ _ lg)).natTrans)
    (he : e = (mateEquiv af ag (TwoSquare.mk _ _ _ _ sa)).natTrans)
    (heb : eb = (mateEquiv bf bg (TwoSquare.mk _ _ _ _ sb)).natTrans)
    (p : c ⋙ T₂ ⟶ T₀ ⋙ cb) (q : a ⋙ T₃ ⟶ T₁ ⋙ ab)
    (hp : p = lc.hom) (hq : q = la.hom) (J : A₁)
    (EJ : T₂.obj (c.obj (rf.obj J)) ⟶ T₂.obj (rg.obj (a.obj J)))
    (EBJ : cb.obj (rfb.obj (T₁.obj J)) ⟶ rgb.obj (ab.obj (T₁.obj J)))
    (hEJ : EJ = T₂.map (e.app J)) (hEBJ : EBJ = eb.app (T₁.obj J)) :
    p.app (rf.obj J) ≫ cb.map (r.app J) ≫ EBJ =
      EJ ≫ t.app (a.obj J) ≫ rgb.map (q.app J) := by
  subst EJ EBJ p q
  have h := mate_rectangle_of_eq af ag bf bg lf lg la.inv lc.inv sa sb coh
    r t e eb hr ht he heb J
  dsimp only [mateRouteLeft, mateRouteRight] at h
  have h' := congrArg (fun z ↦ lc.hom.app (rf.obj J) ≫ z ≫
    rgb.map (la.hom.app J)) h
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Functor.comp_obj, Iso.hom_inv_id_app_assoc] at h'
  rw [rgb.map_id (ab.obj (T₁.obj J))] at h'
  simpa only [Category.comp_id] using h'

private theorem scalarComparisonRectangle
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (_hcd : BaseFieldFiniteCD ell k) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (_ha : ListedCoefficientMap ell a)
    {X' X Y' Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : ChosenCartesianSquare u.left f'.left f.left g.left)
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    (scalarSixPullHom a g.left).app
          ((RootCoordinateFace.lower Λ.X f.left).obj K.obj) ≫
        (scalarSixPull Λ' g.left).map
          ((scalarDirectImageMate a f.left).app K.obj) ≫
        (RootCoordinateFace.exchange Λ'.X u.left f'.left f.left g.left sq.w).app
          ((scalarSixChange a X.left).obj K.obj) =
      (scalarSixChange a Y'.left).map
          ((RootCoordinateFace.exchange Λ.X u.left f'.left f.left g.left sq.w).app
            K.obj) ≫
        (scalarDirectImageMate a f'.left).app
          ((scalarSixPull Λ u.left).obj K.obj) ≫
        (RootCoordinateFace.lower Λ'.X f'.left).map
          ((scalarSixPullHom a u.left).app K.obj) := by
  have h := forwardNamedMateRectangle
    (T₀ := scalarSixChange a Y.left) (T₁ := scalarSixChange a X.left)
    (T₂ := scalarSixChange a Y'.left) (T₃ := scalarSixChange a X'.left)
    (f := scalarSixPull Λ f.left) (rf := RootCoordinateFace.lower Λ.X f.left)
    (g := scalarSixPull Λ f'.left) (rg := RootCoordinateFace.lower Λ.X f'.left)
    (fb := scalarSixPull Λ' f.left) (rfb := RootCoordinateFace.lower Λ'.X f.left)
    (gb := scalarSixPull Λ' f'.left) (rgb := RootCoordinateFace.lower Λ'.X f'.left)
    (a := scalarSixPull Λ u.left) (c := scalarSixPull Λ g.left)
    (ab := scalarSixPull Λ' u.left) (cb := scalarSixPull Λ' g.left)
    (RootCoordinateFace.adjunction Λ.X f.left)
    (RootCoordinateFace.adjunction Λ.X f'.left)
    (RootCoordinateFace.adjunction Λ'.X f.left)
    (RootCoordinateFace.adjunction Λ'.X f'.left)
    (scalarDirectImagePullbackData.theta a f.left).inv
    (scalarDirectImagePullbackData.theta a f'.left).inv
    (scalarDirectImagePullbackData.theta a u.left)
    (scalarDirectImagePullbackData.theta a g.left)
    (nativeSquare Λ u.left f'.left f.left g.left sq.w)
    (nativeSquare Λ' u.left f'.left f.left g.left sq.w)
    (nativeScalarSquareInverse a u.left f'.left f.left g.left sq.w)
    (scalarDirectImageMate a f.left) (scalarDirectImageMate a f'.left)
    (nativeExchange Λ u.left f'.left f.left g.left sq.w)
    (nativeExchange Λ' u.left f'.left f.left g.left sq.w)
    (directImageMate_native a f.left) (directImageMate_native a f'.left)
    (exchange_native Λ u.left f'.left f.left g.left sq.w)
    (exchange_native Λ' u.left f'.left f.left g.left sq.w)
    (scalarSixPullHom a g.left) (scalarSixPullHom a u.left)
    (scalarDirectImagePullbackData.thetaNormalization a g.left).symm
    (scalarDirectImagePullbackData.thetaNormalization a u.left).symm K.obj
    ((scalarSixChange a Y'.left).map
      ((RootCoordinateFace.exchange Λ.X u.left f'.left f.left g.left sq.w).app K.obj))
    ((RootCoordinateFace.exchange Λ'.X u.left f'.left f.left g.left sq.w).app
      ((scalarSixChange a X.left).obj K.obj))
    (nativeExchange_map Λ u.left f'.left f.left g.left sq.w
      (scalarSixChange a Y'.left) K.obj).symm
    (nativeExchange_app Λ' u.left f'.left f.left g.left sq.w
      ((scalarSixChange a X.left).obj K.obj)).symm
  exact h


end Helpers

/-- Scalar-six preservation, invertibility, and exchange compatibility for a
listed coefficient map.

Source: blueprint `sk-lem-sbc-exchange-compatibility`, scalar clause; the
preservation and invertibility subclauses use `scalarSixDirectImage` and
`scalarSixCoefficientComparison`, while the final equality is the scalar
geometric mate rectangle.  The remaining work is to transport that rectangle
through the RootCoordinateFace presentation.
(blueprint: lem-sbc-exchange-scalar-comparison)
-/
theorem sbcExchangeScalarComparison
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hcd : BaseFieldFiniteCD ell k) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a)
    {X' X Y' Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : ChosenCartesianSquare u.left f'.left f.left g.left)
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    (constantModelBoundedConstructible Λ'.X Y'.left ⊓
        DerivedCategory.finiteTorAmplitude _)
      ((scalarSixChange a Y'.left).obj
        ((scalarSixPull Λ g.left).obj
          ((RootCoordinateFace.lower Λ.X f.left).obj K.obj))) ∧
    (constantModelBoundedConstructible Λ'.X Y'.left ⊓
        DerivedCategory.finiteTorAmplitude _)
      ((RootCoordinateFace.lower Λ'.X f'.left).obj
        ((scalarSixPull Λ' u.left).obj
          ((scalarSixChange a X.left).obj K.obj))) ∧
    IsIso ((scalarSixPullHom a g.left).app
      ((RootCoordinateFace.lower Λ.X f.left).obj K.obj)) ∧
    IsIso ((scalarDirectImageMate a f.left).app K.obj) ∧
    IsIso ((scalarDirectImageMate a f'.left).app
      ((scalarSixPull Λ u.left).obj K.obj)) ∧
    IsIso ((scalarSixPullHom a u.left).app K.obj) ∧
    (scalarSixPullHom a g.left).app
          ((RootCoordinateFace.lower Λ.X f.left).obj K.obj) ≫
        (scalarSixPull Λ' g.left).map
          ((scalarDirectImageMate a f.left).app K.obj) ≫
        (RootCoordinateFace.exchange Λ'.X u.left f'.left f.left g.left sq.w).app
          ((scalarSixChange a X.left).obj K.obj) =
      (scalarSixChange a Y'.left).map
          ((RootCoordinateFace.exchange Λ.X u.left f'.left f.left g.left sq.w).app
            K.obj) ≫
        (scalarDirectImageMate a f'.left).app
          ((scalarSixPull Λ u.left).obj K.obj) ≫
        (RootCoordinateFace.lower Λ'.X f'.left).map
          ((scalarSixPullHom a u.left).app K.obj) := by
  have h := scalarComparisonEndpoints ell k hcd a ha u f' f g sq K
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2,
    scalarComparisonRectangle ell k hcd a ha u f' f g sq K⟩

end AlgebraicGeometry.Scheme
