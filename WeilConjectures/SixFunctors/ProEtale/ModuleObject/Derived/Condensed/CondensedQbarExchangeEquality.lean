/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarComparisons
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarExchangeLeftAdjunct
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarExchangeRightAdjunct
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison

/-! # The exchange equality for condensed finite-to-Qbar coefficient change -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

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

private theorem pull_eqRoot (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarSixPull Λ f = RootCoordinateFace.upper Λ.X f := by
  rfl

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

private theorem exchange_native (Λ : ScalarSixRing.{u})
    {X' X Y' Y : Scheme.{u}} (u : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (w : u ≫ f = f' ≫ g) :
    nativeExchange Λ u f' f g w =
      (mateEquiv (L₁ := scalarSixPull Λ f) (L₂ := scalarSixPull Λ f')
        (G := scalarSixPull Λ g) (H := scalarSixPull Λ u)
        (RootCoordinateFace.adjunction Λ.X f)
        (RootCoordinateFace.adjunction Λ.X f')
        (TwoSquare.mk _ _ _ _ (nativeSquare Λ u f' f g w))).natTrans := by
  rfl

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

private theorem mateRectangle
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Type*}
    [Category* A₀] [Category* A₁] [Category* A₂] [Category* A₃]
    [Category* B₀] [Category* B₁] [Category* B₂] [Category* B₃]
    {f : A₀ ⥤ A₁} {rf : A₁ ⥤ A₀} {g : A₂ ⥤ A₃} {rg : A₃ ⥤ A₂}
    {fb : B₀ ⥤ B₁} {rfb : B₁ ⥤ B₀} {gb : B₂ ⥤ B₃} {rgb : B₃ ⥤ B₂}
    (af : f ⊣ rf) (ag : g ⊣ rg) (bf : fb ⊣ rfb) (bg : gb ⊣ rgb)
    {a : A₁ ⥤ A₃} {c : A₀ ⥤ A₂} {ab : B₁ ⥤ B₃} {cb : B₀ ⥤ B₂}
    {T₀ : A₀ ⥤ B₀} {T₁ : A₁ ⥤ B₁} {T₂ : A₂ ⥤ B₂} {T₃ : A₃ ⥤ B₃}
    (lf : T₀ ⋙ fb ⟶ f ⋙ T₁) (lg : T₂ ⋙ gb ⟶ g ⋙ T₃)
    (la : T₁ ⋙ ab ⟶ a ⋙ T₃) (lc : T₀ ⋙ cb ⟶ c ⋙ T₂)
    (sa : c ⋙ g ⟶ f ⋙ a) (sb : cb ⋙ gb ⟶ fb ⋙ ab)
    (coh : ∀ M, gb.map (lc.app M) ≫ lg.app (c.obj M) ≫ T₃.map (sa.app M) =
      sb.app (T₀.obj M) ≫ ab.map (lf.app M) ≫ la.app (f.obj M))
    (J : A₁) :
    cb.map ((mateEquiv af bf (TwoSquare.mk _ _ _ _ lf)).natTrans.app J) ≫
        (mateEquiv bf bg (TwoSquare.mk _ _ _ _ sb)).natTrans.app (T₁.obj J) ≫
        rgb.map (la.app J) =
      lc.app (rf.obj J) ≫
        T₂.map ((mateEquiv af ag (TwoSquare.mk _ _ _ _ sa)).natTrans.app J) ≫
        (mateEquiv ag bg (TwoSquare.mk _ _ _ _ lg)).natTrans.app (a.obj J) := by
  let r := (mateEquiv af bf (TwoSquare.mk _ _ _ _ lf)).natTrans
  let t := (mateEquiv ag bg (TwoSquare.mk _ _ _ _ lg)).natTrans
  let e := (mateEquiv af ag (TwoSquare.mk _ _ _ _ sa)).natTrans
  let eb := (mateEquiv bf bg (TwoSquare.mk _ _ _ _ sb)).natTrans
  have hr := mateEquiv_counit af bf (TwoSquare.mk _ _ _ _ lf) J
  have ht := mateEquiv_counit ag bg (TwoSquare.mk _ _ _ _ lg) (a.obj J)
  have he := mateEquiv_counit af ag (TwoSquare.mk _ _ _ _ sa) J
  have heb := mateEquiv_counit bf bg (TwoSquare.mk _ _ _ _ sb) (T₁.obj J)
  change fb.map (r.app J) ≫ bf.counit.app _ = _ at hr
  change gb.map (t.app (a.obj J)) ≫ bg.counit.app _ = _ at ht
  change g.map (e.app J) ≫ ag.counit.app _ = _ at he
  change gb.map (eb.app (T₁.obj J)) ≫ bg.counit.app _ = _ at heb
  dsimp only [TwoSquare.mk, TwoSquare.natTrans] at hr ht he heb
  apply (bg.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, CategoryTheory.Functor.map_comp, Category.assoc]
  change gb.map (cb.map (r.app J)) ≫ gb.map (eb.app (T₁.obj J)) ≫
      gb.map (rgb.map (la.app J)) ≫ bg.counit.app _ =
    gb.map (lc.app (rf.obj J)) ≫ gb.map (T₂.map (e.app J)) ≫
      gb.map (t.app (a.obj J)) ≫ bg.counit.app _
  have hn := bg.counit.naturality (la.app J)
  change gb.map (rgb.map (la.app J)) ≫ bg.counit.app _ =
    bg.counit.app _ ≫ la.app J at hn
  rw [hn, reassoc_of% heb, ht]
  have ns := sb.naturality (r.app J)
  change gb.map (cb.map (r.app J)) ≫ sb.app _ =
    sb.app _ ≫ ab.map (fb.map (r.app J)) at ns
  rw [reassoc_of% ns, ← ab.map_comp_assoc, hr, ab.map_comp]
  have nl := la.naturality (af.counit.app J)
  change ab.map (T₁.map (af.counit.app J)) ≫ la.app J =
    la.app _ ≫ T₃.map (a.map (af.counit.app J)) at nl
  simp only [Category.assoc]
  rw [nl]
  have ng := lg.naturality (e.app J)
  change gb.map (T₂.map (e.app J)) ≫ lg.app _ =
    lg.app _ ≫ T₃.map (g.map (e.app J)) at ng
  rw [reassoc_of% ng, ← T₃.map_comp, he, T₃.map_comp]
  rw [reassoc_of% coh]
  rfl

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
  have h := mateRectangle af ag bf bg lf lg la.inv lc.inv sa sb coh J
  rw [← hr, ← ht, ← he, ← heb] at h
  have h' := congrArg (fun z ↦ lc.hom.app (rf.obj J) ≫ z ≫
    rgb.map (la.hom.app J)) h
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Functor.comp_obj, Iso.hom_inv_id_app_assoc] at h'
  rw [rgb.map_id (ab.obj (T₁.obj J))] at h'
  simpa only [Category.comp_id] using h'

/-- Coefficient extension respects the specified unit-square-counit exchange arrow.
Source: `ModuleObject/Colimit/TwoColimit.lean`, final transport paragraph;
`ModuleObject/ChangeOfCoefficients.lean`, Derived section; mate pasting in
`Mathlib/CategoryTheory/Adjunction/Mates.lean`
(blueprint: lem-weil-pbc-qbar-condensed-exchange-equality).

Proof in words. Write T for scalar extension, l_h for derived pullback, r_h for derived
pushforward, α_h: T l_h,E ≅ l_h,Ω T for the pull comparison, and δ_h: T r_h,E → r_h,Ω T
for the push comparison. By their definitions from the same restriction/direct-image
isomorphism, δ_h is the mate of α_h inverse along the two pull/push adjunctions. This follows
by expanding pullIsoOfComapIso and pushHomOfComapIso: conjugation is the mate correspondence
for the composite adjunctions, and the two successive transpositions cancel. In particular,
the adjunct of δ_h at K is α_h inverse at r_h,E(K), followed by T of the E-counit.

The α comparisons respect composition of scheme morphisms. At the underived module level,
both composites are induced by the identical associativity map on inverse images and the
balanced tensor map b ⊗ (a ⊗ m) ↦ ba ⊗ m. The coefficient square commutes by naturality of
the coefficient map. This gives equality of natural transformations by the tensor and
sheafification universal properties. Exact pullback and flat scalar extension compute their
derived functors termwise; restriction preserves K-injectives since its left adjoint is
exact. Thus the same coherence descends through localization and agrees with the derived
comparisons defined by conjugation. The composition comparisons are the derived ones used
in boundedConstructiblePullbackSquareComparison, rather than newly chosen comparisons.

Let θ_A: l_f',A l_g,A ≅ l_g',A l_f,A be the square comparison. Coherence gives the following
commuting diagram, suppressing object arguments and the canonical associators:
T(θ_E), then α_g', then l_g',Ω(α_f) equals α_f', then l_f',Ω(α_g), then θ_Ω(T).
Both routes start at T l_f',E l_g,E and end at l_g',Ω l_f,Ω T. The equality also respects
the commutativity proof in the square: substitution by equal morphisms is natural, and
proof irrelevance identifies proofs of that equality.

Take mates of this equality along l_f,E ⊣ r_f,E and l_f',E ⊣ r_f',E, and along the analogous
Ω-adjunctions. Mate pasting preserves equality and composition (mateEquiv_hcomp and
mateEquiv_vcomp, equivalently mateEquiv_square). The mate of θ_A is exactly the specified
exchange B_A: expanding the mate is unit insertion, square transport, then counit contraction.
The edge mates are δ_f and δ_f', by the first paragraph. Thus the resulting equality is
B_Ω(T(K)) ∘ l_g,Ω(δ_f(K)) ∘ α_g(r_f,E(K)) =
r_f',Ω(α_g'(K)) ∘ δ_f'(l_g',E(K)) ∘ T(B_E(K)), exactly the asserted formula.
The bounded constructible adjunction and square comparison are restrictions along fully
faithful inclusions, which preserve the displayed units, counits, and composition constraints.
Neither δ nor B is
inverted; properness and Cartesianity are unnecessary. -/
theorem constructibleToQbar_exchange_equality
    (sq : CommSq g' f' f g) (K : PadicSubfieldConstructible X ℓ E) :
    constructibleToQbarSourceHom ℓ k E f g K ≫
        (boundedConstructibleBaseChange ℓ (sq.asOver (Spec (.of k)))).app
          ((constructibleToPadicAlgCl X ℓ E).obj K) =
      (constructibleToPadicAlgCl Y' ℓ E).map
          ((ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E
            (sq.asOver (Spec (.of k)))).app K) ≫
        constructibleToQbarTargetHom ℓ k E f' g' K := by
  apply ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
    (f'.asOver (Spec (.of k)))).homEquiv _ _).symm.injective
  exact (constructibleToQbar_exchange_left_adjunct ℓ k E f g f' g' sq K).trans
    (constructibleToQbar_exchange_right_adjunct ℓ k E f g f' g' sq K).symm

end AlgebraicGeometry.ProEtale.CondensedRing
