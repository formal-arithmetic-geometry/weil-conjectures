/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekData
import all WeilConjectures.AlgebraicGeometry.VaryingRingOperations
import WeilConjectures.AlgebraicGeometry.VaryingRingProperOpenArrows
import WeilConjectures.AlgebraicGeometry.VaryingRingTensorSupport
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerOrdinaryUnitEvaluation
import WeilConjectures.AlgebraicGeometry.SemilinearSystemIsoAssembly
import WeilConjectures.CategoryTheory.ExactDerivedAdjunctionSupplement

/-! # Open extension and the invertible normalized tensor transpose

Source: Zheng Construction 4.1; Stacks 03DI, 0E8I and 0GL1;
the system case of openTensorNormalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u v c r
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek
attribute [local implicit_reducible] CategoryTheory.TwoSquare
  CategoryTheory.Functor.mapHomologicalComplex
  AlgebraicGeometry.ProEtale.VaryingRing.push
  AlgebraicGeometry.ProEtale.spCoefficientCommRings
  AlgebraicGeometry.ProEtale.SpTowerShriek.tau
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  WeilConjectures.SemilinearSections.evaluation
  SheafOfModules.pushforward PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj AlgebraicGeometry.Scheme.proEtaleRingModuleDirectImage
  AlgebraicGeometry.ProEtale.StrictTower.modulePullback
  AlgebraicGeometry.ProEtale.StrictTower.moduleDirectImage
  AlgebraicGeometry.ProEtale.StrictTower.constantRingIso
  AlgebraicGeometry.Scheme.proEtaleConstantRingComparison
attribute [local irreducible] CategoryTheory.constantSheaf Padic
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf WeilConjectures.SemilinearSections.rings
  Padic.coefficientExtensionIntegers
  WeilConjectures.SemilinearSections.transition
  WeilConjectures.SemilinearSections.coefficientMap
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction
  AlgebraicGeometry.Scheme.proEtaleRingDirectImageMap

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private abbrev chart {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.ProEtᵒᵖ) :=
  (Scheme.proEtaleBaseChange f).op.obj U

private def restrictedSection {C : Type*} [Category C] [EssentiallySmall.{v} C]
    {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{v}} (φ : R ⟶ S)
    (M : SemilinearSections.Mod.{_, _, v} J S) (U : Cᵒᵖ) :
    ((SemilinearSections.res.{_, _, v} φ).obj M).val.obj U → M.val.obj U :=
  fun x ↦ x

private theorem restrictedSection_heq {C : Type*} [Category C] [EssentiallySmall.{v} C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{v}} (φ : R ⟶ S)
    (M : SemilinearSections.Mod.{_, _, v} J S) (U : Cᵒᵖ)
    (x : ((SemilinearSections.res.{_, _, v} φ).obj M).val.obj U) :
    HEq (restrictedSection φ M U x) x := by rfl

private theorem restrict_map_heq {C : Type*} [Category C] [EssentiallySmall.{v} C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{v}} (φ : R ⟶ S)
    {M N : SemilinearSections.Mod.{_, _, v} J S} (a : M ⟶ N) (U : Cᵒᵖ)
    (x : ((SemilinearSections.res.{_, _, v} φ).obj M).val.obj U)
    (y : M.val.obj U) (h : HEq x y) :
    HEq (((SemilinearSections.res.{_, _, v} φ).map a).val.app U x)
      (a.val.app U y) := by
  have hx : x = y := eq_of_heq h
  cases hx
  rfl

private def pushSection (A : Type u) [CommRing A] {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A))
    (U : S.ProEtᵒᵖ) :
    ((Scheme.proEtaleConstantRingPushforward A f).obj M).val.obj U →
      M.val.obj (chart f U) := fun x ↦ x

private theorem pushSection_heq (A : Type u) [CommRing A] {X S : Scheme.{u}}
    (f : X ⟶ S) (M : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A))
    (U : S.ProEtᵒᵖ) (x : ((Scheme.proEtaleConstantRingPushforward A f).obj M).val.obj U) :
    HEq (pushSection A f M U x) x := by rfl

private theorem pushSection_map (A : Type u) [CommRing A] {X S : Scheme.{u}}
    (f : X ⟶ S) {M N : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)}
    (a : M ⟶ N) (U : S.ProEtᵒᵖ)
    (x : ((Scheme.proEtaleConstantRingPushforward A f).obj M).val.obj U) :
    pushSection A f N U (((Scheme.proEtaleConstantRingPushforward A f).map a).val.app U x) =
      a.val.app (chart f U) (pushSection A f M U x) := by rfl
private theorem pushSection_comp (A : Type u) [CommRing A] {X S : Scheme.{u}}
    (f : X ⟶ S) {M N : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)}
    {P : Scheme.proEtaleRingModules S (Scheme.proEtaleConstantRing S A)}
    (a : P ⟶ (Scheme.proEtaleConstantRingPushforward A f).obj M) (b : M ⟶ N)
    (U : S.ProEtᵒᵖ) (x : P.val.obj U) :
    pushSection A f N U ((a ≫ (Scheme.proEtaleConstantRingPushforward A f).map b).val.app U x) =
      b.val.app (chart f U) (pushSection A f M U (a.val.app U x)) := by rfl

private theorem counit_evaluation
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    {L : A ⥤ B} {R : B ⥤ A} (b : L ⊣ R) (V : C ⥤ A) (W : D ⥤ B)
    (eF : F ⋙ W ≅ V ⋙ L) (eG : G ⋙ V ≅ W ⋙ R)
    (hu : ∀ M, V.map (a.unit.app M) ≫ eG.hom.app (F.obj M) ≫
      R.map (eF.hom.app M) = b.unit.app (V.obj M)) (N : D) :
    b.homEquiv _ _ (eF.inv.app (G.obj N) ≫ W.map (a.counit.app N)) =
      eG.hom.app N := by
  have hu' : V.map (a.unit.app (G.obj N)) ≫ eG.hom.app (F.obj (G.obj N)) =
      b.unit.app (V.obj (G.obj N)) ≫ R.map (eF.inv.app (G.obj N)) := by
    apply (Iso.eq_comp_inv (R.mapIso (eF.app (G.obj N)))).2
    simpa only [CategoryTheory.Functor.mapIso_hom, Iso.app_hom, Category.assoc]
      using hu (G.obj N)
  have hh : V.map (a.homEquiv _ _ (a.counit.app N)) ≫ eG.hom.app N =
      b.homEquiv _ _ (eF.inv.app (G.obj N) ≫ W.map (a.counit.app N)) := by
    rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp, Category.assoc]
    have hn : V.map (G.map (a.counit.app N)) ≫ eG.hom.app N =
        eG.hom.app (F.obj (G.obj N)) ≫ R.map (W.map (a.counit.app N)) :=
      eG.hom.naturality (a.counit.app N)
    rw [hn, ← Category.assoc, hu']
    simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp,
      Category.assoc]
  have he : a.homEquiv _ _ (a.counit.app N) = 𝟙 (G.obj N) := by
    rw [← a.homEquiv_symm_id N]
    exact (a.homEquiv _ _).apply_symm_apply _
  rw [he, CategoryTheory.Functor.map_id, Category.id_comp] at hh
  exact hh.symm

private abbrev horizontal (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    SpTowerShriek.ev l E T m ⟶ SpTowerShriek.ev l E T n ⋙
      SemilinearSections.res.{u + 1, u, u + 1}
        (SemilinearSections.coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h) :=
  SemilinearSections.transition.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
    (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h
private abbrev restrict (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (SpTowerShriek.B l E T n) ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (SpTowerShriek.B l E T m) :=
  SemilinearSections.res.{u + 1, u, u + 1}
    (SemilinearSections.coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h)

private def horizontalSection (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (M : SpTowerShriek.S l E T) (U : T.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l E T m).obj M).val.obj U) :
    ((SpTowerShriek.ev l E T n).obj M).val.obj U :=
  restrictedSection
    (SemilinearSections.coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h)
    ((SpTowerShriek.ev l E T n).obj M) U (((horizontal l E T h).app M).val.app U x)

private theorem push_horizontal {X S : Scheme.{u}} (f : X ⟶ S)
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f)
    (N : SpTowerShriek.S l E X) {m n : ℕ} (h : n ≤ m) (U : S.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l E S m).obj (g.push.obj N)).val.obj U) :
    pushSection (SpTowerShriek.R l E n) f ((SpTowerShriek.ev l E X n).obj N) U
      (((g.ordinaryPushEvaluation n).hom.app N).val.app U
        (horizontalSection l E S h (g.push.obj N) U x)) =
      horizontalSection l E X h N (chart f U)
        (pushSection (SpTowerShriek.R l E m) f ((SpTowerShriek.ev l E X m).obj N) U
          (((g.ordinaryPushEvaluation m).hom.app N).val.app U x)) := by
  let D := g.push.obj N
  let ε : g.pull.obj D ⟶ N := g.ordinaryAdjunction.counit.app N
  let a := fun k ↦ Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E k) f
  let d := fun k ↦ (g.ordinaryPullEvaluation k).inv.app D ≫
    (SpTowerShriek.ev l E X k).map ε
  have hd (k : ℕ) : (a k).homEquiv _ _ (d k) =
      (g.ordinaryPushEvaluation k).hom.app N := by
    exact counit_evaluation g.ordinaryAdjunction (a k)
      (SpTowerShriek.ev l E S k) (SpTowerShriek.ev l E X k)
      (g.ordinaryPullEvaluation k) (g.ordinaryPushEvaluation k)
      (SpTowerShriek.geometry_unit_evaluation l E b g k) N
  let t := (g.ordinaryPullEvaluation m).inv.app D ≫
    (horizontal l E X h).app (g.pull.obj D) ≫
      (restrict l E X h).map ((g.ordinaryPullEvaluation n).hom.app D)
  have ht : t ≫ (restrict l E X h).map (d n) =
      d m ≫ (horizontal l E X h).app N := by
    calc
      _ = (g.ordinaryPullEvaluation m).inv.app D ≫
          (horizontal l E X h).app (g.pull.obj D) ≫
            (restrict l E X h).map
              ((g.ordinaryPullEvaluation n).hom.app D ≫ d n) := by
        simp only [t, Category.assoc, CategoryTheory.Functor.map_comp]
      _ = (g.ordinaryPullEvaluation m).inv.app D ≫
          (horizontal l E X h).app (g.pull.obj D) ≫
            (restrict l E X h).map ((SpTowerShriek.ev l E X n).map ε) := by
        rw [show (g.ordinaryPullEvaluation n).hom.app D ≫ d n =
          (SpTowerShriek.ev l E X n).map ε from
            (g.ordinaryPullEvaluation n).hom_inv_id_app_assoc D _]
      _ = _ := congrArg ((g.ordinaryPullEvaluation m).inv.app D ≫ ·)
        ((horizontal l E X h).naturality ε).symm
  let y := horizontalSection l E S h D U x
  have hy : HEq (((horizontal l E S h).app D).val.app U x) y :=
    (restrictedSection_heq _ _ _ _).symm
  have hu := g.ordinaryUnitTransition
  unfold SpTowerShriek.OrdinaryUnitTransition SpTowerShriek.OrdinaryUnitTransitionModel at hu
  have hh := hu D h U x y hy
  have hh' : HEq
      (pushSection (SpTowerShriek.R l E m) f ((restrict l E X h).obj
        ((SpTowerShriek.ev l E X n).obj N)) U
          (((a m).homEquiv _ _ (t ≫ (restrict l E X h).map (d n))).val.app U x))
      (pushSection (SpTowerShriek.R l E n) f ((SpTowerShriek.ev l E X n).obj N) U
        (((a n).homEquiv _ _ (d n)).val.app U y)) := by
    rw [Adjunction.homEquiv_naturality_right, pushSection_comp]
    have hh₀ := (pushSection_heq _ _ _ _ _).trans
      (hh.trans (pushSection_heq _ _ _ _ _).symm)
    have hh₁ := restrict_map_heq
      (SemilinearSections.coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h)
      (d n) (chart f U) _ _ hh₀
    change HEq _ (pushSection (SpTowerShriek.R l E n) f _ U
      (((a n).unit.app _ ≫
        (Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).map
          (d n)).val.app U y))
    rw [show ((a n).unit.app _ ≫
        (Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).map
          (d n)).val.app U y =
        ((Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).map
          (d n)).val.app U (((a n).unit.app _).val.app U y) by rfl,
      pushSection_map]
    exact hh₁
  rw [ht, Adjunction.homEquiv_naturality_right, hd m, hd n, pushSection_comp] at hh'
  exact eq_of_heq (((restrictedSection_heq _ _ _ _).trans hh').symm)

private abbrev VR (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1} (R l E n))
private def VM (n : ℕ) : VR l E (n + 1) ⟶ VR l E n :=
  CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((Ideal.Quotient.factorPowSucc (spEllIdeal l E) (n + 1)).comp
      ULift.ringEquiv.toRingHom))
private theorem inverseMate_otherLeft
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {P : D ⥤ C} {F' Q' : C' ⥤ D'} {P' : D' ⥤ C'}
    (a : F ⊣ P) (b : F' ⊣ P') (q : Q' ⊣ P')
    {V : C ⥤ C'} {W : D ⥤ D'} (d : P ⋙ V ⟶ W ⋙ P') :
    ((mateEquiv a b).symm d).natTrans =
      Functor.whiskerLeft V (b.leftAdjointUniq q).hom ≫
        ((mateEquiv a q).symm d).natTrans := by
  ext M
  apply (b.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, CategoryTheory.Functor.map_comp]
  rw [← Category.assoc, b.unit_leftAdjointUniq_hom_app q]
  exact (unit_mateEquiv_symm a b d M).symm.trans (unit_mateEquiv_symm a q d M)

private theorem inverseMate_rightIso
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {P Q : D ⥤ C} {F' : C' ⥤ D'} {P' : D' ⥤ C'}
    (a : F ⊣ P) (b : F' ⊣ P') (e : P ≅ Q)
    {V : C ⥤ C'} {W : D ⥤ D'} (d : Q ⋙ V ⟶ W ⋙ P') :
    ((mateEquiv (a.ofNatIsoRight e) b).symm d).natTrans =
      ((mateEquiv a b).symm (Functor.whiskerRight e.hom V ≫ d)).natTrans := by
  ext M
  apply (b.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have h₁ := unit_mateEquiv_symm (a.ofNatIsoRight e) b (TwoSquare.mk _ _ _ _ d) M
  have h₂ := unit_mateEquiv_symm a b
    (TwoSquare.mk _ _ _ _ (Functor.whiskerRight e.hom V ≫ d)) M
  simp only [Functor.id_obj] at h₁ h₂
  calc
    _ = V.map ((a.ofNatIsoRight e).unit.app M) ≫ d.app (F.obj M) := h₁.symm
    _ = V.map (a.unit.app M) ≫
        (Functor.whiskerRight e.hom V ≫ d).app (F.obj M) := by
      simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
        CategoryTheory.Functor.map_comp, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Category.assoc]
    _ = _ := h₂

private theorem deriveMap_fac {T T' : Scheme.{u}} {F G : S l E T ⥤ S l E T'}
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⟶ G) (K : CochainComplex (S l E T) ℤ) :
    (deriveMap l E a).app (DerivedCategory.Q.obj K) ≫ G.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex a (.up ℤ)).app K) := by
  simp only [deriveMap, Localization.liftNatTrans_app, Localization.Lifting.iso,
    Functor.whiskerRight_app, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

section ExactUnit

-- Work over abstract abelian categories so the localization formula retains its instances.
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard

private theorem exactUnit_fac
    {A C : Type*} [Category A] [Category C] [Abelian A] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory C]
    {F : A ⥤ C} {G : C ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) (K : CochainComplex A ℤ) :
    a.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) := by
  simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_unit_app]
  change (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
    G.mapDerivedCategoryFactors.inv.app _ ≫
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K)) ≫
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
    G.mapDerivedCategoryFactors.hom.app _ = _
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp

end ExactUnit

private theorem exact_unit_termwise {T T' : Scheme.{u}}
    {F : S l E T ⥤ S l E T'} {G : S l E T' ⥤ S l E T}
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    a.mapExactDerivedCategory.unit =
      (Functor.mapDerivedCategoryIdIso _).inv ≫ deriveMap l E a.unit ≫
        (Functor.mapDerivedCategoryCompIso F G).hom := by
  symm
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (S l E T) (.up ℤ))
  intro K
  apply (cancel_mono (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
    G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K))).mp
  simp only [NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors, deriveMap_fac,
    ← Functor.mapDerivedCategoryIdIso_hom_app_Q_obj, Iso.inv_hom_id_app_assoc]
  calc
    _ = DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) := by
      apply congrArg (fun f ↦ DerivedCategory.Q.map f)
      ext i
      rfl
    _ = _ := (exactUnit_fac a K).symm

private theorem exact_counit_termwise {T T' : Scheme.{u}}
    {F : S l E T ⥤ S l E T'} {G : S l E T' ⥤ S l E T}
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    a.mapExactDerivedCategory.counit =
      (Functor.mapDerivedCategoryCompIso G F).inv ≫ deriveMap l E a.counit ≫
        (Functor.mapDerivedCategoryIdIso _).hom := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (S l E T') (.up ℤ))
  intro K
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso G F).hom.app
    (DerivedCategory.Q.obj K))).mp
  simp only [NatTrans.comp_app, Iso.hom_inv_id_app_assoc]
  rw [Functor.mapDerivedCategoryIdIso_hom_app_Q_obj, deriveMap_fac]
  simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_counit_app,
    Iso.symm_inv]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  apply congrArg ((G ⋙ F).mapDerivedCategoryFactors.hom.app K ≫ ·)
  apply congrArg (fun f ↦ DerivedCategory.Q.map f)
  ext i
  rfl


private abbrev SS (X : Scheme.{u}) (σ : ∀ n, B l E X (n + 1) ⟶ B l E X n) :=
  SemilinearSections.Systems.{u + 1, u, u + 1} (ProEt.topology X) (B l E X) σ
private abbrev EE (X : Scheme.{u}) (σ : ∀ n, B l E X (n + 1) ⟶ B l E X n) :=
  SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology X) (B l E X) σ
private abbrev DD (X : Scheme.{u}) (σ : ∀ n, B l E X (n + 1) ⟶ B l E X n) :=
  SemilinearSections.DS.{u + 1, u, u + 1} (ProEt.topology X) (B l E X) σ
private def transitionValue {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (B' : ℕ → Sheaf J CommRingCat.{r})
    (σ : ∀ n, B' (n + 1) ⟶ B' n) {m n : ℕ} (h : n ≤ m)
    (M : SemilinearSections.Systems.{c, v, r} J B' σ) (V : Cᵒᵖ)
    (x : ((SemilinearSections.evaluation.{c, v, r} J B' σ m).obj M).val.obj V) :
    ((SemilinearSections.evaluation.{c, v, r} J B' σ n).obj M).val.obj V :=
  ((SemilinearSections.transition.{c, v, r} J B' σ h).app M).val.app V x

private theorem transitionValue_eq {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (B' : ℕ → Sheaf J CommRingCat.{r})
    (σ : ∀ n, B' (n + 1) ⟶ B' n) {m n : ℕ} (h : n ≤ m)
    (M : SemilinearSections.Systems.{c, v, r} J B' σ) (V : Cᵒᵖ)
    (x : ((SemilinearSections.evaluation.{c, v, r} J B' σ m).obj M).val.obj V) :
    transitionValue J B' σ h M V x =
      M.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x := by
  unfold transitionValue SemilinearSections.transition
  exact congrFun (eq_of_heq
    ((SemilinearSections.transition_exists.{c, v, r} J B' σ h).exists.choose_spec M V)) x

private abbrev HS (X : Scheme.{u}) (σ : ∀ n, B l E X (n + 1) ⟶ B l E X n)
    {m n : ℕ} (h : n ≤ m) :=
  transitionValue (ProEt.topology X) (B l E X) σ h

set_option maxHeartbeats 1600000 in
-- Each section comparison normalizes the two continuous module-sheaf carrier presentations.
private theorem canonicalPushHorizontal
    (R' : ℕ → CommRingCat.{u + 1}) (φ : ∀ n, R' (n + 1) ⟶ R' n)
    {U T : Scheme.{u}} (j : U ⟶ T) (M : VaryingRing.Modules R' φ U)
    {m n : ℕ} (h : n ≤ m) (V : T.ProEtᵒᵖ)
    (x : ((VaryingRing.eval R' φ T m).obj ((VaryingRing.push R' φ j).obj M)).val.obj V) :
    ((VaryingRing.moduleEvalP R' φ j n).hom.app M).val.app V
        (transitionValue (ProEt.topology T) (VaryingRing.coefficients R' T)
          (VaryingRing.coefficientTransition R' φ T) h ((VaryingRing.push R' φ j).obj M) V x) =
      transitionValue (ProEt.topology U) (VaryingRing.coefficients R' U)
        (VaryingRing.coefficientTransition R' φ U) h M (chart j V)
          (((VaryingRing.moduleEvalP R' φ j m).hom.app M).val.app V x) := by
  dsimp only [VaryingRing.moduleEvalP]
  have hn := (VaryingRing.moduleEvalP_existsUnique R' φ j n).choose_spec.1 M V.unop
    (transitionValue (ProEt.topology T) (VaryingRing.coefficients R' T)
      (VaryingRing.coefficientTransition R' φ T) h ((VaryingRing.push R' φ j).obj M) V x)
  have hm := (VaryingRing.moduleEvalP_existsUnique R' φ j m).choose_spec.1 M V.unop x
  rw [hn, hm, transitionValue_eq, transitionValue_eq]
  change M.val.map
    (((VaryingRing.baseChange j).map (Prod.mkHom (homOfLE h) (𝟙 V.unop))).op) x =
    M.val.map
      (Prod.mkHom (homOfLE h) (𝟙 ((Scheme.proEtaleBaseChange j).obj V.unop))).op x
  apply M.val.congr_map_apply
  congr 1
  simp only [VaryingRing.baseChange, Functor.prod_map, Functor.id_map,
    CategoryTheory.Functor.map_id]

-- A private model records the canonical operations without imposing a definitional
-- choice of the adjacent coefficient maps. This permits equality transport once.
private structure OpenSiteModel (b : Base l E) {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j]
    (σU : ∀ n, B l E U (n + 1) ⟶ B l E U n)
    (σT : ∀ n, B l E T (n + 1) ⟶ B l E T n) where
  push : SS l E U σU ⥤ SS l E T σT
  pull : SS l E T σT ⥤ SS l E U σU
  extension : SS l E U σU ⥤ SS l E T σT
  [pullAdditive : pull.Additive]
  [pullLimits : PreservesFiniteLimits pull]
  [pullColimits : PreservesFiniteColimits pull]
  [extensionAdditive : extension.Additive]
  [extensionLimits : PreservesFiniteLimits extension]
  [extensionColimits : PreservesFiniteColimits extension]
  adj : pull ⊣ push
  openAdj : extension ⊣ pull
  evalP : ∀ n, push ⋙ EE l E T σT n ≅
    EE l E U σU n ⋙ proEtaleConstantRingPushforward (R l E n) j
  pushHorizontal : ∀ (M : SS l E U σU) {m n : ℕ} (h : n ≤ m) (V : T.ProEtᵒᵖ)
    (x : ((EE l E T σT m).obj (push.obj M)).val.obj V),
    ((evalP n).hom.app M).val.app V (HS l E T σT h (push.obj M) V x) =
      HS l E U σU h M (chart j V) (((evalP m).hom.app M).val.app V x)
  evalG : ∀ n, pull ⋙ EE l E U σU n ≅
    EE l E T σT n ⋙ proEtaleConstantRingPullback (R l E n) j
  unitG : ∀ n (M : SS l E T σT),
    (EE l E T σT n).map (adj.unit.app M) ≫
      (evalP n).hom.app (pull.obj M) ≫
      (proEtaleConstantRingPushforward (R l E n) j).map ((evalG n).hom.app M) =
        (proEtaleConstantRingAdjunction (R l E n) j).unit.app ((EE l E T σT n).obj M)
  openMate : ∀ n, IsIso
    ((mateEquiv openAdj (finiteOpenAdjunction l E b j n)).symm (evalG n).hom).natTrans
  openUnit : IsIso openAdj.unit
  support : ∀ (A : SemilinearSections.Closed.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology T))
      (SemilinearSections.systemRing (ProEt.topology T) (B l E T) σT))
    (_ : SemilinearSections.Models.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology T))
      (SemilinearSections.systemRing (ProEt.topology T) (B l E T) σT) A)
    (M : DD l E U σU) (N : DD l E T σT),
    extension.mapDerivedCategory.essImage
      (A.tensor.obj (extension.mapDerivedCategory.obj M, N))

attribute [local instance] OpenSiteModel.pullAdditive OpenSiteModel.pullLimits
  OpenSiteModel.pullColimits OpenSiteModel.extensionAdditive OpenSiteModel.extensionLimits
  OpenSiteModel.extensionColimits

private theorem tau_eq (X : Scheme.{u}) : tau l E X =
    VaryingRing.coefficientTransition (VR l E) (VM l E) X := by
  funext n
  simp only [tau, spCoefficientCommRings, Functor.ofOpSequence_map_homOfLE_succ]
  rfl

private theorem openSiteModel_exists (b : Base l E)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (σU : ∀ n, B l E U (n + 1) ⟶ B l E U n)
    (σT : ∀ n, B l E T (n + 1) ⟶ B l E T n)
    (hU : σU = VaryingRing.coefficientTransition (VR l E) (VM l E) U)
    (hT : σT = VaryingRing.coefficientTransition (VR l E) (VM l E) T) :
    Nonempty (OpenSiteModel l E b j σU σT) := by
  subst σU
  subst σT
  refine ⟨{
    push := VaryingRing.push (VR l E) (VM l E) j
    pull := VaryingRing.pull (VR l E) (VM l E) j
    extension := VaryingRing.extension (VR l E) (VM l E) j
    adj := VaryingRing.moduleAdj (VR l E) (VM l E) j
    openAdj := VaryingRing.moduleJAdj (VR l E) (VM l E) j
    evalP := VaryingRing.moduleEvalP (VR l E) (VM l E) j
    pushHorizontal := canonicalPushHorizontal (VR l E) (VM l E) j
    evalG := VaryingRing.moduleEvalG (VR l E) (VM l E) j
    unitG := fun n ↦
      (VaryingRing.moduleEvalG_existsUnique (VR l E) (VM l E) j n).choose_spec.1
    openMate := ?_
    openUnit := VaryingRing.moduleJAdj_unit_isIso (VR l E) (VM l E) j
    support := VaryingRing.tensor_openSupported (VR l E) (VM l E) j }⟩
  · intro n
    have := VaryingRing.ordinaryOpenMateIso (VR l E) (VM l E) j n
    rw [inverseMate_otherLeft (VaryingRing.moduleJAdj (VR l E) (VM l E) j)
      (finiteOpenAdjunction l E b j n) (StrictTower.moduleJAdj (VR l E n) j)
      (VaryingRing.moduleEvalG (VR l E) (VM l E) j n).hom]
    infer_instance


private def pushLevelIso (b : Base l E) {U T : Scheme.{u}} {j : U ⟶ T}
    [IsOpenImmersion j] (g : Geometry l E b j)
    (c : OpenSiteModel l E b j (tau l E U) (tau l E T)) (M : S l E U) (n : ℕ) :
    (ev l E T n).obj (g.push.obj M) ≅ (ev l E T n).obj (c.push.obj M) :=
  (g.ordinaryPushEvaluation n).app M ≪≫ ((c.evalP n).app M).symm

private theorem pushLevelIso_horizontal (b : Base l E)
    {U T : Scheme.{u}} {j : U ⟶ T} [IsOpenImmersion j] (g : Geometry l E b j)
    (c : OpenSiteModel l E b j (tau l E U) (tau l E T))
    (M : S l E U) {m n : ℕ} (h : n ≤ m) :
    (horizontal l E T h).app (g.push.obj M) ≫
        (restrict l E T h).map (pushLevelIso l E b g c M n).hom =
      (pushLevelIso l E b g c M m).hom ≫
        (horizontal l E T h).app (c.push.obj M) := by
  have hd (k : ℕ) : (pushLevelIso l E b g c M k).hom ≫ (c.evalP k).hom.app M =
      (g.ordinaryPushEvaluation k).hom.app M := by
    simp only [pushLevelIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  apply (cancel_mono ((restrict l E T h).map ((c.evalP n).hom.app M))).mp
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, hd]
  ext V x
  have hg := push_horizontal l E j b g M h V x
  have hc := c.pushHorizontal M h V ((pushLevelIso l E b g c M m).hom.val.app V x)
  have hm := congrArg (fun a ↦ a.val.app V x) (hd m)
  change ((c.evalP m).hom.app M).val.app V
    ((pushLevelIso l E b g c M m).hom.val.app V x) =
      ((g.ordinaryPushEvaluation m).hom.app M).val.app V x at hm
  rw [hm] at hc
  change ((g.ordinaryPushEvaluation n).hom.app M).val.app V
      (HS l E T (tau l E T) h (g.push.obj M) V x) =
    ((c.evalP n).hom.app M).val.app V
      (HS l E T (tau l E T) h (c.push.obj M) V
        ((pushLevelIso l E b g c M m).hom.val.app V x))
  exact hg.trans hc.symm

private theorem pushIso_exists (b : Base l E)
    {U T : Scheme.{u}} {j : U ⟶ T} [IsOpenImmersion j] (g : Geometry l E b j)
    (c : OpenSiteModel l E b j (tau l E U) (tau l E T)) :
    ∃ d : g.push ≅ c.push, ∀ (M : S l E U) (n : ℕ),
      (ev l E T n).map (d.hom.app M) = (pushLevelIso l E b g c M n).hom := by
  have hc (M : S l E U) :=
    SemilinearSections.systemIsoOfEvaluation_exists.{u + 1, u, u + 1}
    (ProEt.topology T) (B l E T) (tau l E T)
    (pushLevelIso l E b g c M) (fun h ↦ pushLevelIso_horizontal l E b g c M h)
  choose d hd using hc
  refine ⟨NatIso.ofComponents d (fun {M N} a ↦ ?_), hd⟩
  ext V x
  have hn := (g.ordinaryPushEvaluation V.unop.1).hom.naturality a
  have hv := (c.evalP V.unop.1).inv.naturality a
  have hs : (ev l E T V.unop.1).map (g.push.map a ≫ (d N).hom) =
      (ev l E T V.unop.1).map ((d M).hom ≫ c.push.map a) := by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hd, hd]
    dsimp only [pushLevelIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
    dsimp only [Functor.comp_map] at hn hv
    rw [← Category.assoc, hn, Category.assoc, hv, Category.assoc]
  exact congrArg (fun a ↦ a.val.app (op V.unop.2) x) hs

private theorem unitComparison_unique
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {P : D ⥤ C} {F' : C' ⥤ D'} {P' : D' ⥤ C'}
    (a : F ⊣ P) (b : F' ⊣ P') (V : C ⥤ C') (W : D ⥤ D')
    (d : P ⋙ V ≅ W ⋙ P') (q e : F ⋙ W ≅ V ⋙ F')
    (hq : ∀ M, V.map (a.unit.app M) ≫ d.hom.app (F.obj M) ≫
      P'.map (q.hom.app M) = b.unit.app (V.obj M))
    (he : ∀ M, V.map (a.unit.app M) ≫ d.hom.app (F.obj M) ≫
      P'.map (e.hom.app M) = b.unit.app (V.obj M)) : q = e := by
  apply Iso.ext_inv
  ext M
  apply (b.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hq' := congrArg (fun a ↦ a ≫ P'.map (q.inv.app M)) (hq M)
  have he' := congrArg (fun a ↦ a ≫ P'.map (e.inv.app M)) (he M)
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app] at hq' he'
  exact hq'.symm.trans he'

private theorem pullIso_exists (b : Base l E)
    {U T : Scheme.{u}} {j : U ⟶ T} [IsOpenImmersion j] (g : Geometry l E b j)
    (c : OpenSiteModel l E b j (tau l E U) (tau l E T)) :
    ∃ p : c.pull ≅ g.pull, ∀ n : ℕ,
      Functor.isoWhiskerRight p (ev l E U n) ≪≫ g.ordinaryPullEvaluation n = c.evalG n := by
  obtain ⟨d, hd⟩ := pushIso_exists l E b g c
  let ac := c.adj.ofNatIsoRight d.symm
  let p := ac.leftAdjointUniq g.ordinaryAdjunction
  refine ⟨p, ?_⟩
  intro n
  apply unitComparison_unique c.adj (proEtaleConstantRingAdjunction (R l E n) j)
    (ev l E T n) (ev l E U n) (c.evalP n)
  · intro M
    have hu := ac.unit_leftAdjointUniq_hom_app g.ordinaryAdjunction M
    have hc (N : S l E U) :
        (ev l E T n).map (d.inv.app N) ≫ (g.ordinaryPushEvaluation n).hom.app N =
          (c.evalP n).hom.app N := by
      apply (cancel_epi ((ev l E T n).map (d.hom.app N))).mp
      rw [← CategoryTheory.Functor.map_comp_assoc, d.hom_inv_id_app,
        CategoryTheory.Functor.map_id, Category.id_comp, hd]
      simp only [pushLevelIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
        Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    have hn := (g.ordinaryPushEvaluation n).hom.naturality (p.hom.app M)
    dsimp only [Functor.comp_map] at hn
    have hh := geometry_unit_evaluation l E b g n M
    have he : (ev l E T n).map (c.adj.unit.app M) ≫
        (c.evalP n).hom.app (c.pull.obj M) ≫
          (proEtaleConstantRingPushforward (R l E n) j).map
            ((ev l E U n).map (p.hom.app M)) =
        (ev l E T n).map (g.ordinaryAdjunction.unit.app M) ≫
          (g.ordinaryPushEvaluation n).hom.app (g.pull.obj M) := by
      calc
        _ = (ev l E T n).map (c.adj.unit.app M) ≫
            (ev l E T n).map (d.inv.app (c.pull.obj M)) ≫
            (g.ordinaryPushEvaluation n).hom.app (c.pull.obj M) ≫
            (proEtaleConstantRingPushforward (R l E n) j).map
              ((ev l E U n).map (p.hom.app M)) := by
          rw [← hc]
          simp only [Category.assoc]
        _ = (ev l E T n).map (c.adj.unit.app M) ≫
            (ev l E T n).map (d.inv.app (c.pull.obj M)) ≫
            (ev l E T n).map (g.push.map (p.hom.app M)) ≫
            (g.ordinaryPushEvaluation n).hom.app (g.pull.obj M) := by
          simpa only [Category.assoc] using congrArg
            (fun z ↦ (ev l E T n).map (c.adj.unit.app M) ≫
              (ev l E T n).map (d.inv.app (c.pull.obj M)) ≫ z) hn.symm
        _ = _ := by
          rw [← CategoryTheory.Functor.map_comp_assoc,
            ← CategoryTheory.Functor.map_comp_assoc]
          rw [show (c.adj.unit.app M ≫ d.inv.app (c.pull.obj M)) ≫
            g.push.map (p.hom.app M) = g.ordinaryAdjunction.unit.app M from
              (by simpa only [ac, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
                Iso.symm_hom, Functor.whiskerLeft_app, Category.assoc] using hu)]
    apply Eq.trans _ hh
    simpa only [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.trans_hom,
      NatTrans.comp_app, CategoryTheory.Functor.map_comp, Category.assoc] using congrArg
      (fun z ↦ z ≫ (proEtaleConstantRingPushforward (R l E n) j).map
        ((g.ordinaryPullEvaluation n).hom.app M)) he
  · exact c.unitG n

private theorem openMate_isIso (b : Base l E)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (g : Geometry l E b j)
    (c : OpenSiteModel l E b j (tau l E U) (tau l E T))
    (p : c.pull ≅ g.pull)
    (hp : ∀ n : ℕ, Functor.isoWhiskerRight p (ev l E U n) ≪≫
      g.ordinaryPullEvaluation n = c.evalG n) (n : ℕ) :
    IsIso ((mateEquiv (c.openAdj.ofNatIsoRight p)
      (finiteOpenAdjunction l E b j n)).symm (g.ordinaryPullEvaluation n).hom).natTrans := by
  rw [inverseMate_rightIso]
  have he : Functor.whiskerRight p.hom (ev l E U n) ≫
      (g.ordinaryPullEvaluation n).hom = (c.evalG n).hom := congrArg Iso.hom (hp n)
  rw [he]
  exact c.openMate n

private theorem open_exists (b : Base l E)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (g : Geometry l E b j) :
    ∃ o : Open l E b j g, IsIso o.derivedAdjunction.unit ∧
      ∀ (K : D l E U) (L : D l E T),
        (openD l E b o).essImage ((tensor l E b T).obj ((openD l E b o).obj K, L)) := by
  obtain ⟨c⟩ := openSiteModel_exists l E b j (tau l E U) (tau l E T)
    (tau_eq l E U) (tau_eq l E T)
  obtain ⟨p, hp⟩ := pullIso_exists l E b g c
  let F := c.extension
  let a : F ⊣ g.pull := c.openAdj.ofNatIsoRight p
  have hi (n : ℕ) : IsIso
      ((mateEquiv a (finiteOpenAdjunction l E b j n)).symm
        (g.ordinaryPullEvaluation n).hom).natTrans := openMate_isIso l E b j g c p hp n
  let e (n : ℕ) := (asIso
    ((mateEquiv a (finiteOpenAdjunction l E b j n)).symm
      (g.ordinaryPullEvaluation n).hom).natTrans).symm
  have hu (n : ℕ) (M : S l E U) :
      (ev l E U n).map (a.unit.app M) ≫
          (g.ordinaryPullEvaluation n).hom.app (F.obj M) ≫
          (proEtaleConstantRingPullback (R l E n) j).map ((e n).hom.app M) =
        (finiteOpenAdjunction l E b j n).unit.app ((ev l E U n).obj M) := by
    rw [← Category.assoc, unit_mateEquiv_symm, Category.assoc, ← CategoryTheory.Functor.map_comp]
    change _ ≫ (proEtaleConstantRingPullback (R l E n) j).map
      ((e n).inv.app M ≫ (e n).hom.app M) = _
    rw [(e n).inv_hom_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  have hc (n : ℕ) (M : S l E T) :
      (e n).inv.app (g.pull.obj M) ≫ (ev l E T n).map (a.counit.app M) =
        (sfIntrinsicExtensionByZero j (R l E n)).map
          ((g.ordinaryPullEvaluation n).hom.app M) ≫
          (finiteOpenAdjunction l E b j n).counit.app ((ev l E T n).obj M) := by
    have h := counit_evaluation a (finiteOpenAdjunction l E b j n)
      (ev l E U n) (ev l E T n) (e n) (g.ordinaryPullEvaluation n) (hu n) M
    apply ((finiteOpenAdjunction l E b j n).homEquiv
      ((ev l E U n).obj (g.pull.obj M)) ((ev l E T n).obj M)).injective
    calc
      _ = (g.ordinaryPullEvaluation n).hom.app M := by
        simpa only [Functor.id_obj] using h
      _ = _ := by
        simpa only [Adjunction.homEquiv_counit] using
          (((finiteOpenAdjunction l E b j n).homEquiv
            ((ev l E U n).obj (g.pull.obj M)) ((ev l E T n).obj M)).apply_symm_apply
              ((g.ordinaryPullEvaluation n).hom.app M)).symm
  let o : Open l E b j g := {
    extension := F
    ordinaryAdjunction := a
    evaluation := e
    ordinaryPullEvaluation := g.ordinaryPullEvaluation
    ordinaryPullEvaluation_eq := g.ordinaryPullEvaluation_eq
    unit_evaluation := hu
    counit_evaluation := hc
    derivedAdjunction := a.mapExactDerivedCategory
    unit_termwise := exact_unit_termwise l E a
    counit_termwise := exact_counit_termwise l E a }
  have := c.openUnit
  let q : F ⋙ g.pull ≅ 𝟭 (S l E U) :=
    Functor.isoWhiskerLeft F p.symm ≪≫ (asIso c.openAdj.unit).symm
  have := a.isIso_unit_of_iso q
  let z : openD l E b o ⋙ pull l E b g ≅ 𝟭 (D l E U) :=
    (Functor.mapDerivedCategoryCompIso F g.pull).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso a.unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso _
  exact ⟨o, o.derivedAdjunction.isIso_unit_of_iso z,
    c.support (b.calculus T).closed (b.calculus T).tensorModels⟩


private theorem tensor_transpose_iso (b : Base l E)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (g : Geometry l E b j)
    (o : Open l E b j g) [IsIso o.derivedAdjunction.unit]
    (hs : ∀ (K : D l E U) (L : D l E T),
      (openD l E b o).essImage ((tensor l E b T).obj ((openD l E b o).obj K, L)))
    (K : D l E U) (L : D l E T) :
    IsIso ((o.derivedAdjunction.homEquiv _ _).symm
      ((tensor l E b U).map (Prod.mkHom (o.derivedAdjunction.unit.app K) (𝟙 _)) ≫
        g.tensorPullback.inv.app ((openD l E b o).obj K, L))) := by
  let ff := o.derivedAdjunction.fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have hc : IsIso (o.derivedAdjunction.counit.app
      ((tensor l E b T).obj ((openD l E b o).obj K, L))) :=
    o.derivedAdjunction.isIso_counit_app_of_iso (hs K L).getIso.symm
  have hp : IsIso (Prod.mkHom (o.derivedAdjunction.unit.app K)
      (𝟙 ((pull l E b g).obj L))) := (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  rw [Adjunction.homEquiv_counit]
  infer_instance

/-- Exact open extension in already fixed geometric coordinates has invertible
tensor-adjunction transpose. The forward tensor isomorphism is not chosen here:
it is recovered by inverting this specified arrow.
Source: blueprint operations proof (2), open tensor step; Stacks 03DI, 0E8I
and 0GL1; openTensorNormalization on the ringed sequence site.
(blueprint: lem-sp-strict-open-tensor-coordinates).

Proof: form extension by zero on the vertical sequence site, using direct sums
over the open factorizations and sheafification. The coefficient action and
the adjacent transitions come from the actual quotient maps. The ordinary
summand Hom correspondence gives the adjunction to the supplied g.pull;
its identity-on-open-sections normalization agrees with the constant-section
level adjunction. This gives both ordinary evaluation equations and their
unit and counit formulas. Exactness permits termwise localization of the
extension, unit and counit, giving Open with its two termwise equations.
Apply the open tensor support argument on this same ringed sequence site.
On the open, the adjunction unit is invertible and the inverse tensor
pullback comparison identifies the displayed transpose with the identity.
On the complementary closed part both sides are zero. The open/closed
restriction functors jointly detect isomorphisms, so this actual system
arrow is invertible. The signed representative normalization of g's tensor
comparison identifies it with precisely the displayed transpose, rather
than an independently chosen isomorphism. These statements include the
empty open, the identity open and zero complexes; they require no flatness
of any quotient transition and do not infer equality of derived arrows
from their evaluations. -/
theorem strictOpenTensorCoordinates (b : Base l E)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (g : Geometry l E b j) :
    ∃ o : Open l E b j g, ∀ (K : D l E U) (L : D l E T),
      IsIso ((o.derivedAdjunction.homEquiv _ _).symm
        ((tensor l E b U).map (Prod.mkHom (o.derivedAdjunction.unit.app K) (𝟙 _)) ≫
          g.tensorPullback.inv.app ((openD l E b o).obj K, L))) := by
  obtain ⟨o, hu, hs⟩ := open_exists l E b j g
  have := hu
  exact ⟨o, tensor_transpose_iso l E b j g o hs⟩

end AlgebraicGeometry.ProEtale.SpTowerShriek
