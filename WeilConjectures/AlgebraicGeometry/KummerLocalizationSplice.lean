/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KummerLocalizationSpliceDefs
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctor
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Forget
import WeilConjectures.AlgebraicGeometry.RawModuleScalarComparison.RawModuleScalarDerivedPullbackIso
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedKummerBoundaryPullback
import WeilConjectures.AlgebraicGeometry.PrincipalTorsorOpenSections
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Coefficients in the Kummer localization splice
Source: Stacks Tags 03PL and 0A45, coefficient step of the principal Cartier formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem exact_ext_naturality {C D : Type*}
    [Category C] [Abelian C] [Category D] [Abelian D]
    [HasExt.{u + 1} C] [HasExt.{u + 1} D] [EnoughInjectives C]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (α : F ⟶ G) {X Y : C} {n : ℕ} (x : Ext X Y n) :
    (x.mapExactFunctor F).comp (Ext.mk₀ (α.app Y)) (add_zero n) =
      (Ext.mk₀ (α.app X)).comp (x.mapExactFunctor G) (zero_add n) := by
  induction n generalizing Y with
  | zero =>
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X Y).2 x
    simp only [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
    exact congrArg Ext.mk₀ (α.naturality f)
  | succ n ih =>
    let ι := Injective.ι Y
    let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel ι }
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ X hS x
      (Ext.eq_zero_of_injective _) rfl
    let φ : S.map F ⟶ S.map G :=
      { τ₁ := α.app _, τ₂ := α.app _, τ₃ := α.app _
        comm₁₂ := (α.naturality S.f).symm
        comm₂₃ := (α.naturality S.g).symm }
    have hn := ShortComplex.ShortExact.extClass_naturality
      (hS.map_of_exact F) (hS.map_of_exact G) φ
    change ((hS.map_of_exact F).extClass).comp (Ext.mk₀ (α.app Y)) (add_zero 1) =
      (Ext.mk₀ (α.app S.X₃)).comp (hS.map_of_exact G).extClass (zero_add 1) at hn
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp,
      Ext.mapExactFunctor_extClass, Ext.mapExactFunctor_extClass,
      Ext.comp_assoc_of_third_deg_zero, hn,
      ← Ext.comp_assoc_of_second_deg_zero, ih]
    exact Ext.comp_assoc (Ext.mk₀ (α.app X)) (y.mapExactFunctor G)
      ((hS.map_of_exact G).extClass) (zero_add n) rfl (by omega)

private theorem ext_localization_splice {C D : Type*}
    [Category C] [Abelian C] [Category D] [Abelian D]
    [HasExt.{u + 1} C] [HasExt.{u + 1} D]
    (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {SZ : ShortComplex D} {SA : ShortComplex C}
    (hZ : SZ.ShortExact) (hA : SA.ShortExact) (φ : SZ ⟶ SA.map G)
    {P I : C} {Q : D} (aA : P ⟶ SA.X₃) (aZ : Q ⟶ SZ.X₃)
    (gen : Q ⟶ G.obj P) (hc : gen ≫ G.map aA = aZ ≫ φ.τ₃)
    (κ : Ext SA.X₁ I 1) (b : Ext SZ.X₁ (G.obj I) 1)
    (ho : (Ext.mk₀ φ.τ₁).comp (κ.mapExactFunctor G) (zero_add 1) = b) :
    (Ext.mk₀ gen).comp
      (((Ext.mk₀ aA).comp (hA.extClass.comp κ rfl) (zero_add 2)).mapExactFunctor G)
      (zero_add 2) =
    (Ext.mk₀ aZ).comp (hZ.extClass.comp b rfl) (zero_add 2) := by
  have hn := hZ.extClass_naturality (hA.map_of_exact G) φ
  rw [← Ext.mapExactFunctor_extClass G hA] at hn
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [Ext.mk₀_comp_mk₀_assoc, hc, ← Ext.mk₀_comp_mk₀_assoc]
  congr 1
  rw [← Ext.comp_assoc _ _ _ (zero_add 1) rfl (show 0 + 1 + 1 = 2 from rfl),
    ← hn, Ext.comp_assoc_of_second_deg_zero, ho]

private def lowerShriekCoefficientMate (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    moduleAbelianForget A U ⋙ openImmersionLowerShriek AddCommGrpCat.{u + 1} j ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⋙ moduleAbelianForget A T :=
  ((CategoryTheory.mateEquiv
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    (openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1} j)).symm
      (TwoSquare.mk _ _ _ _ (moduleAbelianUpperStarIso A j).inv)).natTrans

private theorem lowerShriekCoefficientMate_counit (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (X : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (lowerShriekCoefficientMate A j).app ((upperStar (ModuleCat.{u + 1} A) j).obj X) ≫
      (moduleAbelianForget A T).map
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
          j).counit.app X) =
      (openImmersionLowerShriek AddCommGrpCat.{u + 1} j).map
        ((moduleAbelianUpperStarIso A j).inv.app X) ≫
        (openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1}
          j).counit.app ((moduleAbelianForget A T).obj X) := by
  exact (CategoryTheory.mateEquiv_counit_symm
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    (openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1} j)
    (TwoSquare.mk _ _ _ _ (moduleAbelianUpperStarIso A j).inv) X).symm

private def coefficient_localization_map (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ) :
    openClosedShortComplex AddCommGrpCat.{u + 1} W.ι i
        (disjoint_range_of_range_eq_compl W.ι i h) (supportedIntegralConstant T) ⟶
      (openClosedShortComplex (ModuleCat.{u + 1} A) W.ι i
        (disjoint_range_of_range_eq_compl W.ι i h) (ordinaryFiniteConstant A T)).map
          (RawModuleScalarComparison.forget A T) := by
  let SZ := openClosedShortComplex AddCommGrpCat.{u + 1} W.ι i
    (disjoint_range_of_range_eq_compl W.ι i h) (supportedIntegralConstant T)
  let SA := openClosedShortComplex (ModuleCat.{u + 1} A) W.ι i
    (disjoint_range_of_range_eq_compl W.ι i h) (ordinaryFiniteConstant A T)
  let G := RawModuleScalarComparison.forget A T
  let r := (lowerStar AddCommGrpCat.{u + 1} i).map
    ((upperStar AddCommGrpCat.{u + 1} i).map (ordinaryFiniteIntegralGenerator A T) ≫
      (moduleAbelianUpperStarComparison A i).app (ordinaryFiniteConstant A T))
  have h23 : ordinaryFiniteIntegralGenerator A T ≫ G.map SA.g = SZ.g ≫ r := by
    change ordinaryFiniteIntegralGenerator A T ≫
      (RawModuleScalarComparison.forget A T).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit.app _) = _
    rw [← RawModuleScalarComparison.pullback_unit]
    rw [← Category.assoc]
    erw [(upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.naturality
      (ordinaryFiniteIntegralGenerator A T)]
    simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
    rfl
  have hz : (SZ.f ≫ ordinaryFiniteIntegralGenerator A T) ≫ G.map SA.g = 0 := by
    rw [Category.assoc, h23, ← Category.assoc, SZ.zero, zero_comp]
  have hSA : (SA.map G).ShortExact :=
    (shortExact_openClosedShortComplex (ModuleCat.{u + 1} A)
      W.ι i (ordinaryFiniteConstant A T) h).map_of_exact G
  letI := hSA.mono_f
  exact
    { τ₁ := hSA.exact.lift (SZ.f ≫ ordinaryFiniteIntegralGenerator A T) hz
      τ₂ := ordinaryFiniteIntegralGenerator A T
      τ₃ := r
      comm₁₂ := hSA.exact.lift_f _ _
      comm₂₃ := h23 }

private theorem coefficient_closed_normalization (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ) :
    (lowerStar AddCommGrpCat.{u + 1} i).map
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} i).app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv ≫
      (coefficient_localization_map A i W h).τ₃ =
    supportedIntegralGenerator A i ≫
      (RawModuleScalarComparison.forget A T).map
        ((lowerStar (ModuleCat.{u + 1} A) i).map
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app
            (ModuleCat.of A A)).inv) := by
  dsimp only [coefficient_localization_map, supportedIntegralGenerator]
  dsimp only [RawModuleScalarComparison.forget]
  rw [forget_lowerStar_map A i, ← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (lowerStar AddCommGrpCat.{u + 1} i).map
  apply (cancel_mono ((moduleAbelianForget A D).map
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app
      (ModuleCat.of A A)).hom)).mp
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rw [integralGenerator_pullback]
  exact ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} i).app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv_hom_id_assoc _

private theorem coefficient_open_normalization (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ) :
    (coefficient_localization_map A i W h).τ₁ =
      (openImmersionLowerShriek AddCommGrpCat.{u + 1} W.ι).map
        ((upperStar AddCommGrpCat.{u + 1} W.ι).map
            (ordinaryFiniteIntegralGenerator A T) ≫
          (moduleAbelianUpperStarIso A W.ι).hom.app (ordinaryFiniteConstant A T)) ≫
        (lowerShriekCoefficientMate A W.ι).app
          ((upperStar (ModuleCat.{u + 1} A) W.ι).obj (ordinaryFiniteConstant A T)) := by
  let SA := openClosedShortComplex (ModuleCat.{u + 1} A) W.ι i
    (disjoint_range_of_range_eq_compl W.ι i h) (ordinaryFiniteConstant A T)
  have hSA := (shortExact_openClosedShortComplex (ModuleCat.{u + 1} A) W.ι i
    (ordinaryFiniteConstant A T) h).map_of_exact (moduleAbelianForget A T)
  let _ : Mono ((moduleAbelianForget A T).map SA.f) := hSA.mono_f
  apply (cancel_mono ((moduleAbelianForget A T).map SA.f)).1
  erw [(coefficient_localization_map A i W h).comm₁₂]
  rw [Category.assoc]
  change _ = _ ≫ ((lowerShriekCoefficientMate A W.ι).app _ ≫
    (moduleAbelianForget A T).map
      ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
        W.ι).counit.app _))
  rw [lowerShriekCoefficientMate_counit]
  simp only [← Functor.map_comp_assoc, Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  exact ((openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1}
    W.ι).counit.naturality (ordinaryFiniteIntegralGenerator A T)).symm

private theorem finiteKummerUnitClass_forget (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤)))
    (s : Γ(T, ⊤)ˣ) :
    (Ext.mk₀ (ordinaryFiniteIntegralGenerator A T)).comp
      ((finiteKummerUnitClass A N hA T hT s).mapExactFunctor
        (RawModuleScalarComparison.forget A T)) (zero_add 1) =
      (((Sheaf.H.equiv₀ T.gmSheaf
        (MorphismProperty.Over.mkIdTerminal @Etale T)).symm
          ⟨Additive.ofMul s⟩).comp
        (T.kummerSequence_shortExact N hT).extClass (zero_add 1)).comp
          (Ext.mk₀ (ordinaryFiniteRootMap A N hA T)) (add_zero 1) := by
  have hc := ordinaryFiniteClass_extHomEquiv A T
    (Scheme.finiteEtaleTateLine T N A hA) 1 (finiteKummerUnitClass A N hA T hT s)
  rw [finiteKummerUnitClass, Equiv.apply_symm_apply] at hc
  rw [← ordinaryFiniteClassEquiv_apply, Equiv.apply_symm_apply] at hc
  change Sheaf.H.map (ordinaryFiniteRootMap A N hA T) 1
    (T.kummerδ₀ N hT (Additive.ofMul s)) = _ at hc
  exact hc.symm

private theorem finiteKummerOpenClass_forget (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (hT : IsUnit (N : Γ(T, ⊤))) (s : Γ(W.toScheme, ⊤)ˣ) :
    (Ext.mk₀ (coefficient_localization_map A i W h).τ₁).comp
      ((finiteKummerOpenClass A N hA t T W hT s).mapExactFunctor
        (moduleAbelianForget A T)) (zero_add 1) =
    (Ext.mk₀ ((openImmersionLowerShriek AddCommGrpCat.{u + 1} W.ι).map
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} W.ι).app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom)).comp
      ((((Ext.mk₀ (ordinaryFiniteIntegralGenerator A W.toScheme)).comp
        ((finiteKummerUnitClass A N hA W.toScheme
          (by simpa using hT.map W.ι.appTop.hom) s).mapExactFunctor
            (moduleAbelianForget A W.toScheme)) (zero_add 1)).mapExactFunctor
              (openImmersionLowerShriek AddCommGrpCat.{u + 1} W.ι)).comp
        (Ext.mk₀ ((openImmersionLowerShriek AddCommGrpCat.{u + 1} W.ι).map
          ((moduleAbelianForget A W.toScheme).map (t.line W.ι hT).inv ≫
            (moduleAbelianUpperStarIso A W.ι).inv.app _) ≫
          (openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1}
            W.ι).counit.app _)) (add_zero 1)) (zero_add 1) := by
  let JM := openImmersionLowerShriek (ModuleCat.{u + 1} A) W.ι
  let JZ := openImmersionLowerShriek AddCommGrpCat.{u + 1} W.ι
  let GT := moduleAbelianForget A T
  let GW := moduleAbelianForget A W.toScheme
  let α := lowerShriekCoefficientMate A W.ι
  let cM := (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) W.ι).app
    (ModuleCat.of A A)
  let cZ := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} W.ι).app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let L := Scheme.finiteEtaleTateLine W.toScheme N A hA
  let ε := JM.map (t.line W.ι hT).inv ≫
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
      W.ι).counit.app (Scheme.finiteEtaleTateLine T N A hA)
  let κ := finiteKummerUnitClass A N hA W.toScheme
    (by simpa using hT.map W.ι.appTop.hom) s
  have hsrc : (coefficient_localization_map A i W h).τ₁ ≫ GT.map (JM.map cM.hom) =
      JZ.map (cZ.hom ≫ ordinaryFiniteIntegralGenerator A W.toScheme) ≫
        α.app (ordinaryFiniteConstant A W.toScheme) := by
    rw [coefficient_open_normalization]
    rw [Category.assoc]
    erw [← α.naturality cM.hom]
    change JZ.map _ ≫ JZ.map (GW.map cM.hom) ≫ _ = _
    rw [← JZ.map_comp_assoc]
    congr 2
    simpa only [cM, cZ, GW, moduleUpperStarIso_hom, Category.assoc] using
      integralGenerator_pullback A W.ι
  have hε : α.app L ≫ GT.map ε =
      JZ.map (GW.map (t.line W.ι hT).inv ≫
        (moduleAbelianUpperStarIso A W.ι).inv.app _) ≫
        (openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1}
          W.ι).counit.app _ := by
    dsimp only [ε]
    rw [GT.map_comp, ← Category.assoc]
    erw [← α.naturality (t.line W.ι hT).inv]
    rw [Category.assoc, lowerShriekCoefficientMate_counit]
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
    rfl
  have hn := exact_ext_naturality (GW ⋙ JZ) (JM ⋙ GT) α κ
  rw [← Ext.mapExactFunctor_mapExactFunctor GW JZ,
    ← Ext.mapExactFunctor_mapExactFunctor JM GT] at hn
  have hmid : (Ext.mk₀ (α.app (ordinaryFiniteConstant A W.toScheme))).comp
      (((κ.mapExactFunctor JM).mapExactFunctor GT).comp
        (Ext.mk₀ (GT.map ε)) (add_zero 1)) (zero_add 1) =
      ((κ.mapExactFunctor GW).mapExactFunctor JZ).comp
        (Ext.mk₀ (JZ.map (GW.map (t.line W.ι hT).inv ≫
          (moduleAbelianUpperStarIso A W.ι).inv.app _) ≫
          (openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1}
            W.ι).counit.app _)) (add_zero 1) := by
    rw [← Ext.comp_assoc_of_third_deg_zero, ← hn,
      Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, hε]
  change (Ext.mk₀ (coefficient_localization_map A i W h).τ₁).comp
    (((Ext.mk₀ (JM.map cM.hom)).comp
      ((κ.mapExactFunctor JM).comp (Ext.mk₀ ε) (add_zero 1))
        (zero_add 1)).mapExactFunctor GT) (zero_add 1) = _
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [Ext.mk₀_comp_mk₀_assoc, hsrc, ← Ext.mk₀_comp_mk₀_assoc]
  erw [hmid]
  simp only [Functor.map_comp, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀_assoc]
  rfl

private theorem inverse_ext_square_local {B : Type*} [Category B] [Abelian B]
    [HasExt.{u + 1} B] {X X' Y Y' : B} (b : X ≅ X') (c : Y ≅ Y')
    (x : Ext X Y 1) (y : Ext X' Y' 1)
    (h : (Ext.mk₀ b.hom).comp y (zero_add 1) =
      x.comp (Ext.mk₀ c.hom) (add_zero 1)) :
    y.comp (Ext.mk₀ c.inv) (add_zero 1) =
      (Ext.mk₀ b.inv).comp x (zero_add 1) := by
  have hn := congrArg (fun z => (Ext.mk₀ b.inv).comp
    (z.comp (Ext.mk₀ c.inv) (add_zero 1)) (zero_add 1)) h
  simpa only [Ext.comp_assoc_of_third_deg_zero,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    Iso.inv_hom_id, Iso.hom_inv_id, Ext.mk₀_id_comp, Ext.comp_mk₀_id] using hn

private theorem kummer_inverse_pullback_local (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {T : Scheme.{u}} (W : T.Opens) (hT : IsUnit (N : Γ(T, ⊤)))
    (hW : IsUnit (N : Γ(W.toScheme, ⊤))) :
    let G := moduleAbelianForget A W.toScheme
    let c := (moduleAbelianUpperStarIso A W.ι).app
      (Scheme.finiteEtaleTateLine T N A hA) ≪≫ G.mapIso (t.line W.ι hT)
    let b := Scheme.upperStarGmSheafIso W.ι
    (ProEtale.cartierEtaleKummerUnit A N hA W.toScheme hW).comp
      (Ext.mk₀ c.inv) (add_zero 1) =
      (Ext.mk₀ b.inv).comp
        ((ProEtale.cartierEtaleKummerUnit A N hA T hT).mapExactFunctor
          (upperStar AddCommGrpCat.{u + 1} W.ι)) (zero_add 1) := by
  intro G c b
  apply inverse_ext_square_local b c
  simpa only [b, c, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    moduleUpperStarIso_hom, Scheme.upperStarGmSheafIso, asIso_hom] using
      kummerUnit_pullback A N hA t W.ι hT hW

set_option maxHeartbeats 800000 in
-- The counit calculation compares two presentations of the derived pullback.
private theorem kummer_open_counit_local (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {T : Scheme.{u}} (W : T.Opens) (hT : IsUnit (N : Γ(T, ⊤)))
    (hW : IsUnit (N : Γ(W.toScheme, ⊤))) :
    let J := openImmersionLowerShriek AddCommGrpCat.{u + 1} W.ι
    let G := moduleAbelianForget A W.toScheme
    let c := (moduleAbelianUpperStarIso A W.ι).app
      (Scheme.finiteEtaleTateLine T N A hA) ≪≫ G.mapIso (t.line W.ι hT)
    let b := Scheme.upperStarGmSheafIso W.ι
    ((ProEtale.cartierEtaleKummerUnit A N hA W.toScheme hW).mapExactFunctor J).comp
      (Ext.mk₀ (J.map c.inv ≫
        (openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1}
          W.ι).counit.app _)) (add_zero 1) =
      (Ext.mk₀ (J.map b.inv ≫
        (openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1}
          W.ι).counit.app T.gmSheaf)).comp
        (ProEtale.cartierEtaleKummerUnit A N hA T hT) (zero_add 1) := by
  intro J G c b
  let R := upperStar AddCommGrpCat.{u + 1} W.ι
  have hKU' := kummer_inverse_pullback_local A N hA t W hT hW
  have hopen : ((ProEtale.cartierEtaleKummerUnit A N hA W.toScheme hW).mapExactFunctor
      J).comp (Ext.mk₀ (J.map c.inv)) (add_zero 1) =
      (Ext.mk₀ (J.map b.inv)).comp
        (((ProEtale.cartierEtaleKummerUnit A N hA T hT).mapExactFunctor R).mapExactFunctor
          J) (zero_add 1) := by
    rw [← Ext.mapExactFunctor_mk₀ J, ← Ext.mapExactFunctor_comp, hKU',
      Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  have hn := exact_ext_naturality (R ⋙ J) (𝟭 _)
    (openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1} W.ι).counit
      (ProEtale.cartierEtaleKummerUnit A N hA T hT)
  rw [← Ext.mapExactFunctor_mapExactFunctor R J, Ext.mapExactFunctor_id] at hn
  rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero,
    hopen, Ext.comp_assoc_of_third_deg_zero, hn, Ext.mk₀_comp_mk₀_assoc]

private theorem finiteKummerOpenClass_splice (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (C : PrincipalTorsorComparisons.{u}) (hC : C.Normalized)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (hT : IsUnit (N : Γ(T, ⊤))) (s : Γ(W.toScheme, ⊤)ˣ) :
    (Ext.mk₀ (coefficient_localization_map A i W h).τ₁).comp
      ((finiteKummerOpenClass A N hA t T W hT s).mapExactFunctor
        (moduleAbelianForget A T)) (zero_add 1) =
      (Ext.mk₀ ((C.openSection T D i W h T.gmSheaf).symm
        ⟨Additive.ofMul s⟩)).comp
          (ProEtale.cartierEtaleKummerUnit A N hA T hT) (zero_add 1) := by
  let J := openImmersionLowerShriek AddCommGrpCat.{u + 1} W.ι
  let G := moduleAbelianForget A W.toScheme
  let hW : IsUnit (N : Γ(W.toScheme, ⊤)) := by simpa using hT.map W.ι.appTop.hom
  let c := ((moduleAbelianUpperStarIso A W.ι).app
    (Scheme.finiteEtaleTateLine T N A hA)) ≪≫ G.mapIso (t.line W.ι hT)
  let b := Scheme.upperStarGmSheafIso W.ι
  have hloc := kummer_open_counit_local A N hA t W hT hW
  obtain ⟨v, hv⟩ := (Ext.mk₀_bijective _ _).2
    ((Sheaf.H.equiv₀ W.toScheme.gmSheaf
      (MorphismProperty.Over.mkIdTerminal @Etale W.toScheme)).symm
        (show W.toScheme.gmSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 W.toScheme))) from
          ⟨Additive.ofMul s⟩))
  -- Associate the root coefficient map before folding the Kummer unit class.
  rw [finiteKummerOpenClass_forget, finiteKummerUnitClass_forget, ← hv,
    Ext.comp_assoc_of_third_deg_zero]
  change (Ext.mk₀ (J.map _)).comp
    ((((Ext.mk₀ v).comp (ProEtale.cartierEtaleKummerUnit A N hA W.toScheme hW)
      (zero_add 1)).mapExactFunctor J).comp
        (Ext.mk₀ (J.map c.inv ≫
          (openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1}
            W.ι).counit.app _)) (add_zero 1)) (zero_add 1) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, hloc]
  rw [principalTorsorOpenUnit C hC, ← hv]
  erw [Ext.addEquiv₀.apply_symm_apply]
  simp only [Functor.map_comp, Category.assoc, Ext.mk₀_comp_mk₀_assoc]
  rfl

set_option maxHeartbeats 800000 in
-- The closed-source comparison reduces through the localization definitions.
/-- Forgetting module coefficients in the localization splice agrees with splicing
its integral boundary with the Kummer extension and then applying the root coefficient map.
Source: Stacks Tags 03PL and 0A45, naturality of localization and the Kummer boundary.
(blueprint: lem-pur-kummer-localization-splice).
Proof: first the defining ordinary class comparison identifies the module representative
of a unit boundary with the integral unit map spliced with the Kummer extension. The
kernel-normalized root and line inverse-image maps identify its open restriction with
the corresponding splice on the ambient site. Exact forgetting commutes with extension
by zero; its adjunction mate respects the counit. The integral-to-module constant maps
therefore give a morphism of the open-closed coefficient sequences. Naturality of their
extension classes and associativity of Yoneda composition give the displayed equation.
All constructions use the canonical constant comparisons, so there is no choice of
an unnormalized localization boundary. -/
theorem kummerLocalizationSplice (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (C : PrincipalTorsorComparisons.{u}) (hC : C.Normalized)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (hT : IsUnit (N : Γ(T, ⊤))) (s : Γ(W.toScheme, ⊤)ˣ) :
    (Ext.mk₀ (supportedIntegralGenerator A i)).comp
      ((finiteKummerLocalizationBoundary A N hA t i W h hT s).mapExactFunctor
        (RawModuleScalarComparison.forget A T)) (zero_add 2) =
    ((integralLocalizationBoundary C i W h ⟨Additive.ofMul s⟩).comp
      (T.kummerSequence_shortExact N hT).extClass (rfl : 1 + 1 = 2)).comp
        (Ext.mk₀ (ordinaryFiniteRootMap A N hA T)) (add_zero 2) := by
  let SZ := openClosedShortComplex AddCommGrpCat.{u + 1} W.ι i
    (disjoint_range_of_range_eq_compl W.ι i h) (supportedIntegralConstant T)
  let SA := openClosedShortComplex (ModuleCat.{u + 1} A) W.ι i
    (disjoint_range_of_range_eq_compl W.ι i h) (ordinaryFiniteConstant A T)
  let hZ := shortExact_openClosedShortComplex AddCommGrpCat.{u + 1} W.ι i
    (supportedIntegralConstant T) h
  let hM := shortExact_openClosedShortComplex (ModuleCat.{u + 1} A) W.ι i
    (ordinaryFiniteConstant A T) h
  have hs := ext_localization_splice (moduleAbelianForget A T) hZ hM
    (coefficient_localization_map A i W h)
    ((lowerStar (ModuleCat.{u + 1} A) i).map
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app
        (ModuleCat.of A A)).inv)
    ((lowerStar AddCommGrpCat.{u + 1} i).map
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} i).app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)
    (supportedIntegralGenerator A i) (coefficient_closed_normalization A i W h).symm
    (finiteKummerOpenClass A N hA t T W hT s)
    ((Ext.mk₀ ((C.openSection T D i W h T.gmSheaf).symm
      ⟨Additive.ofMul s⟩)).comp (ProEtale.cartierEtaleKummerUnit A N hA T hT) (zero_add 1))
    (finiteKummerOpenClass_splice A N hA t C hC i W h hT s)
  change _ = _ at hs
  erw [hs]
  unfold integralLocalizationBoundary ProEtale.cartierEtaleKummerUnit
    ProEtale.cartierKummerClass
  simp only [Ext.comp_assoc_of_third_deg_zero]
  simpa only [Ext.comp_assoc_of_second_deg_zero] using
    (Ext.comp_assoc
      (Ext.mk₀ ((lowerStar AddCommGrpCat.{u + 1} i).map
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} i).app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv))
      (hZ.extClass.comp
        (Ext.mk₀ ((C.openSection T D i W h T.gmSheaf).symm
          ⟨Additive.ofMul s⟩)) (add_zero 1))
      ((T.kummerSequence_shortExact N hT).extClass.comp
        (Ext.mk₀ (ordinaryFiniteRootMap A N hA T)) (add_zero 1))
      (zero_add 1) rfl rfl).symm

end AlgebraicGeometry.Etale
