/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenDerivedSupport
import all WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenDerivedSupport

/-! # Support in a proper/open square

The supported counit remains invertible when the two opens have different sources.
Source: Stacks 0F7B; the Postnikov argument of proper-open derived support.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.ProperOpenSquareSupport

section

attribute [-instance] HasDerivedCategory.ofIsGrothendieckAbelian
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify

private noncomputable local instance (priority := 3000) fixed_sheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X

private noncomputable local instance (priority := 3000) fixed_locallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

private noncomputable local instance fixed_derived (X : Scheme.{u}) (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 2} (proEtaleRingModules X (proEtaleConstantRing X A)) :=
  HasDerivedCategory.standard _

private theorem sheaf_support
    {X Y T₁ T₂ : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : Y ⟶ T₂) (r : X ⟶ Y) [IsProper r]
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (comm : j₁ ≫ f = r ≫ j₂) (A : Type u) [CommRing A] [Finite A]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) :
    IsIso ((sfIntrinsicOpenAdjunction A j₂).counit.app
      ((proEtaleConstantModuleDirectImage f A).obj
        ((sfIntrinsicExtensionByZero j₁ A).obj M))) := by
  let s : X ⟶ CategoryTheory.Limits.pullback f j₂ :=
    CategoryTheory.Limits.pullback.lift j₁ r comm
  have hs : s ≫ CategoryTheory.Limits.pullback.fst f j₂ = j₁ := by simp [s]
  have : IsOpenImmersion (s ≫ CategoryTheory.Limits.pullback.fst f j₂) := by
    rw [hs]
    infer_instance
  have : IsOpenImmersion s := IsOpenImmersion.of_comp s (CategoryTheory.Limits.pullback.fst f j₂)
  let e := (sfIntrinsicOpenComp A s (CategoryTheory.Limits.pullback.fst f j₂)).app M
  let N := (sfIntrinsicExtensionByZero s A).obj M
  have := sfProperOpenSheafComparison_isIso A f j₂
  let d := asIso ((sfProperOpenSheafComparison A
    (CategoryTheory.Limits.pullback.snd f j₂)
    (CategoryTheory.Limits.pullback.fst f j₂) j₂ f
    (IsPullback.of_hasPullback f j₂).flip).app N)
  have : (sfIntrinsicExtensionByZero j₂ A).Full := by
    unfold sfIntrinsicExtensionByZero
    infer_instance
  have : (sfIntrinsicExtensionByZero j₂ A).Faithful := by
    unfold sfIntrinsicExtensionByZero
    infer_instance
  let e' : (sfIntrinsicExtensionByZero j₁ A).obj M ≅
      (sfIntrinsicExtensionByZero (CategoryTheory.Limits.pullback.fst f j₂) A).obj N := by
    simpa only [hs, Functor.comp_obj] using e
  apply (sfIntrinsicOpenAdjunction A j₂).isIso_counit_app_of_iso
  exact (proEtaleConstantModuleDirectImage f A).mapIso e' ≪≫ d.symm

private theorem bounded_support_square
    {X Y T₁ T₂ : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : Y ⟶ T₂) (r : X ⟶ Y) [IsProper r]
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [QuasiCompact j₁] [QuasiCompact j₂]
    (comm : j₁ ≫ f = r ≫ j₂) (A : Type u) [CommRing A] [Finite A]
    (K : proEtaleDerivedCategory X A) (n : ℤ)
    [DerivedCategory.IsGE.{u + 2, u + 1, u + 2}
      (C := proEtaleRingModules X (proEtaleConstantRing X A)) K n] :
    IsIso ((exceptionalOpenAdjunction j₂ A).counit.app
      ((proEtaleConstantDerivedDirectImage f A).obj
        ((sfIntrinsicDerivedOpen A j₁).obj K))) := by
  have hgroth (T : Scheme.{u}) :
      IsGrothendieckAbelian.{u + 1}
        (proEtaleRingModules T (proEtaleConstantRing T A)) := fixed_groth T A
  have := hgroth X
  have := hgroth T₁
  have : EnoughInjectives (proEtaleRingModules X (proEtaleConstantRing X A)) :=
    IsGrothendieckAbelian.enoughInjectives.{u + 1, u + 1, u + 2}
  have : EnoughInjectives (proEtaleRingModules T₁ (proEtaleConstantRing T₁ A)) :=
    IsGrothendieckAbelian.enoughInjectives.{u + 1, u + 1, u + 2}
  have : (sfIntrinsicExtensionByZero j₂ A).Full := by
    unfold sfIntrinsicExtensionByZero
    infer_instance
  have : (sfIntrinsicExtensionByZero j₂ A).Faithful := by
    unfold sfIntrinsicExtensionByZero
    infer_instance
  have : PreservesFiniteLimits (proEtaleConstantModuleDirectImage f A) :=
    (proEtaleConstantModuleDirectImage_additive_leftExact f A).2
  apply bounded_support.{u + 1, u + 2, u + 1, u + 2, u + 1, u + 2, u + 1,
      u + 2, u + 2, u + 2, u + 2, u + 2} (sfIntrinsicExtensionByZero j₁ A)
    (proEtaleConstantModuleDirectImage f A) (sfIntrinsicExtensionByZero j₂ A)
    (sfIntrinsicPullback A j₂) (sfIntrinsicOpenAdjunction A j₂)
    (exceptionalOpenAdjunction j₂ A) (sheaf_support f j₁ j₂ r comm A) ?_ K n
  intro M hM k
  exact (isZero_higherDirectImage_open_injective_of_proper A f r j₁ j₂
    (by simpa using comm) M (k + 1) (by omega)).of_iso
    ((proEtaleConstantModuleDirectImage f A).homologyRightDerivedFunctorObjSingleFunctorIso
      ((sfIntrinsicExtensionByZero j₁ A).obj M) (k + 1)).symm

/-- A proper direct image of an open extension remains supported on the target open
in a commuting proper/open square, for arbitrary unbounded inputs.
Source: Stacks 0F7B and the Postnikov proof of proper-open derived support
(blueprint: lem-sf-proper-open-square-derived-support).

Proof: lift the source open into the Cartesian pullback of the target open.
The ordinary proper/open comparison identifies the direct image with extension
from the target open, so its open counit is invertible. Resolve bounded-below
inputs by injectives; proper/open injective acyclicity computes their direct
images and proves the same counit assertion after localization. Express an
arbitrary complex as the homotopy limit of its lower Postnikov truncations.
Exact countable products, preservation of these products by open extension and
restriction, and preservation of limits by derived direct image let the supported
subcategory pass to that homotopy limit. Naturality transports the assertion
from a representative complex to the given derived object. -/
theorem derived_support_square
    {X Y T₁ T₂ : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : Y ⟶ T₂) (r : X ⟶ Y) [IsProper r]
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [QuasiCompact j₁] [QuasiCompact j₂]
    (_comm : j₁ ≫ f = r ≫ j₂) (A : Type u) [CommRing A] [Finite A]
    (K : proEtaleDerivedCategory X A) :
    IsIso ((exceptionalOpenAdjunction j₂ A).counit.app
      ((proEtaleConstantDerivedDirectImage f A).obj ((sfIntrinsicDerivedOpen A j₁).obj K))) := by
  let C := proEtaleRingModules Y (proEtaleConstantRing Y A)
  let D := proEtaleRingModules T₁ (proEtaleConstantRing T₁ A)
  let E := proEtaleRingModules T₂ (proEtaleConstantRing T₂ A)
  have hex (T : Scheme.{u}) : HasExactLimitsOfShape (Discrete ℕ)
      (proEtaleRingModules T (proEtaleConstantRing T A)) :=
    ProEt.products_exact.{u, u + 1, 0} T ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing T A)) ℕ
  have := hex X
  have := hex Y
  have := hex T₁
  have := hex T₂
  let J₁ := sfIntrinsicExtensionByZero j₁ A
  let J₂ := sfIntrinsicExtensionByZero j₂ A
  let G₂ := sfIntrinsicPullback A j₂
  let P := proEtaleConstantModuleDirectImage f A
  have : PreservesLimitsOfShape (Discrete ℕ) J₁ := intrinsic_open_products A j₁
  have : PreservesLimitsOfShape (Discrete ℕ) J₂ := intrinsic_open_products A j₂
  have : PreservesLimitsOfShape (Discrete ℕ) G₂ := intrinsic_pullback_products A j₂
  have : PreservesLimitsOfShape (Discrete ℕ) J₁.mapDerivedCategory :=
    derived_products_of_Q ℕ J₁
  have : PreservesLimitsOfShape (Discrete ℕ) J₂.mapDerivedCategory :=
    derived_products_of_Q ℕ J₂
  have : PreservesLimitsOfShape (Discrete ℕ) G₂.mapDerivedCategory :=
    derived_products_of_Q ℕ G₂
  have : PreservesLimitsOfShape (Discrete ℕ) P.rightDerivedFunctor :=
    (sfIntrinsicConstantModuleAdjunction f A).mapDerivedCategoryRightDerivedAdjunction
      |>.rightAdjoint_preservesLimits.preservesLimitsOfShape
  have : J₂.Full := by unfold J₂ sfIntrinsicExtensionByZero; infer_instance
  have : J₂.Faithful := by unfold J₂ sfIntrinsicExtensionByZero; infer_instance
  let adj := exceptionalOpenAdjunction j₂ A
  have ff := adj.fullyFaithfulLOfCompIsoId
    ((Functor.mapDerivedCategoryCompIso J₂ G₂).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso (sfIntrinsicOpenAdjunction A j₂).unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso C)
  have := ff.full
  have := ff.faithful
  let Φ := J₁.mapDerivedCategory ⋙ P.rightDerivedFunctor
  let L := DerivedCategory.Q.{u + 2, u + 1, u + 2}.objPreimage K
  obtain ⟨c, hpt, hc⟩ := postnikov_homotopyLimit X A L
  have hs : IsIso (adj.counit.app (Φ.obj (DerivedCategory.Q.obj L))) := by
    rw [← hpt]
    apply support_of_homotopyLimit J₂.mapDerivedCategory G₂.mapDerivedCategory adj
      (Φ.mapCone c) (hc.map Φ)
    intro n
    have : (DerivedCategory.Q.obj (ProEt.postnikovTower L |>.obj
        (Opposite.op n))).IsGE (-(n : ℤ)) := by
      change (DerivedCategory.Q.obj (L.truncGE (-(n : ℤ)))).IsGE (-(n : ℤ))
      infer_instance
    exact bounded_support_square f j₁ j₂ r _comm A
      (DerivedCategory.Q.obj (ProEt.postnikovTower L |>.obj (Opposite.op n)))
      (-(n : ℤ))
  exact (NatTrans.isIso_app_iff_of_iso adj.counit
    (Φ.mapIso (DerivedCategory.Q.objObjPreimageIso K))).1 hs

end

end AlgebraicGeometry.Scheme.ProperOpenSquareSupport
