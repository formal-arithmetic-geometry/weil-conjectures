/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationSystemRealization
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClopenIdempotent
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
import all WeilConjectures.AlgebraicGeometry.ClopenCompositeCounit.ClopenCompositeCounitNormalization
import all WeilConjectures.AlgebraicGeometry.Compactification.CompactificationProjectionExchangeCoherence
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenPullTensorComposition
import WeilConjectures.CategoryTheory.SixFunctors.SystemProperOpenLambdaExchange
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.CategoryTheory.Tensor.TensorSquareMateTransfer
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus

/-!
# Normalized proper/open interchange commutes with projection

Source: Stacks Project, Tags 0F7B, 0F7C and 0F7D; the normalized proper/open
projection calculation in the blueprint (blueprint: lem-sf-proper-open-projection-mate).

The ordinary comparison is constructed from open base change and the canonical clopen
projection. The second statement uses the intrinsic comparison of the published system
realization, in the unbounded derived category of strict semilinear systems itself.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

/-- A finite commutative coefficient ring is noetherian.
Source: Stacks 00IU (blueprint: lem-sf-proper-open-projection-mate). -/
instance finiteRingIsNoetherian (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    IsNoetherianRing Λ :=
  @instIsNoetherianRingOfIsArtinianRing Λ _
    (isArtinian_of_finite : IsArtinianRing Λ)

/-- The ordinary unbounded derived category of constant `Λ`-module sheaves.
Source: Stacks 0F7B (blueprint: lem-sf-proper-open-projection-mate). -/
abbrev ProperOpenDerived (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :=
  DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))

/-- Derived inverse image on the ordinary pro-etale module categories.
Source: Stacks 0F7B (blueprint: lem-sf-proper-open-projection-mate). -/
abbrev ProperOpenPull (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ProperOpenDerived Λ Y ⥤ ProperOpenDerived Λ X :=
  (upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor

/-- Derived direct image on the ordinary pro-etale module categories.
Source: Stacks 0F7B (blueprint: lem-sf-proper-open-projection-mate). -/
abbrev ProperOpenPush (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ProperOpenDerived Λ X ⥤ ProperOpenDerived Λ Y :=
  (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor

/-- Exact extension by zero on the ordinary pro-etale derived categories.
Source: Stacks 0F7B (blueprint: lem-sf-proper-open-projection-mate). -/
abbrev ProperOpenShriek (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ProperOpenDerived Λ U ⥤ ProperOpenDerived Λ X :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory

/-- The derived tensor bifunctor on a pro-etale site.
Source: Stacks 0F7B (blueprint: lem-sf-proper-open-projection-mate). -/
abbrev ProperOpenTensor (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :=
  derivedTensor (ModuleCat.{u + 1} Λ) X

/-- Component of the published counit-defined projection, used by def-exchange-projection.
Source: Stacks 0E48 (blueprint: lem-sf-proper-open-projection-mate). -/
abbrev properOpenProjection (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : ProperOpenDerived Λ X)
    (N : ProperOpenDerived Λ Y) :=
  ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app M).app N

/-- The unit-normalized open tensor comparison.
Source: Stacks 0F7B (blueprint: lem-sf-proper-open-projection-mate). -/
noncomputable def properOpenTensorIso (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : ProperOpenDerived Λ U) (N : ProperOpenDerived Λ X) :
    ((ProperOpenTensor Λ X).obj ((ProperOpenShriek Λ j).obj M)).obj N ≅
      (ProperOpenShriek Λ j).obj
        (((ProperOpenTensor Λ U).obj M).obj ((ProperOpenPull Λ j).obj N)) :=
  (((derivedOpenImmersionLowerShriekProjectionIso
      (ModuleCat.{u + 1} Λ) j).app M).app N).symm

/-- The open adjunction, transported to the canonical total derived inverse image.
Source: Stacks 03DI (blueprint: lem-sf-proper-open-projection-mate). -/
def properOpenAdj (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ProperOpenShriek Λ j ⊣ ProperOpenPull Λ j :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).symm

/-- Canonical composition of open extensions, fixed by the pullback compositor and
adjunctions. Source: Stacks 03DI (blueprint: lem-sf-proper-open-projection-mate). -/
def properOpenShriekComp (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] :
    ProperOpenShriek Λ j ⋙ ProperOpenShriek Λ k ≅ ProperOpenShriek Λ (j ≫ k) :=
  Adjunction.leftAdjointCompIso (properOpenAdj Λ j) (properOpenAdj Λ k)
    (properOpenAdj Λ (j ≫ k))
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) j k).symm

/-- Equality transport of open extensions via the canonical pullback identification.
Source: Stacks 03DI (blueprint: lem-sf-proper-open-projection-mate). -/
def properOpenShriekCongr (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} {j k : U ⟶ X} [IsOpenImmersion j] [IsOpenImmersion k]
    (h : j = k) : ProperOpenShriek Λ j ≅ ProperOpenShriek Λ k :=
  ((properOpenAdj Λ j).ofNatIsoRight
    (leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) h)).leftAdjointUniq (properOpenAdj Λ k)

/-- The clopen projection: the direct-image unit followed by the canonical identification
of clopen direct image with extension by zero. It is identity on the image and zero on
its complement. Source: Stacks 09AE (blueprint: lem-sf-proper-open-projection-mate). -/
def properOpenClopenProjection (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (ProperOpenDerived Λ X) ⟶ ProperOpenPull Λ s ⋙ ProperOpenShriek Λ s :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).unit ≫
    Functor.whiskerLeft (ProperOpenPull Λ s)
      (rightDerivedLowerStarIsoOfIsClosedRange (ModuleCat.{u + 1} Λ) s
        s.isClosedEmbedding.isClosed_range).hom

/-- Ordinary canonical open base change, with total derived pullbacks.
Source: Stacks 09AE (blueprint: lem-sf-proper-open-projection-mate). -/
def properOpenBeta (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback a j' j g) :
    ProperOpenShriek Λ j ⋙ ProperOpenPull Λ g ≅
      ProperOpenPull Λ a ⋙ ProperOpenShriek Λ j' :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g) ≪≫
    ordinaryOpenExtensionBaseChangeIso Λ a j' j g sq ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) a).symm _

/-- The prescribed ordinary-site alpha: beta, then b_! of the clopen projection for
s=(k,r), then the canonical open/pullback compositors. No comparison is supplied as a
parameter. The lift and its clopenness are those of the recorded strict-tower calculus.
Source: Stacks 0F7B and node Step 1 (blueprint: lem-sf-proper-open-projection-mate). -/
def properOpenAlpha (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A B C D : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C) (p : B ⟶ D) (i : C ⟶ D)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    ProperOpenShriek Λ i ⋙ ProperOpenPull Λ p ⟶
      ProperOpenPull Λ r ⋙ ProperOpenShriek Λ k :=
  (properOpenBeta Λ (pullback.snd p i) (pullback.fst p i) i p
    (IsPullback.of_hasPullback p i).flip).hom ≫
  Functor.whiskerRight (Functor.whiskerLeft (ProperOpenPull Λ (pullback.snd p i))
    (properOpenClopenProjection Λ (StrictTower.squareLift k r p i h)))
      (ProperOpenShriek Λ (pullback.fst p i)) ≫
  Functor.whiskerRight
    (Functor.associator (ProperOpenPull Λ (pullback.snd p i))
      (ProperOpenPull Λ (StrictTower.squareLift k r p i h))
      (ProperOpenShriek Λ (StrictTower.squareLift k r p i h))).inv
    (ProperOpenShriek Λ (pullback.fst p i)) ≫
  (Functor.associator
    (ProperOpenPull Λ (pullback.snd p i) ⋙ ProperOpenPull Λ (StrictTower.squareLift k r p i h))
    (ProperOpenShriek Λ (StrictTower.squareLift k r p i h))
    (ProperOpenShriek Λ (pullback.fst p i))).hom ≫
  Functor.whiskerLeft
    (ProperOpenPull Λ (pullback.snd p i) ⋙ ProperOpenPull Λ (StrictTower.squareLift k r p i h))
    ((properOpenShriekComp Λ (StrictTower.squareLift k r p i h) (pullback.fst p i)).hom ≫
      (properOpenShriekCongr Λ (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ)
      (StrictTower.squareLift k r p i h) (pullback.snd p i)).inv ≫
      (leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) (pullback.lift_snd k r h)).hom)
    (ProperOpenShriek Λ k)

/-- The proper-adjunction mate of the canonical clopen-projection alpha.
Source: Stacks 0F7B (blueprint: lem-sf-proper-open-projection-mate). -/
def properOpenMate (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A B C D : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C) (p : B ⟶ D) (i : C ⟶ D)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    ProperOpenPush Λ r ⋙ ProperOpenShriek Λ i ⟶
      ProperOpenShriek Λ k ⋙ ProperOpenPush Λ p :=
  mateEquiv
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p)
    (TwoSquare.mk _ _ _ _ (properOpenAlpha Λ k r p i h))

/-- Tensoring the mate component with the identity on the second variable, with the
definitional functor-composition casts made explicit.
Source: node Step 5 (blueprint: lem-sf-proper-open-projection-mate). -/
noncomputable def properOpenMateTensorMap
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A B C D : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C)
    (p : B ⟶ D) (i : C ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (M : ProperOpenDerived Λ A) (N : ProperOpenDerived Λ D) :
    ((ProperOpenTensor Λ D).obj ((ProperOpenShriek Λ i).obj ((ProperOpenPush Λ r).obj M))).obj N ⟶
      ((ProperOpenTensor Λ D).obj
        ((ProperOpenPush Λ p).obj ((ProperOpenShriek Λ k).obj M))).obj N :=
  eqToHom (by rfl) ≫
      ((ProperOpenTensor Λ D).map ((properOpenMate Λ k r p i h).app M)).app N ≫
    eqToHom (by rfl)

/-- The canonical derived pullback comparison attached to the commutative square.
Source: Stacks 0F7B (blueprint: lem-sf-proper-open-projection-mate). -/
noncomputable def properOpenPullSquareIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A B C D : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C)
    (p : B ⟶ D) (i : C ⟶ D) (_h : k ≫ p = r ≫ i) :
    ProperOpenPull Λ i ⋙ ProperOpenPull Λ r ≅
      ProperOpenPull Λ p ⋙ ProperOpenPull Λ k :=
  leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) (CommSq.mk _h)

section ProofHelpers

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint

attribute [local instance 30000] isNoetherian_of_finite
  AlgebraicGeometry.ProEtale.preservesHomology_upperStar
  AlgebraicGeometry.ProEtale.preservesFiniteLimits_upperStar
  AlgebraicGeometry.ProEtale.additive_upperStar
  AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf
  CategoryTheory.GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.hasDerivedMonoidalCategory
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
  Adjunction.derivedAdjunction

section MateTransfer
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A : Type*} [Category A] {B : Type*} [Category B]
  {C : Type*} [Category C] {D : Type*} [Category D]

private theorem forward_mate_transfer
    (Pr : C ⥤ A) (Rr : A ⥤ C) (Pp : D ⥤ B) (Rp : B ⥤ D)
    (ar : Pr ⊣ Rr) (ap : Pp ⊣ Rp) (Pi : D ⥤ C) (Pk : B ⥤ A)
    (J : C ⥤ D) (K : A ⥤ B) (theta : Pi ⋙ Pr ≅ Pp ⋙ Pk)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (muR : TC ⋙ Pr ⟶ (Pr.prod Pr) ⋙ TA)
    (muP : TD ⋙ Pp ⟶ (Pp.prod Pp) ⋙ TB)
    (di : (J.prod (𝟭 D)) ⋙ TD ⟶ ((𝟭 C).prod Pi) ⋙ TC ⋙ J)
    (dk : (K.prod (𝟭 B)) ⋙ TB ⟶ ((𝟭 A).prod Pk) ⋙ TA ⋙ K)
    (a : J ⋙ Pp ⟶ Pr ⋙ K)
    (square : ∀ (H : C) (N : D),
      Pp.map (di.app (H, N)) ≫ a.app (TC.obj (H, Pi.obj N)) ≫
        K.map (muR.app (H, Pi.obj N)) ≫
        K.map (TA.map (Prod.mkHom (𝟙 (Pr.obj H)) (theta.hom.app N))) =
      muP.app (J.obj H, N) ≫
        TB.map (Prod.mkHom (a.app H) (𝟙 (Pp.obj N))) ≫ dk.app (Pr.obj H, Pp.obj N))
    (M : A) (N : D) :
    di.app (Rr.obj M, N) ≫
      J.map (tensorSquareProjectionMap Pr Rr ar TC TA muR M (Pi.obj N)) ≫
      J.map (Rr.map (TA.map (Prod.mkHom (𝟙 M) (theta.hom.app N)))) ≫
      (mateEquiv ar ap (TwoSquare.mk J Pr Pp K a)).natTrans.app
        (TA.obj (M, Pk.obj (Pp.obj N))) =
    TD.map (Prod.mkHom ((mateEquiv ar ap (TwoSquare.mk J Pr Pp K a)).natTrans.app M) (𝟙 N)) ≫
      tensorSquareProjectionMap Pp Rp ap TD TB muP (K.obj M) N ≫
      Rp.map (dk.app (M, Pp.obj N)) := by
  obtain ⟨t, ht⟩ := tensorSquare_mate_transfer Pr Rr Pp Rp ar ap Pi Pk J K theta
    TA TB TC TD muR muP di dk a square
  have h := (ht M N).1.symm.trans (ht M N).2.1
  have hh := congrArg (fun f ↦ f ≫
    Rp.map (K.map (TA.map (Prod.mkHom (𝟙 M) (theta.hom.app N))))) h
  dsimp only [tensorSquareMateFirst, tensorSquareMateSecond] at hh
  simp only [Functor.map_comp, Category.assoc] at hh
  have hg := (mateEquiv ar ap (TwoSquare.mk J Pr Pp K a)).natTrans.naturality
    (TA.map (Prod.mkHom (𝟙 M) (theta.hom.app N)))
  dsimp only [Functor.comp_map] at hg
  erw [← hg] at hh
  have hc : TA.map (Prod.mkHom (𝟙 M) (theta.inv.app N)) ≫
      TA.map (Prod.mkHom (𝟙 M) (theta.hom.app N)) = 𝟙 _ := by
    rw [← TA.map_comp]
    have hp : Prod.mkHom (𝟙 M) (theta.inv.app N) ≫
        Prod.mkHom (𝟙 M) (theta.hom.app N) = 𝟙 (M, Pk.obj (Pp.obj N)) := by
      ext <;> simp
    erw [hp, TA.map_id]
  erw [← Rp.map_comp, ← K.map_comp, hc, K.map_id, Rp.map_id, Category.comp_id] at hh
  exact hh

end MateTransfer

private theorem properOpenBeta_eq
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback a j' j g) :
    properOpenBeta Λ a j' j g sq =
      (leftDerivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) sq).symm := by
  let := isIso_baseChangeMap_of_isPullback (ModuleCat.{u + 1} Λ) sq
  unfold properOpenBeta ordinaryOpenExtensionBaseChangeIso
    leftDerivedOpenImmersionLowerShriekBaseChangeIso
    derivedOpenImmersionLowerShriekBaseChangeIso
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Functor.isoWhiskerLeft_symm,
    Functor.isoWhiskerRight_symm, Iso.trans_assoc]
  have he : (conjugateIsoEquiv
      ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g))
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).comp
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j'))).symm
      (asIso (baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq)) =
        openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) sq := by
    apply Iso.ext
    rfl
  rw [he]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapDerivedCategoryNatIso_symm]

private theorem properOpenBeta_tensor
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback a j' j g) (H : ProperOpenDerived Λ U)
    (N : ProperOpenDerived Λ X) :
    (ProperOpenPull Λ g).map (properOpenTensorIso Λ j H N).hom ≫
        (properOpenBeta Λ a j' j g sq).hom.app
          (((ProperOpenTensor Λ U).obj H).obj ((ProperOpenPull Λ j).obj N)) ≫
        (ProperOpenShriek Λ j').map
          (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) a).app H).app
            ((ProperOpenPull Λ j).obj N)) ≫
        (ProperOpenShriek Λ j').map
          (((ProperOpenTensor Λ U').obj ((ProperOpenPull Λ a).obj H)).map
            ((leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq.toCommSq).inv.app N)) =
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) g).app
        ((ProperOpenShriek Λ j).obj H)).app N ≫
        ((ProperOpenTensor Λ X').map ((properOpenBeta Λ a j' j g sq).hom.app H)).app
          ((ProperOpenPull Λ g).obj N) ≫
        (properOpenTensorIso Λ j' ((ProperOpenPull Λ a).obj H)
          ((ProperOpenPull Λ g).obj N)).hom := by
  have ht := derivedOpenImmersionLowerShriekProjectionIso_inv_baseChange
    (ModuleCat.{u + 1} Λ) sq H N
  rw [properOpenBeta_eq]
  dsimp only [properOpenTensorIso]
  apply (cancel_epi (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g
    ((ProperOpenShriek Λ j).obj H) N).inv).1
  simp only [← leftDerivedUpperStarTensorIso_hom]
  rw [Iso.inv_hom_id_assoc]
  erw [reassoc_of% ht]
  simp only [← Functor.map_comp]
  dsimp only [ProperOpenPull, ProperOpenShriek, ProperOpenTensor]
  simp only [Iso.inv_hom_id_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

private theorem properOpenTensorIso_inv_transpose
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : ProperOpenDerived Λ U) (N : ProperOpenDerived Λ X) :
    (properOpenAdj Λ j).homEquiv _ _ (properOpenTensorIso Λ j M N).inv =
      ((ProperOpenTensor Λ U).map ((properOpenAdj Λ j).unit.app M)).app
          ((ProperOpenPull Λ j).obj N) ≫
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) j
          ((ProperOpenShriek Λ j).obj M) N).inv := by
  have he : (properOpenTensorIso Λ j M N).inv =
      (((derivedOpenImmersionLowerShriekProjectionIso
        (ModuleCat.{u + 1} Λ) j).hom.app M).app N) := rfl
  rw [he]
  rw [derivedOpenImmersionLowerShriekProjectionIso_hom]
  unfold properOpenAdj derivedOpenImmersionLowerShriekProjectionMap
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.projectionMap_app_app]
  erw [Equiv.apply_symm_apply]
  simp only [Adjunction.projectionMapTranspose_app_app,
    mapDerivedCategoryUpperStarDerivedTensorIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Adjunction.ofNatIsoRight_unit,
    Functor.whiskerLeft_app]
  change _ ≫
      ((ProperOpenTensor Λ U).map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).inv.app
          ((ProperOpenShriek Λ j).obj M))).app ((ProperOpenPull Λ j).obj N) ≫
      ((leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} Λ) j).inv.app
        ((ProperOpenShriek Λ j).obj M)).app N ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).hom.app _ ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).inv.app _ = _
  rw [Iso.hom_inv_id_app]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  erw [Category.comp_id]
  rfl

private def uncurryPostIso
    {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]
    (T : C ⥤ D ⥤ E) (F : E ⥤ B) :
    Functor.uncurry.obj T ⋙ F ≅
      Functor.uncurry.obj ((Functor.postcompose₂.obj F).obj T) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N k
    simp [Functor.uncurry, Functor.map_comp])

private def uncurryPreIso
    {C D E B A : Type*} [Category C] [Category D] [Category E] [Category B] [Category A]
    (T : D ⥤ E ⥤ B) (F : C ⥤ D) (G : A ⥤ E) :
    (F.prod G) ⋙ Functor.uncurry.obj T ≅
      Functor.uncurry.obj ((((Functor.whiskeringLeft₂ B).obj F).obj G).obj T) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro M N k; simp [Functor.uncurry])

private def properOpenMuRaw
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (f : U ⟶ X) :
    Functor.uncurry.obj (ProperOpenTensor Λ X) ⋙ ProperOpenPull Λ f ≅
      ((ProperOpenPull Λ f).prod (ProperOpenPull Λ f)) ⋙
        Functor.uncurry.obj (ProperOpenTensor Λ U) :=
  uncurryPostIso (ProperOpenTensor Λ X) (ProperOpenPull Λ f) ≪≫
    Functor.uncurry.mapIso (leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} Λ) f) ≪≫
      (uncurryPreIso (ProperOpenTensor Λ U) (ProperOpenPull Λ f)
        (ProperOpenPull Λ f)).symm

private def properOpenDeltaRaw
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ((ProperOpenShriek Λ j).prod (𝟭 _)) ⋙ Functor.uncurry.obj (ProperOpenTensor Λ X) ≅
      ((𝟭 _).prod (ProperOpenPull Λ j)) ⋙ Functor.uncurry.obj (ProperOpenTensor Λ U) ⋙
        ProperOpenShriek Λ j :=
  uncurryPreIso (ProperOpenTensor Λ X) (ProperOpenShriek Λ j) (𝟭 _) ≪≫
    Functor.uncurry.mapIso
      (derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} Λ) j).symm ≪≫
    (uncurryPostIso _ (ProperOpenShriek Λ j)).symm ≪≫
    Functor.isoWhiskerRight
      (uncurryPreIso (ProperOpenTensor Λ U) (𝟭 _) (ProperOpenPull Λ j)).symm _

private theorem properOpenMuRaw_hom
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (f : U ⟶ X) (M N : ProperOpenDerived Λ X) :
    (properOpenMuRaw Λ f).hom.app (M, N) =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) f M N).hom := by
  simp only [properOpenMuRaw, Iso.trans_hom, Iso.symm_hom, uncurryPostIso, uncurryPreIso,
    NatTrans.comp_app, Functor.mapIso_hom, Functor.uncurry_map_app,
    NatIso.ofComponents, Iso.refl_hom, Iso.refl_inv, Category.id_comp]
  erw [Category.comp_id]
  rfl

private theorem properOpenDeltaRaw_hom
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : ProperOpenDerived Λ U) (N : ProperOpenDerived Λ X) :
    (properOpenDeltaRaw Λ j).hom.app (M, N) = (properOpenTensorIso Λ j M N).hom := by
  simp only [properOpenDeltaRaw, Iso.trans_hom, Iso.symm_hom, uncurryPostIso, uncurryPreIso,
    NatTrans.comp_app, Functor.mapIso_hom, Functor.uncurry_map_app,
    NatIso.ofComponents, Iso.refl_hom, Iso.refl_inv, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.id_comp, properOpenTensorIso]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
  rfl

private def properOpenMu
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (f : U ⟶ X) :
    Functor.uncurry.obj (ProperOpenTensor Λ X) ⋙ ProperOpenPull Λ f ≅
      ((ProperOpenPull Λ f).prod (ProperOpenPull Λ f)) ⋙
        Functor.uncurry.obj (ProperOpenTensor Λ U) :=
  NatIso.ofComponents
    (fun M ↦ leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) f M.1 M.2) (by
      intro M N h
      rcases M with ⟨M₁, M₂⟩
      rcases N with ⟨N₁, N₂⟩
      simpa only [properOpenMuRaw_hom] using (properOpenMuRaw Λ f).hom.naturality h)

private def properOpenDelta
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ((ProperOpenShriek Λ j).prod (𝟭 _)) ⋙ Functor.uncurry.obj (ProperOpenTensor Λ X) ≅
      ((𝟭 _).prod (ProperOpenPull Λ j)) ⋙ Functor.uncurry.obj (ProperOpenTensor Λ U) ⋙
        ProperOpenShriek Λ j :=
  NatIso.ofComponents (fun M ↦ properOpenTensorIso Λ j M.1 M.2) (by
    intro M N h
    rcases M with ⟨M₁, M₂⟩
    rcases N with ⟨N₁, N₂⟩
    simpa only [properOpenDeltaRaw_hom] using (properOpenDeltaRaw Λ j).hom.naturality h)

attribute [local irreducible] properOpenMu properOpenDelta

private theorem properOpenMu_hom
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (f : U ⟶ X) (M N : ProperOpenDerived Λ X) :
    (properOpenMu Λ f).hom.app (M, N) =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) f M N).hom := by
  unfold properOpenMu
  rfl

private theorem properOpenMu_inv
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (f : U ⟶ X) (M N : ProperOpenDerived Λ X) :
    (properOpenMu Λ f).inv.app (M, N) =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) f M N).inv := by
  unfold properOpenMu
  rfl

private theorem properOpenDelta_hom
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : ProperOpenDerived Λ U) (N : ProperOpenDerived Λ X) :
    (properOpenDelta Λ j).hom.app (M, N) = (properOpenTensorIso Λ j M N).hom := by
  unfold properOpenDelta
  rfl

private theorem properOpenDelta_inv
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : ProperOpenDerived Λ U) (N : ProperOpenDerived Λ X) :
    (properOpenDelta Λ j).inv.app (M, N) = (properOpenTensorIso Λ j M N).inv := by
  unfold properOpenDelta
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem projection_uncurry
    {A C : Type*} [Category A] [Category C]
    (P : C ⥤ A) (R : A ⥤ C) (adj : P ⊣ R)
    (TA : A ⥤ A ⥤ A) (TC : C ⥤ C ⥤ C)
    (mu : Functor.uncurry.obj TC ⋙ P ⟶ P.prod P ⋙ Functor.uncurry.obj TA)
    (phi : (Functor.postcompose₂.obj P).obj TC ⟶
      (((Functor.whiskeringLeft₂ A).obj P).obj P).obj TA)
    (hmu : ∀ (M N : C), mu.app (M, N) = (phi.app M).app N)
    (M : A) (N : C) :
    tensorSquareProjectionMap P R adj (Functor.uncurry.obj TC)
      (Functor.uncurry.obj TA) mu M N =
      ((adj.rightAdjointProjectionMap phi).app M).app N := by
  unfold tensorSquareProjectionMap
  simp only [Adjunction.rightAdjointProjectionMap_app_app]
  apply congrArg (adj.homEquiv _ _)
  simp only [NatTrans.comp_app, Functor.curry_map_app_app,
    Functor.curryObjProdComp_hom_app_app, hmu]
  dsimp only [Functor.curry, Functor.curryObj, Functor.uncurry, Functor.id_obj]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  erw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem properOpenProjection_tensorSquare
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : ProperOpenDerived Λ X) (N : ProperOpenDerived Λ Y) :
    tensorSquareProjectionMap (ProperOpenPull Λ f) (ProperOpenPush Λ f)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
      (Functor.uncurry.obj (ProperOpenTensor Λ Y))
      (Functor.uncurry.obj (ProperOpenTensor Λ X)) (properOpenMu Λ f).hom M N =
      properOpenProjection Λ f M N := by
  unfold properOpenProjection
  erw [rightDerivedLowerStarProjectionMap_app_app]
  apply projection_uncurry
  intro U V
  rw [properOpenMu_hom, leftDerivedUpperStarTensorIso_hom]

private def tensorComparisonComp
    {C D E : Type*} [Category C] [Category D] [Category E]
    (S : D ⥤ C) (R : E ⥤ D)
    (U : C × C ⥤ C) (T : D × D ⥤ D) (V : E × E ⥤ E)
    (muS : T ⋙ S ≅ (S.prod S) ⋙ U) (muR : V ⋙ R ≅ (R.prod R) ⋙ T) :
    V ⋙ (R ⋙ S) ≅ ((R ⋙ S).prod (R ⋙ S)) ⋙ U :=
  NatIso.ofComponents (fun X ↦ S.mapIso (muR.app X) ≪≫ muS.app (R.obj X.1, R.obj X.2))
    (by
      intro X Y f
      have hR := muR.hom.naturality f
      have hS := muS.hom.naturality (Prod.mkHom (R.map f.1) (R.map f.2))
      dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj] at hR hS ⊢
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
      rw [← S.map_comp_assoc, hR, S.map_comp, Category.assoc, hS])

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def openTensorComp
    {C D E : Type w} [Category.{v} C] [Category.{v} D] [Category.{v} E]
    (L : C ⥤ D) (S : D ⥤ C) (B : D ⥤ E) (R : E ⥤ D)
    (U : C × C ⥤ C) (T : D × D ⥤ D) (V : E × E ⥤ E)
    (deltaS : (L.prod (𝟭 D)) ⋙ T ≅ (𝟭 C).prod S ⋙ U ⋙ L)
    (deltaR : (B.prod (𝟭 E)) ⋙ V ≅ (𝟭 D).prod R ⋙ T ⋙ B) :
    ((L ⋙ B).prod (𝟭 E)) ⋙ V ≅ (𝟭 C).prod (R ⋙ S) ⋙ U ⋙ (L ⋙ B) :=
  NatIso.ofComponents
    (F := ((L ⋙ B).prod (𝟭 E)) ⋙ V)
    (G := (𝟭 C).prod (R ⋙ S) ⋙ U ⋙ (L ⋙ B))
    (fun (X : C × E) ↦ deltaR.app (L.obj X.1, X.2) ≪≫
      B.mapIso (deltaS.app (X.1, R.obj X.2)))
    (by
      intro X Y f
      have hR := deltaR.hom.naturality (Prod.mkHom (L.map f.1) f.2)
      have hS := deltaS.hom.naturality (Prod.mkHom f.1 (R.map f.2))
      dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj,
        Functor.id_map, Functor.id_obj] at hR hS ⊢
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
      rw [reassoc_of% hR, ← B.map_comp]
      rw [hS, B.map_comp])

attribute [local simp] Functor.isoWhiskerLeft_hom Functor.isoWhiskerRight_hom
  Functor.isoWhiskerLeft_inv Functor.isoWhiskerRight_inv

private theorem genericPull_comp_tensor
    (V₀ : Type*) [Category.{u + 1} V₀] [Abelian V₀]
    [IsGrothendieckAbelian.{u + 1} V₀] [MonoidalCategory V₀]
    [MonoidalPreadditive V₀] [SymmetricCategory V₀] [MonoidalClosed V₀]
    [Abelian.HasFunctorialFlatResolution V₀] [UpperStarPreservesFlat V₀]
    {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X)
    (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) V₀)) :
    (leftDerivedUpperStarComp (V₀) s b).hom.app
        (((derivedTensor V₀ X).obj M).obj N) ≫
      ((upperStar V₀ s).leftDerivedFunctor).map (leftDerivedUpperStarTensorIso
        (V₀) b M N).hom ≫
      (leftDerivedUpperStarTensorIso (V₀) s
        (((upperStar V₀ b).leftDerivedFunctor).obj M)
        (((upperStar V₀ b).leftDerivedFunctor).obj N)).hom =
    (leftDerivedUpperStarTensorIso (V₀) (s ≫ b) M N).hom ≫
      (Functor.uncurry.obj (derivedTensor V₀ U)).map
        (Prod.mkHom
          ((leftDerivedUpperStarComp (V₀) s b).hom.app M)
          ((leftDerivedUpperStarComp (V₀) s b).hom.app N)) := by
  exact properOpenPullTensorComposition V₀ s b M N

private theorem properOpenPull_comp_tensor
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X)
    (M N : ProperOpenDerived Λ X) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s b).hom.app
        (((ProperOpenTensor Λ X).obj M).obj N) ≫
      (ProperOpenPull Λ s).map (leftDerivedUpperStarTensorIso
        (ModuleCat.{u + 1} Λ) b M N).hom ≫
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) s
        ((ProperOpenPull Λ b).obj M) ((ProperOpenPull Λ b).obj N)).hom =
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) (s ≫ b) M N).hom ≫
      (Functor.uncurry.obj (ProperOpenTensor Λ U)).map
        (Prod.mkHom
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s b).hom.app M)
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s b).hom.app N)) := by
  exact genericPull_comp_tensor (ModuleCat.{u + 1} Λ) s b M N

private theorem open_tensor_composite_transpose
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) (S : D ⥤ C) (B : D ⥤ E) (R : E ⥤ D)
    (a : L ⊣ S) (b : B ⊣ R)
    (U : C × C ⥤ C) (T : D × D ⥤ D) (V : E × E ⥤ E)
    (muS : T ⋙ S ≅ (S.prod S) ⋙ U) (muR : V ⋙ R ≅ (R.prod R) ⋙ T)
    (deltaS : (L.prod (𝟭 D)) ⋙ T ≅ (𝟭 C).prod S ⋙ U ⋙ L)
    (deltaR : (B.prod (𝟭 E)) ⋙ V ≅ (𝟭 D).prod R ⋙ T ⋙ B)
    (hS : ∀ (M : C) (N : D), a.homEquiv _ _ (deltaS.inv.app (M, N)) =
      U.map (Prod.mkHom (a.unit.app M) (𝟙 _)) ≫ muS.inv.app (L.obj M, N))
    (hR : ∀ (M : D) (N : E), b.homEquiv _ _ (deltaR.inv.app (M, N)) =
      T.map (Prod.mkHom (b.unit.app M) (𝟙 _)) ≫ muR.inv.app (B.obj M, N))
    (M : C) (N : E) :
    (a.comp b).homEquiv _ _
        (B.map (deltaS.inv.app (M, R.obj N)) ≫ deltaR.inv.app (L.obj M, N)) =
      U.map (Prod.mkHom ((a.comp b).unit.app M) (𝟙 (S.obj (R.obj N)))) ≫
        muS.inv.app (R.obj (B.obj (L.obj M)), R.obj N) ≫
          S.map (muR.inv.app (B.obj (L.obj M), N)) := by
  rw [Adjunction.comp_homEquiv]
  change a.homEquiv _ _ (b.homEquiv _ _ _) = _
  rw [b.homEquiv_naturality_left]
  erw [hR]
  rw [a.homEquiv_naturality_right]
  erw [hS]
  rw [Functor.map_comp]
  have hn := muS.inv.naturality (Prod.mkHom (b.unit.app (L.obj M)) (𝟙 (R.obj N)))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj] at hn
  simp only [Category.assoc]
  slice_lhs 2 3 => erw [← hn]
  simp only [Category.assoc]
  rw [← U.map_comp_assoc]
  congr 2
  ext
  · exact (Adjunction.comp_unit_app a b M).symm
  · simp

private theorem open_tensor_transport
    {C D : Type*} [Category C] [Category D]
    (L L' : C ⥤ D) (S S' : D ⥤ C) (a : L ⊣ S) (b : L' ⊣ S')
    (T : D × D ⥤ D) (U : C × C ⥤ C)
    (mu : T ⋙ S ≅ (S.prod S) ⋙ U) (mu' : T ⋙ S' ≅ (S'.prod S') ⋙ U)
    (delta : (L.prod (𝟭 D)) ⋙ T ≅ (𝟭 C).prod S ⋙ U ⋙ L)
    (delta' : (L'.prod (𝟭 D)) ⋙ T ≅ (𝟭 C).prod S' ⋙ U ⋙ L')
    (e : L ≅ L') (c : S ≅ S')
    (he : ∀ M : C, a.unit.app M ≫ c.hom.app (L.obj M) =
      b.unit.app M ≫ S'.map (e.inv.app M))
    (hc : ∀ F V : D, mu.inv.app (F, V) ≫ c.hom.app (T.obj (F, V)) =
      U.map (Prod.mkHom (c.hom.app F) (c.hom.app V)) ≫ mu'.inv.app (F, V))
    (hd : ∀ (M : C) (N : D), a.homEquiv _ _ (delta.inv.app (M, N)) =
      U.map (Prod.mkHom (a.unit.app M) (𝟙 _)) ≫ mu.inv.app (L.obj M, N))
    (hd' : ∀ (M : C) (N : D), b.homEquiv _ _ (delta'.inv.app (M, N)) =
      U.map (Prod.mkHom (b.unit.app M) (𝟙 _)) ≫ mu'.inv.app (L'.obj M, N))
    (M : C) (N : D) :
    delta.hom.app (M, N) ≫ e.hom.app (U.obj (M, S.obj N)) ≫
        L'.map (U.map (Prod.mkHom (𝟙 M) (c.hom.app N))) =
      T.map (Prod.mkHom (e.hom.app M) (𝟙 N)) ≫ delta'.hom.app (M, N) := by
  let x := delta.app (M, N) ≪≫ e.app _ ≪≫
    L'.mapIso (U.mapIso ((Iso.refl M).prod (c.app N)))
  let y := T.mapIso ((e.app M).prod (Iso.refl N)) ≪≫ delta'.app (M, N)
  have hi : x.inv = y.inv := by
    apply (b.homEquiv _ _).injective
    dsimp only [x, y, Iso.trans_inv, Functor.mapIso_inv, Iso.prod_inv, Iso.refl_inv,
      Iso.app_inv]
    simp only [Category.assoc]
    rw [b.homEquiv_naturality_left]
    conv_rhs => rw [b.homEquiv_naturality_right]
    erw [hd']
    have he' := he (U.obj (M, S.obj N))
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
    erw [← reassoc_of% he']
    rw [← c.hom.naturality]
    simp only [Iso.prod, Iso.refl_inv, Iso.app_inv]
    have hda := hd M N
    simp only [Adjunction.homEquiv_unit] at hda
    dsimp only [Functor.prod_obj, Functor.id_obj] at hda
    rw [reassoc_of% hda]
    dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj]
    rw [hc]
    have hm := mu'.inv.naturality (Prod.mkHom (e.inv.app M) (𝟙 N))
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj] at hm
    rw [← hm]
    simp only [← U.map_comp_assoc]
    congr 2
    ext
    · simpa using he M
    · simp
  have hi' : x.symm = y.symm := Iso.ext hi
  exact congrArg (fun z ↦ z.inv) hi'

private theorem tensor_square_clopen_factors
    {A B C D E : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E]
    (Pi : D ⥤ C) (Pp : D ⥤ B) (Pq : C ⥤ E) (Pb : B ⥤ E)
    (S : E ⥤ A) (L : A ⥤ E) (K : E ⥤ B) (J : C ⥤ D)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TC : C × C ⥤ C)
    (TD : D × D ⥤ D) (TE : E × E ⥤ E)
    (muP : TD ⋙ Pp ⟶ (Pp.prod Pp) ⋙ TB)
    (muQ : TC ⋙ Pq ⟶ (Pq.prod Pq) ⋙ TE)
    (muS : TE ⋙ S ⟶ (S.prod S) ⋙ TA)
    (deltaJ : (J.prod (𝟭 D)) ⋙ TD ⟶ (𝟭 C).prod Pi ⋙ TC ⋙ J)
    (deltaK : (K.prod (𝟭 B)) ⋙ TB ⟶ (𝟭 E).prod Pb ⋙ TE ⋙ K)
    (deltaS : (L.prod (𝟭 E)) ⋙ TE ⟶ (𝟭 A).prod S ⋙ TA ⋙ L)
    (beta : J ⋙ Pp ⟶ Pq ⋙ K) (theta : Pp ⋙ Pb ≅ Pi ⋙ Pq)
    (rho : 𝟭 E ⟶ S ⋙ L)
    (hcart : ∀ (H : C) (N : D),
      Pp.map (deltaJ.app (H, N)) ≫ beta.app (TC.obj (H, Pi.obj N)) ≫
        K.map (muQ.app (H, Pi.obj N)) ≫
        K.map (TE.map (Prod.mkHom (𝟙 _) (theta.inv.app N))) =
      muP.app (J.obj H, N) ≫ TB.map (Prod.mkHom (beta.app H) (𝟙 _)) ≫
        deltaK.app (Pq.obj H, Pp.obj N))
    (hclopen : ∀ (F V : E), rho.app (TE.obj (F, V)) ≫ L.map (muS.app (F, V)) =
      TE.map (Prod.mkHom (rho.app F) (𝟙 V)) ≫ deltaS.app (S.obj F, V))
    (H : C) (N : D) :
    Pp.map (deltaJ.app (H, N)) ≫ beta.app (TC.obj (H, Pi.obj N)) ≫
      K.map (rho.app (Pq.obj (TC.obj (H, Pi.obj N)))) ≫
      K.map (L.map (S.map (muQ.app (H, Pi.obj N)))) ≫
      K.map (L.map (muS.app (Pq.obj H, Pq.obj (Pi.obj N)))) ≫
      K.map (L.map (TA.map (Prod.mkHom (𝟙 _) (S.map (theta.inv.app N))))) =
    muP.app (J.obj H, N) ≫
      TB.map (Prod.mkHom (beta.app H ≫ K.map (rho.app (Pq.obj H))) (𝟙 _)) ≫
      deltaK.app (L.obj (S.obj (Pq.obj H)), Pp.obj N) ≫
      K.map (deltaS.app (S.obj (Pq.obj H), Pb.obj (Pp.obj N))) := by
  have hr := rho.naturality (muQ.app (H, Pi.obj N))
  have hs := deltaS.naturality
    (Prod.mkHom (𝟙 (S.obj (Pq.obj H))) (theta.inv.app N))
  have hk := deltaK.naturality (Prod.mkHom (rho.app (Pq.obj H)) (𝟙 (Pp.obj N)))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map, Functor.comp_obj,
    Functor.prod_obj, Functor.id_obj] at hr hs hk
  slice_lhs 3 4 => rw [← K.map_comp, ← hr, K.map_comp]
  slice_lhs 4 5 => rw [← K.map_comp, hclopen, K.map_comp]
  have ht : Prod.mkHom (beta.app H ≫ K.map (rho.app (Pq.obj H))) (𝟙 (Pp.obj N)) =
      Prod.mkHom (beta.app H) (𝟙 (Pp.obj N)) ≫
        Prod.mkHom (K.map (rho.app (Pq.obj H))) (𝟙 (Pp.obj N)) := by
    ext <;> simp
  rw [ht, TB.map_comp]
  simp only [Category.assoc]
  slice_rhs 3 4 => exact hk
  slice_lhs 5 6 => rw [← K.map_comp, ← hs, K.map_comp]
  have hp :
      Prod.mkHom (rho.app (Pq.obj H)) (𝟙 (Pq.obj (Pi.obj N))) ≫
        Prod.mkHom (L.map (𝟙 (S.obj (Pq.obj H)))) (theta.inv.app N) =
      Prod.mkHom (𝟙 (Pq.obj H)) (theta.inv.app N) ≫
        Prod.mkHom (rho.app (Pq.obj H)) (Pb.map (𝟙 (Pp.obj N))) := by
    ext <;> simp
  slice_lhs 4 5 => rw [← K.map_comp, ← TE.map_comp, hp, TE.map_comp, K.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hcart H N]

private theorem tensor_square_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (Pi : D ⥤ C) (Pp : D ⥤ B) (Pr₀ Pr : C ⥤ A) (Pk₀ Pk : B ⥤ A)
    (J : C ⥤ D) (K₀ K : A ⥤ B)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (muP : TD ⋙ Pp ⟶ (Pp.prod Pp) ⋙ TB)
    (mu₀ : TC ⋙ Pr₀ ⟶ (Pr₀.prod Pr₀) ⋙ TA)
    (muR : TC ⋙ Pr ⟶ (Pr.prod Pr) ⋙ TA)
    (di : (J.prod (𝟭 D)) ⋙ TD ⟶ (𝟭 C).prod Pi ⋙ TC ⋙ J)
    (dk₀ : (K₀.prod (𝟭 B)) ⋙ TB ⟶ (𝟭 A).prod Pk₀ ⋙ TA ⋙ K₀)
    (dk : (K.prod (𝟭 B)) ⋙ TB ⟶ (𝟭 A).prod Pk ⋙ TA ⋙ K)
    (alpha₀ : J ⋙ Pp ⟶ Pr₀ ⋙ K₀)
    (theta₀ : Pi ⋙ Pr₀ ≅ Pp ⋙ Pk₀) (theta : Pi ⋙ Pr ≅ Pp ⋙ Pk)
    (e : K₀ ≅ K) (t : Pr₀ ≅ Pr) (c : Pk₀ ≅ Pk)
    (hmu : ∀ H V, t.hom.app (TC.obj (H, V)) ≫ muR.app (H, V) =
      mu₀.app (H, V) ≫ TA.map (Prod.mkHom (t.hom.app H) (t.hom.app V)))
    (htheta : ∀ N, t.hom.app (Pi.obj N) ≫ theta.hom.app N =
      theta₀.hom.app N ≫ c.hom.app (Pp.obj N))
    (hdelta : ∀ M N, dk₀.app (M, N) ≫ e.hom.app (TA.obj (M, Pk₀.obj N)) ≫
      K.map (TA.map (Prod.mkHom (𝟙 M) (c.hom.app N))) =
      TB.map (Prod.mkHom (e.hom.app M) (𝟙 N)) ≫ dk.app (M, N))
    (hsquare : ∀ H N, Pp.map (di.app (H, N)) ≫ alpha₀.app (TC.obj (H, Pi.obj N)) ≫
      K₀.map (mu₀.app (H, Pi.obj N)) ≫
      K₀.map (TA.map (Prod.mkHom (𝟙 _) (theta₀.hom.app N))) =
      muP.app (J.obj H, N) ≫ TB.map (Prod.mkHom (alpha₀.app H) (𝟙 _)) ≫
      dk₀.app (Pr₀.obj H, Pp.obj N))
    (H : C) (N : D) :
    let alpha : J ⋙ Pp ⟶ Pr ⋙ K := alpha₀ ≫ Functor.whiskerLeft Pr₀ e.hom ≫
      Functor.whiskerRight t.hom K
    Pp.map (di.app (H, N)) ≫ alpha.app (TC.obj (H, Pi.obj N)) ≫
      K.map (muR.app (H, Pi.obj N)) ≫
      K.map (TA.map (Prod.mkHom (𝟙 _) (theta.hom.app N))) =
      muP.app (J.obj H, N) ≫ TB.map (Prod.mkHom (alpha.app H) (𝟙 _)) ≫
      dk.app (Pr.obj H, Pp.obj N) := by
  intro alpha
  dsimp only [alpha, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  simp only [Category.assoc]
  slice_lhs 4 5 => rw [← K.map_comp, hmu, K.map_comp]
  have he₁ := e.hom.naturality (mu₀.app (H, Pi.obj N))
  have he₂ := e.hom.naturality
    (TA.map (Prod.mkHom (𝟙 (Pr₀.obj H)) (theta₀.hom.app N)))
  have hd := dk.naturality (Prod.mkHom (t.hom.app H) (𝟙 (Pp.obj N)))
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.prod_obj, Functor.prod_map,
    Functor.id_obj, Functor.id_map] at he₁ he₂ hd
  slice_lhs 3 4 => rw [← he₁]
  have hp : Prod.mkHom (t.hom.app H) (t.hom.app (Pi.obj N)) ≫
      Prod.mkHom (𝟙 (Pr.obj H)) (theta.hom.app N) =
      Prod.mkHom (𝟙 (Pr₀.obj H)) (theta₀.hom.app N) ≫
        Prod.mkHom (𝟙 (Pr₀.obj H)) (c.hom.app (Pp.obj N)) ≫
          Prod.mkHom (t.hom.app H) (Pk.map (𝟙 (Pp.obj N))) := by
    ext
    · simp
    · simpa using htheta N
  slice_lhs 5 6 => rw [← K.map_comp, ← TA.map_comp, hp, TA.map_comp, TA.map_comp,
    K.map_comp, K.map_comp]
  slice_lhs 4 5 => rw [← he₂]
  simp only [Category.assoc]
  rw [reassoc_of% hsquare H N]
  slice_lhs 3 5 => rw [hdelta]
  slice_lhs 4 5 => rw [← hd]
  simp only [← TB.map_comp_assoc]
  congr 2
  apply congrArg TB.map
  ext <;> simp

private theorem properOpenTensor_comp
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b]
    (M : ProperOpenDerived Λ U) (N : ProperOpenDerived Λ X) :
    (properOpenTensorIso Λ b ((ProperOpenShriek Λ s).obj M) N).hom ≫
      (ProperOpenShriek Λ b).map
        (properOpenTensorIso Λ s M ((ProperOpenPull Λ b).obj N)).hom ≫
      (properOpenShriekComp Λ s b).hom.app
        (((ProperOpenTensor Λ U).obj M).obj
          ((ProperOpenPull Λ s).obj ((ProperOpenPull Λ b).obj N))) ≫
      (ProperOpenShriek Λ (s ≫ b)).map
        (((ProperOpenTensor Λ U).obj M).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s b).inv.app N)) =
    ((ProperOpenTensor Λ X).map ((properOpenShriekComp Λ s b).hom.app M)).app N ≫
      (properOpenTensorIso Λ (s ≫ b) M N).hom := by
  let L := ProperOpenShriek Λ s
  let B := ProperOpenShriek Λ b
  let S := ProperOpenPull Λ s
  let R := ProperOpenPull Λ b
  let U' := Functor.uncurry.obj (ProperOpenTensor Λ U)
  let T := Functor.uncurry.obj (ProperOpenTensor Λ V)
  let W := Functor.uncurry.obj (ProperOpenTensor Λ X)
  let a := properOpenAdj Λ s
  let ab := properOpenAdj Λ b
  let a' := properOpenAdj Λ (s ≫ b)
  let mu := tensorComparisonComp S R U' T W (properOpenMu Λ s) (properOpenMu Λ b)
  let delta := openTensorComp L S B R U' T W (properOpenDelta Λ s) (properOpenDelta Λ b)
  let e := properOpenShriekComp Λ s b
  let c := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s b).symm
  have he (H : ProperOpenDerived Λ U) :
      (a.comp ab).unit.app H ≫ c.hom.app ((L ⋙ B).obj H) =
        a'.unit.app H ≫ (ProperOpenPull Λ (s ≫ b)).map (e.inv.app H) := by
    simpa only [a, ab, a', e, c, properOpenShriekComp,
      Adjunction.conjugateEquiv_leftAdjointCompIso_inv] using
      unit_conjugateEquiv (a.comp ab) a' e.inv H
  have hc (F V' : ProperOpenDerived Λ X) :
      mu.inv.app (F, V') ≫ c.hom.app (W.obj (F, V')) =
        U'.map (Prod.mkHom (c.hom.app F) (c.hom.app V')) ≫
          (properOpenMu Λ (s ≫ b)).inv.app (F, V') := by
    apply (cancel_epi (mu.hom.app (F, V'))).1
    simp only [Iso.hom_inv_id_app_assoc]
    apply (cancel_mono ((properOpenMu Λ (s ≫ b)).hom.app (F, V'))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    have ht := properOpenPull_comp_tensor Λ s b F V'
    dsimp only [mu, tensorComparisonComp, NatIso.ofComponents, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom]
    simp only [properOpenMu_hom]
    apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s b).hom.app
      (W.obj (F, V')))).1
    simp only [c, Iso.symm_hom, Iso.hom_inv_id_app_assoc]
    dsimp only [S, R, U', W, Functor.uncurry_obj_obj]
    simp only [Category.assoc]
    erw [Category.comp_id]
    rw [reassoc_of% ht]
    rw [← U'.map_comp]
    have hp :
        Prod.mkHom ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s b).hom.app F)
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s b).hom.app V') ≫
        Prod.mkHom ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s b).inv.app F)
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s b).inv.app V') = 𝟙 _ := by
      ext <;> simp
    rw [hp, U'.map_id]
    erw [Category.comp_id]
  have hd (H : ProperOpenDerived Λ U) (V' : ProperOpenDerived Λ X) :
      (a.comp ab).homEquiv _ _ (delta.inv.app (H, V')) =
        U'.map (Prod.mkHom ((a.comp ab).unit.app H) (𝟙 _)) ≫
          mu.inv.app ((L ⋙ B).obj H, V') := by
    have ht := open_tensor_composite_transpose L S B R a ab U' T W
      (properOpenMu Λ s) (properOpenMu Λ b)
      (properOpenDelta Λ s) (properOpenDelta Λ b)
      (fun H V' ↦ by
        simpa only [L, S, B, R, a, ab, a', U', T, W,
          Functor.comp_obj, Functor.prod_obj, Functor.id_obj, Functor.uncurry_obj_obj,
          properOpenDelta_inv, properOpenMu_inv,
          Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, Category.comp_id] using
          properOpenTensorIso_inv_transpose Λ s H V')
      (fun H V' ↦ by
        simpa only [L, S, B, R, a, ab, T, W,
          Functor.comp_obj, Functor.prod_obj, Functor.id_obj, Functor.uncurry_obj_obj,
          properOpenDelta_inv, properOpenMu_inv,
          Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, Category.comp_id] using
          properOpenTensorIso_inv_transpose Λ b H V') H V'
    simpa only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj,
      delta, mu, openTensorComp, tensorComparisonComp, NatIso.ofComponents,
      Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc, Functor.map_comp]
      using ht
  have hn := open_tensor_transport (L ⋙ B) (ProperOpenShriek Λ (s ≫ b))
    (R ⋙ S) (ProperOpenPull Λ (s ≫ b)) (a.comp ab) a' W U' mu
    (properOpenMu Λ (s ≫ b)) delta (properOpenDelta Λ (s ≫ b)) e c he hc hd
    (fun H V' ↦ by
      simpa only [L, S, B, R, a, ab, a', U', T, W,
          Functor.comp_obj, Functor.prod_obj, Functor.id_obj, Functor.uncurry_obj_obj,
          properOpenDelta_inv, properOpenMu_inv, Functor.uncurry_obj_map,
        CategoryTheory.Functor.map_id, Category.comp_id] using
        properOpenTensorIso_inv_transpose Λ (s ≫ b) H V') M N
  simpa only [L, B, S, R, U', T, W, e, c, delta, openTensorComp,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.ofComponents,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, properOpenDelta_hom,
    Iso.symm_hom, Functor.uncurry_obj_map, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Functor.comp_obj, Functor.prod_obj, Functor.id_obj,
    Functor.uncurry_obj_obj, Category.id_comp, Category.comp_id, Category.assoc] using hn

private theorem properOpenTensor_congr
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} {j k : U ⟶ X} [IsOpenImmersion j] [IsOpenImmersion k]
    (h : j = k) (M : ProperOpenDerived Λ U) (N : ProperOpenDerived Λ X) :
    (properOpenTensorIso Λ j M N).hom ≫
      (properOpenShriekCongr Λ h).hom.app
        (((ProperOpenTensor Λ U).obj M).obj ((ProperOpenPull Λ j).obj N)) ≫
      (ProperOpenShriek Λ k).map (((ProperOpenTensor Λ U).obj M).map
        ((leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) h).hom.app N)) =
    ((ProperOpenTensor Λ X).map ((properOpenShriekCongr Λ h).hom.app M)).app N ≫
      (properOpenTensorIso Λ k M N).hom := by
  subst k
  have he : properOpenShriekCongr Λ (rfl : j = j) = Iso.refl _ := by
    simp only [properOpenShriekCongr, leftDerivedUpperStarCongr_rfl]
    have ha : (properOpenAdj Λ j).ofNatIsoRight (Iso.refl _) = properOpenAdj Λ j := by
      apply Adjunction.ext
      ext H
      simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
        Functor.whiskerLeft_app, Iso.refl_hom, NatTrans.id_app]
      erw [Category.comp_id]
    rw [ha]
    apply Iso.ext
    exact Adjunction.leftAdjointUniq_refl _
  simp only [he, leftDerivedUpperStarCongr_rfl, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

private theorem properOpenTensor_factorization
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X) (k : U ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] [IsOpenImmersion k] (h : s ≫ b = k)
    (M : ProperOpenDerived Λ U) (N : ProperOpenDerived Λ X) :
    let e := properOpenShriekComp Λ s b ≪≫ properOpenShriekCongr Λ h
    let c := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s b).symm ≪≫
      leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) h
    (properOpenTensorIso Λ b ((ProperOpenShriek Λ s).obj M) N).hom ≫
      (ProperOpenShriek Λ b).map
        (properOpenTensorIso Λ s M ((ProperOpenPull Λ b).obj N)).hom ≫
      e.hom.app (((ProperOpenTensor Λ U).obj M).obj
        ((ProperOpenPull Λ s).obj ((ProperOpenPull Λ b).obj N))) ≫
      (ProperOpenShriek Λ k).map (((ProperOpenTensor Λ U).obj M).map (c.hom.app N)) =
    ((ProperOpenTensor Λ X).map (e.hom.app M)).app N ≫
      (properOpenTensorIso Λ k M N).hom := by
  intro e c
  dsimp only [e, c, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  have hn := (properOpenShriekCongr Λ h).hom.naturality
    (((ProperOpenTensor Λ U).obj M).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s b).inv.app N))
  dsimp only [Functor.comp_obj] at hn
  slice_lhs 4 5 => erw [← hn]
  simp only [Category.assoc]
  rw [reassoc_of% properOpenTensor_comp Λ s b M N]
  rw [properOpenTensor_congr Λ h M N]
  rw [Functor.map_comp, NatTrans.comp_app]
  simp only [Category.assoc]

private theorem properOpenPull_factorization_tensor
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U V X : Scheme.{u}} (s : U ⟶ V) (q : V ⟶ X) (r : U ⟶ X)
    (h : s ≫ q = r) (M N : ProperOpenDerived Λ X) :
    let t := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s q).symm ≪≫
      leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) h
    t.hom.app (((ProperOpenTensor Λ X).obj M).obj N) ≫
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) r M N).hom =
    (ProperOpenPull Λ s).map (leftDerivedUpperStarTensorIso
      (ModuleCat.{u + 1} Λ) q M N).hom ≫
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) s
        ((ProperOpenPull Λ q).obj M) ((ProperOpenPull Λ q).obj N)).hom ≫
      (Functor.uncurry.obj (ProperOpenTensor Λ U)).map
        (Prod.mkHom (t.hom.app M) (t.hom.app N)) := by
  subst r
  intro t
  dsimp only [t, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [leftDerivedUpperStarCongr_rfl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id]
  apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s q).hom.app
    (((ProperOpenTensor Λ X).obj M).obj N))).1
  simp only [Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% properOpenPull_comp_tensor Λ s q M N]
  rw [← Functor.map_comp]
  have hp :
      Prod.mkHom ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s q).hom.app M)
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s q).hom.app N) ≫
      Prod.mkHom ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s q).inv.app M)
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s q).inv.app N) = 𝟙 _ := by
    ext <;> simp
  rw [hp, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

private theorem properOpenPull_factorization_square
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A B C D V : Scheme.{u}} (s : A ⟶ V) (b : V ⟶ B) (q : V ⟶ C)
    (k : A ⟶ B) (r : A ⟶ C) (p : B ⟶ D) (i : C ⟶ D)
    (hsb : s ≫ b = k) (hsq : s ≫ q = r) (hbq : q ≫ i = b ≫ p)
    (h : k ≫ p = r ≫ i) (N : ProperOpenDerived Λ D) :
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s q).inv.app
        ((ProperOpenPull Λ i).obj N) ≫
      (leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) hsq).hom.app
        ((ProperOpenPull Λ i).obj N)) ≫
      (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) (CommSq.mk h)).hom.app N =
    (ProperOpenPull Λ s).map
      ((leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) (CommSq.mk hbq)).inv.app N) ≫
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s b).inv.app
        ((ProperOpenPull Λ p).obj N) ≫
      (leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) hsb).hom.app
        ((ProperOpenPull Λ p).obj N)) := by
  let aa := (compIso (ModuleCat.{u + 1} Λ) s (b ≫ p) (k ≫ p)
    (by rw [← hsb, Category.assoc])).app N
  let bb := (ProperOpenPull Λ s).mapIso
    ((compIso (ModuleCat.{u + 1} Λ) q i (b ≫ p) hbq.symm).app N)
  let cc := (compIso (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).app N
  let dd := (compIso (ModuleCat.{u + 1} Λ) s q r hsq.symm).app
    ((ProperOpenPull Λ i).obj N)
  let ee := (ProperOpenPull Λ s).mapIso
    ((compIso (ModuleCat.{u + 1} Λ) b p (b ≫ p) rfl).app N)
  let ff := (compIso (ModuleCat.{u + 1} Λ) k p (k ≫ p) rfl).app N
  let gg := (compIso (ModuleCat.{u + 1} Λ) s b k hsb.symm).app
    ((ProperOpenPull Λ p).obj N)
  have h₁ : aa.hom ≫ bb.hom = cc.hom ≫ dd.hom := by
    exact comp_assoc (ModuleCat.{u + 1} Λ) s q i r (b ≫ p) (k ≫ p)
      hsq.symm hbq.symm h N
  have h₂ : aa.hom ≫ ee.hom = ff.hom ≫ gg.hom := by
    exact comp_assoc (ModuleCat.{u + 1} Λ) s b p k (b ≫ p) (k ≫ p)
      hsb.symm rfl rfl N
  have he : aa ≪≫ bb = cc ≪≫ dd := Iso.ext h₁
  have hi := congrArg Iso.inv he
  dsimp only [Iso.trans_inv] at hi
  have hj := congrArg (fun z ↦ aa.inv ≫ z ≫ gg.inv) h₂
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] at hj
  have hh : dd.inv ≫ cc.inv ≫ ff.hom = bb.inv ≫ ee.hom ≫ gg.inv := by
    rw [← Category.assoc, ← hi, Category.assoc, ← hj]
  simpa only [aa, bb, cc, dd, ee, ff, gg, square_eq, compIso,
    Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, NatTrans.comp_app,
    leftDerivedUpperStarCongr_rfl, leftDerivedUpperStarCongr_inv_app,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.comp_id,
    Iso.symm_hom, Iso.symm_inv, Category.assoc] using hh

private theorem clopen_tensor_of_normalization
    {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) (S : D ⥤ C) (a : L ⊣ S) (b : S ⊣ L)
    (T : D × D ⥤ D) (U : C × C ⥤ C)
    (mu : T ⋙ S ≅ (S.prod S) ⋙ U)
    (delta : (L.prod (𝟭 D)) ⋙ T ≅ (𝟭 C).prod S ⋙ U ⋙ L)
    (hn : ∀ M : C, a.unit.app M ≫ b.counit.app M = 𝟙 M)
    (hu : ∀ M : C, IsIso (a.unit.app M))
    (hd : ∀ (M : C) (V : D), a.homEquiv _ _ (delta.inv.app (M, V)) =
      U.map (Prod.mkHom (a.unit.app M) (𝟙 (S.obj V))) ≫ mu.inv.app (L.obj M, V))
    (F V : D) :
    b.unit.app (T.obj (F, V)) ≫ L.map (mu.hom.app (F, V)) =
      T.map (Prod.mkHom (b.unit.app F) (𝟙 V)) ≫ delta.hom.app (S.obj F, V) := by
  have ht (M : C) :
      S.map (delta.hom.app (M, V)) ≫ b.counit.app (U.obj (M, S.obj V)) =
        mu.hom.app (L.obj M, V) ≫
          U.map (Prod.mkHom (b.counit.app M) (𝟙 (S.obj V))) := by
    have := hu (U.obj (M, S.obj V))
    apply (cancel_epi (S.map (delta.inv.app (M, V)))).1
    slice_lhs 1 2 =>
      rw [← S.map_comp, Iso.inv_hom_id_app]
      exact S.map_id _
    rw [Category.id_comp]
    apply (cancel_epi (a.unit.app (U.obj (M, S.obj V)))).1
    have he := hd M V
    change a.unit.app (U.obj (M, S.obj V)) ≫ S.map (delta.inv.app (M, V)) = _ at he
    slice_rhs 1 2 => rw [he]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← U.map_comp]
    have hp : Prod.mkHom (a.unit.app M) (𝟙 (S.obj V)) ≫
        Prod.mkHom (b.counit.app M) (𝟙 (S.obj V)) = 𝟙 _ := by
      ext
      · exact hn M
      · simp
    rw [hp, U.map_id]
    exact hn _
  apply ((b.homEquiv _ _).symm).injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  change S.map (b.unit.app (T.obj (F, V))) ≫ S.map (L.map (mu.hom.app (F, V))) ≫
      b.counit.app (U.obj (S.obj F, S.obj V)) =
    S.map (T.map (Prod.mkHom (b.unit.app F) (𝟙 V))) ≫
      S.map (delta.hom.app (S.obj F, V)) ≫ b.counit.app (U.obj (S.obj F, S.obj V))
  slice_lhs 2 3 => exact b.counit.naturality (mu.hom.app (F, V))
  slice_lhs 1 2 => exact b.left_triangle_components (T.obj (F, V))
  simp only [CategoryTheory.Functor.id_map]
  rw [ht]
  have hm := mu.hom.naturality (Prod.mkHom (b.unit.app F) (𝟙 V))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj] at hm
  slice_rhs 1 2 => exact hm
  rw [Category.assoc, ← U.map_comp]
  have hp : Prod.mkHom (S.map (b.unit.app F)) (S.map (𝟙 V)) ≫
      Prod.mkHom (b.counit.app (S.obj F)) (𝟙 (S.obj V)) = 𝟙 _ := by
    ext
    · exact b.left_triangle_components F
    · simp
  rw [hp]
  erw [U.map_id, Category.id_comp, Category.comp_id]
  rfl

section ClopenNormalization

private theorem homotopy_unit_counit
    {C : Type*} {D : Type*} [Category.{v} C] [Category.{v} D] [Abelian C] [Abelian D]
    {F : C ⥤ D} {G : D ⥤ C} {H : C ⥤ D}
    [F.Additive] [G.Additive] [H.Additive]
    (a : F ⊣ G) (b : G ⊣ H) (e : F ≅ H)
    (h : a.unit ≫ Functor.whiskerRight e.hom G ≫ b.counit = 𝟙 (𝟭 C))
    (P : HomotopyCategory C (.up ℤ)) :
    (a.mapHomotopyCategory (.up ℤ)).unit.app P ≫
      (G.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P) ≫
      (b.mapHomotopyCategory (.up ℤ)).counit.app P = 𝟙 P := by
  obtain ⟨Q, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  simp only [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient,
    NatTrans.mapHomotopyCategory_app]
  change (HomotopyCategory.quotient C (.up ℤ)).map
      ((a.mapHomologicalComplex (.up ℤ)).unit.app Q) ≫
    (HomotopyCategory.quotient C (.up ℤ)).map
      ((G.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app Q)) ≫
    (HomotopyCategory.quotient C (.up ℤ)).map
      ((b.mapHomologicalComplex (.up ℤ)).counit.app Q) = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  have hh : (a.mapHomologicalComplex (.up ℤ)).unit.app Q ≫
      (G.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app Q) ≫
      (b.mapHomologicalComplex (.up ℤ)).counit.app Q = 𝟙 Q := by
    ext n : 1
    exact congr_app h (Q.X n)
  exact (congrArg (HomotopyCategory.quotient C (.up ℤ)).map hh).trans
    ((HomotopyCategory.quotient C (.up ℤ)).map_id Q)

open CategoryTheory.Limits CategoryTheory.MonoidalCategory Abelian
variable {C : Type v} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [HasFunctorialFlatResolution C]
  {D : Type w} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] [BraidedCategory D] [HasFunctorialFlatResolution D]
  {F : C ⥤ D} {G : D ⥤ C} {H : C ⥤ D}
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

private theorem derived_unit_counit
    (a : F ⊣ G) (b : G ⊣ H) (e : F ≅ H)
    (h : a.unit ≫ Functor.whiskerRight e.hom G ≫ b.counit = 𝟙 (𝟭 C))
    (M : DerivedCategory C) :
    (a.mapDerivedCategoryAdjunction.ofNatIsoRight
      G.leftDerivedFunctorIsoMapDerivedCategory.symm).unit.app M ≫
    (b.derivedAdjunction.ofNatIsoRight
      (H.rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso e.symm)).counit.app M = 𝟙 M := by
  have he : Functor.mapDerivedCategoryNatIso e.symm =
      (Functor.mapDerivedCategoryNatIso e).symm := by
    apply Iso.ext
    exact Functor.mapDerivedCategoryNatIso_symm e
  rw [he]
  let c := b.mapDerivedCategoryAdjunction.ofNatIsoRight
    (Functor.mapDerivedCategoryNatIso e).symm
  have hc : a.mapDerivedCategoryAdjunction.unit ≫ c.counit = 𝟙 _ := by
    apply Localization.natTrans_ext DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ))
    intro P
    simp only [NatTrans.comp_app, NatTrans.id_app, c, Adjunction.ofNatIsoRight_counit,
      Functor.whiskerRight_app, Iso.symm_inv]
    rw [b.mapDerivedCategoryAdjunction_counit_app_Qh_obj]
    rw [← Functor.map_comp_assoc, Functor.mapDerivedCategoryNatIso_fach]
    rw [Functor.map_comp]
    simp only [Category.assoc]
    erw [G.mapDerivedCategoryFactorsh.hom.naturality_assoc]
    rw [reassoc_of% (a.mapDerivedCategoryAdjunction_unit_app_Qh_obj P)]
    have hn := homotopy_unit_counit a b e h P
    simpa only [Functor.comp_map, Functor.map_comp, Functor.id_obj] using
      (congrArg DerivedCategory.Qh.map hn).trans (DerivedCategory.Qh.map_id P)
  have hh := congr_app hc M
  dsimp only [c] at hh
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Iso.symm_inv] at hh
  have hbc : b.mapDerivedCategoryAdjunction.counit.app M =
      G.mapDerivedCategory.map (H.rightDerivedFunctorIsoMapDerivedCategory.inv.app M) ≫
      G.leftDerivedFunctorIsoMapDerivedCategory.inv.app _ ≫
      b.derivedAdjunction.counit.app M := by
    simp only [Adjunction.mapDerivedCategoryAdjunction, Adjunction.ofNatIsoLeft_counit,
      Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
  rw [hbc] at hh
  simp only [NatTrans.id_app] at hh
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoRight_counit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Iso.trans_inv, Category.assoc]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  let iso := G.leftDerivedFunctorIsoMapDerivedCategory
  have h₁ := iso.inv.naturality ((Functor.mapDerivedCategoryNatIso e).hom.app M)
  have h₂ := iso.inv.naturality (H.rightDerivedFunctorIsoMapDerivedCategory.inv.app M)
  erw [← reassoc_of% h₁, ← reassoc_of% h₂]
  exact hh

end ClopenNormalization

private theorem properOpenClopen_counit
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s]
    (M : ProperOpenDerived Λ U) :
    (properOpenAdj Λ s).unit.app M ≫
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).ofNatIsoRight
        (rightDerivedLowerStarIsoOfIsClosedRange (ModuleCat.{u + 1} Λ) s
          s.isClosedEmbedding.isClosed_range)).counit.app M = 𝟙 M := by
  let := preservesFiniteColimits_lowerStar_of_isClosed_range
    (ModuleCat.{u + 1} Λ) s s.isClosedEmbedding.isClosed_range
  let a := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) s
  let b := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s
  let e := ClopenCompositeCounit.sheafComparison Λ s
  have hsheaf : a.unit ≫
      Functor.whiskerRight e.hom (upperStar (ModuleCat.{u + 1} Λ) s) ≫
      b.counit = 𝟙 (𝟭 (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ))) := by
    apply NatTrans.ext
    funext Q
    have hh := congr_app (ClopenCompositeCounit.sheaf_counit Λ s) Q
    change a.unit.app Q ≫
      ((ClopenCompositeCounit.reverseSheafAdjunction Λ s).counit.app Q) = 𝟙 _
    rw [hh, NatIso.isIso_inv_app]
    exact IsIso.hom_inv_id (a.unit.app Q)
  simpa only [a, b, e, properOpenAdj,
    derivedOpenImmersionLowerShriekUpperStarAdjunction,
    derivedUpperStarLowerStarAdjunction, leftDerivedUpperStarIsoMapDerivedCategory,
    rightDerivedLowerStarIsoOfIsClosedRange, ClopenCompositeCounit.sheafComparison]
    using derived_unit_counit a b e hsheaf M

private theorem properOpenClopen_tensor
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s]
    (F V : ProperOpenDerived Λ X) :
    (properOpenClopenProjection Λ s).app (((ProperOpenTensor Λ X).obj F).obj V) ≫
        (ProperOpenShriek Λ s).map
          ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) s F V).hom) =
      ((ProperOpenTensor Λ X).map ((properOpenClopenProjection Λ s).app F)).app V ≫
        (properOpenTensorIso Λ s ((ProperOpenPull Λ s).obj F) V).hom := by
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} Λ) s).unit :=
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} Λ) s).unit_isIso_of_L_fully_faithful
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} Λ) s).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  let L := ProperOpenShriek Λ s
  let S := ProperOpenPull Λ s
  let a := properOpenAdj Λ s
  let b := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).ofNatIsoRight
    (rightDerivedLowerStarIsoOfIsClosedRange (ModuleCat.{u + 1} Λ) s
      s.isClosedEmbedding.isClosed_range)
  let T := Functor.uncurry.obj (ProperOpenTensor Λ X)
  let tensorU := Functor.uncurry.obj (ProperOpenTensor Λ U)
  let mu := properOpenMu Λ s
  let delta := properOpenDelta Λ s
  have hn := clopen_tensor_of_normalization L S a b T tensorU mu delta
    (properOpenClopen_counit Λ s) (fun M ↦ by
      simp only [a, properOpenAdj, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
        Functor.whiskerLeft_app, Iso.symm_hom]
      infer_instance)
    (fun M N ↦ by
      simpa only [L, S, a, T, delta, mu, properOpenDelta_inv, properOpenMu_inv,
        tensorU, Functor.prod_obj, Functor.comp_obj, Functor.id_obj,
        Functor.uncurry_obj_obj, Functor.uncurry_obj_map, CategoryTheory.Functor.map_id,
        Category.comp_id] using properOpenTensorIso_inv_transpose Λ s M N) F V
  simpa only [L, S, a, b, T, tensorU, mu, delta, properOpenDelta_hom, properOpenMu_hom,
    Functor.uncurry_obj_map, Functor.uncurry_obj_obj, Functor.prod_obj, Functor.comp_obj,
    Functor.id_obj, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.comp_id, properOpenClopenProjection, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app] using hn

attribute [local implicit_reducible] derivedTensorRightDerivedLowerStar
  rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar

set_option maxRecDepth 4096 in
/-- The normalized proper/open mate commutes with projection on arbitrary unbounded
ordinary constant-coefficient inputs. Source: Stacks 0F7B--0F7D and the agent tensor/counit
calculation (blueprint: lem-sf-proper-open-projection-mate).

Proof, following all eight steps of the DAG node:

1. Use [lem-cbc-strict-tower-proper-open-calculus] for the geometry of the square: $s=(k,r):A\to
B_C$ is clopen, $bs=k$, $qs=r$, and $\alpha$ is exactly the specified base-change map followed by
projection onto $s(A)$. This geometric assertion has no hypothesis on an input complex. Write
$J=i_!$, $K=k_!$, $E=R_rM$, $X=P_iN$, $Y=P_pN$, and $T=P_rX=P_kY$. All tensors below are derived;
canonical pullback/tensor identifications are understood. For an open $j$ write
$\delta_j(U,V):j_!U\otimes V\to j_!(U\otimes P_jV)$. The normalizations in
[lem-sf-open-tensor-normalization] make these maps and the open base-change map identities after
restriction and the open units.

2. First check the tensor square for the base-change factor $\beta:P_pJ\to b_!P_q$. For arbitrary
$H$ on $C$, its two routes have source $P_p(JH\otimes N)$ and target $b_!(P_qH\otimes P_bY)$: one
applies $P_p\delta_i$, then $\beta_{H\otimes X}$ and the pullback tensor comparison; the other
applies $\mu_p$, then $\beta_H\otimes1_Y$ and $\delta_b$. Both source and target lie in the image
of $b_!$: use $\beta_H$ and the open tensor isomorphism to identify the source with
$b_!(P_qH\otimes P_bY)$. Thus full faithfulness of $b_!$ reduces equality to restriction by $P_b$.
Under the open units, $P_b\beta$ and $P_i\delta_i$ are identities. The remaining maps on both
routes are the canonical pullback/tensor comparison on $P_qH\otimes P_bY$, using $P_bP_p=P_qP_i$.
Hence the square commutes. Here the comparison is the canonical one for the commutative ringed
pullback square, as in [lem-weil-pbc-ringed-exchange-tensor-coherence].

3. The clopen-projection factor also respects tensor: in $B_C=s(A)\amalg(B_C\setminus s(A))$,
$\pi_s$ acts by $(1,0)$. Tensoring it with $P_bY$ still acts by $(1,0)$ on the two components. The
open tensor comparison for $s$ restricts to the identity on $s(A)$; on the complementary component
its target is zero. Consequently projection before tensor and projection after tensor agree,
followed by $\delta_s$. This is an identity of the given termwise clopen projections on complexes
and hence of their derived classes, using the canonical tensor comparisons. The comparisons for
the composite open $bs=k$ agree with $\delta_k$: both are maps between objects in the image of
$k_!$, and after restriction to $k$ they are identities, so full faithfulness gives equality.
Combining this calculation with Step 2 gives, for every $H$ on $C$, the explicit identity
$$K(\mu_r)\,\alpha_{H\otimes X}\,P_p(\delta_i)=\delta_k\,(\alpha_H\otimes1_Y)\,\mu_p.$$ Both sides
run from $P_p(JH\otimes N)$ to $K(P_rH\otimes T)$.

4. Put $Z=M\otimes T$ and $a_r=(\varepsilon_{r,M}\otimes1_T)\mu_r:P_r(E\otimes X)\to Z$. The
counit definition of $\pi_r$ gives $\varepsilon_{r,Z}P_r(\pi_r)=a_r$. The mate definition of
$\gamma$ gives $\varepsilon_{p,KW}P_p(\gamma_W)=K(\varepsilon_{r,W})\alpha_{R_rW}$ for every $W$.
Therefore the transpose under $P_p\dashv R_p$ of the left side of the claimed identity is
$$K(\varepsilon_{r,Z})\,\alpha_{R_rZ}\,P_pJ(\pi_r)\,P_p\delta_i
=K(\varepsilon_{r,Z}P_r\pi_r)\,\alpha_{E\otimes X}\,P_p\delta_i =K(a_r)\,\alpha_{E\otimes
X}\,P_p\delta_i.$$ The middle equality is naturality of $\alpha$ for the arrow $\pi_r:E\otimes
X\to R_rZ$.

5. Transpose the right side under the same adjunction. Naturality of $\varepsilon_p$ first moves
$R_p\delta_k$ out of the transpose; the defining adjunct equation of $\pi_p$ then gives
$$\delta_k\,(\varepsilon_{p,KM}\otimes1_Y)\,\mu_p\,P_p(\gamma_M\otimes1_N).$$ Naturality of
$\mu_p$ replaces this by $$\delta_k\,((\varepsilon_{p,KM}P_p\gamma_M)\otimes1_Y)\,\mu_p
=\delta_k\,((K\varepsilon_{r,M}\,\alpha_E)\otimes1_Y)\,\mu_p.$$ Now apply naturality of $\delta_k$
to $\varepsilon_{r,M}:P_rE\to M$, and then the identity of Step 3 with $H=E$. The result is
$$K(\varepsilon_{r,M}\otimes1_T)\,K(\mu_r)\,\alpha_{E\otimes X}\,P_p\delta_i
=K(a_r)\,\alpha_{E\otimes X}\,P_p\delta_i,$$ which is the transpose computed in Step 4. The
adjunction Hom bijection is injective, so the original maps agree. All substitutions are natural
in $M,N$.

6. These calculations use arbitrary inputs in the unbounded ringed-site derived categories. In
particular [lem-weil-pbc-ringed-projection-mate-exact] supplies the counit-defined map for
arbitrary sheaves of commutative rings and all objects, so the use of its formula does not
specialize the finite ring $\Lambda$ to a quotient DVR or impose invertibility of its order.
[lem-sf-open-tensor-normalization] also has no boundedness or Tor hypothesis. We never invert
$\pi_p$, $\pi_r$ or $\gamma$, nor invoke a proper projection formula or proper base-change
isomorphism on these inputs. This proves precisely the finite constant-coefficient identity
claimed.

7. We identify the stipulated system $\Gamma_Q$ intrinsically, rather than from its finite
evaluations. Let $\widetilde\gamma$ be the proper-adjunction mate of the clopen $\alpha$. The
realization node characterizes $\Gamma_Q$ by $\lambda_QP_i\Gamma_Q=1$ under the open unit, where
$\lambda_Q:P_iS_pJ_k\cong S_r$ is obtained by open restriction, $k=bs$, $J_s=S_s$ for the clopen
$s$, and direct-image composition. Make exactly those identifications in $P_i\widetilde\gamma$.
Mate pasting identifies the restricted unit/counit maps with the unit/counit of $P_r\dashv S_r$;
the restricted open base-change map is the identity by open normalization, and the clopen
projection acts as identity on $J_sM$. Thus the composite $\lambda_QP_i\widetilde\gamma$ is
$S_r\varepsilon_r\circ\eta_rS_r=1_{S_r}$ by the triangle identity. Since $J_i\dashv P_i$ gives a
bijection on the relevant Hom sets, its adjunct characterization implies
$\widetilde\gamma=\Gamma_Q$. This argument uses only the intrinsic open-restriction
characterization and canonical composite adjunctions, and is independent of the total-limit
comparisons or the finite evaluated arrows.

8. For the system assertion, apply Steps 1--5 inside the unbounded derived module categories of
the ringed diagram sites themselves. [lem-pur-coefficient-system-derived-comparison] supplies the
exact system inverse images and their derived adjunctions on these unbounded categories.
[lem-sf-open-tensor-normalization] explicitly supplies the same open-unit, tensor and base-change
normalization on the diagram topoi. The operations and intrinsic $\Gamma_Q$ are the simultaneous
ringed-diagram constructions stipulated in [lem-sf-integral-compactification-system-realization];
Step 7 identifies $\Gamma_Q$ with the proper mate of the same clopen-projection $\alpha$. Thus the
system analogue of the mate equation in Step 4 is an equation in the system category. On system
complexes the clopen projection in Step 3 is literally identity on the open component and zero on
its complement; these are morphisms of systems, compatible with every coefficient transition.
Steps 4--5 now compare the two system maps by the single system adjunction Hom bijection and the
displayed common transpose, before applying any evaluation. The generic ringed tensor/projection
nodes apply to these small ringed diagram sites without change. Only the unbounded operations and
intrinsic-map clauses of the realization node are used; no total-limit realization or
constructible-domain claim is needed.
-/
theorem properOpenProjectionMate
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A B C D : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C)
    (p : B ⟶ D) (i : C ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (M : ProperOpenDerived Λ A) (N : ProperOpenDerived Λ D) :
    (properOpenTensorIso Λ i ((ProperOpenPush Λ r).obj M) N).hom ≫
      (ProperOpenShriek Λ i).map (properOpenProjection Λ r M ((ProperOpenPull Λ i).obj N)) ≫
      (ProperOpenShriek Λ i).map ((ProperOpenPush Λ r).map
        (((ProperOpenTensor Λ A).obj M).map
          ((properOpenPullSquareIso Λ k r p i h).hom.app N))) ≫
      (properOpenMate Λ k r p i h).app
        (((ProperOpenTensor Λ A).obj M).obj
          ((ProperOpenPull Λ k).obj ((ProperOpenPull Λ p).obj N))) =
    properOpenMateTensorMap Λ k r p i h M N ≫
      properOpenProjection Λ p ((ProperOpenShriek Λ k).obj M) N ≫
      (ProperOpenPush Λ p).map
        (properOpenTensorIso Λ k M ((ProperOpenPull Λ p).obj N)).hom := by
  let Pr := ProperOpenPull Λ r
  let Pp := ProperOpenPull Λ p
  let Rr := ProperOpenPush Λ r
  let Rp := ProperOpenPush Λ p
  let J := ProperOpenShriek Λ i
  let K := ProperOpenShriek Λ k
  let TA := ProperOpenTensor Λ A
  let TB := ProperOpenTensor Λ B
  let TD := ProperOpenTensor Λ D
  let ar := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r
  let ap := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p
  let a := properOpenAlpha Λ k r p i h
  let θ := properOpenPullSquareIso Λ k r p i h
  have square (H : ProperOpenDerived Λ C) (N₀ : ProperOpenDerived Λ D) :
      Pp.map (properOpenTensorIso Λ i H N₀).hom ≫
          a.app (((ProperOpenTensor Λ C).obj H).obj ((ProperOpenPull Λ i).obj N₀)) ≫
          K.map (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) r).app H).app
            ((ProperOpenPull Λ i).obj N₀)) ≫
          K.map ((TA.obj (Pr.obj H)).map (θ.hom.app N₀)) =
        ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) p).app
          (J.obj H)).app N₀ ≫
          ((TB.map (a.app H)).app (Pp.obj N₀)) ≫
          (properOpenTensorIso Λ k (Pr.obj H) (Pp.obj N₀)).hom := by
    let s := StrictTower.squareLift k r p i h
    let b := pullback.fst p i
    let q := pullback.snd p i
    let L := ProperOpenShriek Λ s
    let S := ProperOpenPull Λ s
    let B' := ProperOpenShriek Λ b
    let Pb := ProperOpenPull Λ b
    let Pq := ProperOpenPull Λ q
    let TC := Functor.uncurry.obj (ProperOpenTensor Λ C)
    let TE := Functor.uncurry.obj (ProperOpenTensor Λ (pullback p i))
    let TA' := Functor.uncurry.obj TA
    let TB' := Functor.uncurry.obj TB
    let TD' := Functor.uncurry.obj TD
    let β := properOpenBeta Λ q b i p (IsPullback.of_hasPullback p i).flip
    let ρ := properOpenClopenProjection Λ s
    let θb := leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ)
      ((IsPullback.of_hasPullback p i).flip.toCommSq)
    let θ₀ : ProperOpenPull Λ i ⋙ (Pq ⋙ S) ≅ Pp ⋙ (Pb ⋙ S) :=
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight θb.symm S ≪≫
        Functor.associator _ _ _
    let t := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s q).symm ≪≫
      leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) (pullback.lift_snd k r h)
    let c := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s b).symm ≪≫
      leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) (pullback.lift_fst k r h)
    let e := properOpenShriekComp Λ s b ≪≫
      properOpenShriekCongr Λ (pullback.lift_fst k r h)
    let α₀ : J ⋙ Pp ⟶ (Pq ⋙ S) ⋙ (L ⋙ B') :=
      β.hom ≫ Functor.whiskerRight (Functor.whiskerLeft Pq ρ) B'
    let μ₀ := tensorComparisonComp S Pq TA' TE TC (properOpenMu Λ s) (properOpenMu Λ q)
    let δ₀ := openTensorComp L S B' Pb TA' TE TB'
      (properOpenDelta Λ s) (properOpenDelta Λ b)
    have cart (F : ProperOpenDerived Λ C) (V : ProperOpenDerived Λ D) :=
      properOpenBeta_tensor Λ q b i p (IsPullback.of_hasPullback p i).flip F V
    have cart' (F : ProperOpenDerived Λ C) (V : ProperOpenDerived Λ D) :
        Pp.map ((properOpenDelta Λ i).hom.app (F, V)) ≫ β.hom.app
          (TC.obj (F, (ProperOpenPull Λ i).obj V)) ≫
        B'.map ((properOpenMu Λ q).hom.app (F, (ProperOpenPull Λ i).obj V)) ≫
        B'.map (TE.map (Prod.mkHom (𝟙 _) (θb.inv.app V))) =
        (properOpenMu Λ p).hom.app (J.obj F, V) ≫
        TB'.map (Prod.mkHom (β.hom.app F) (𝟙 _)) ≫
        (properOpenDelta Λ b).hom.app (Pq.obj F, Pp.obj V) := by
      simpa only [properOpenDelta_hom, properOpenMu_hom, Pp, J, B', Pq, TB', TB, TC, TE,
        β, θb, Functor.uncurry_obj_map, Functor.uncurry_obj_obj, Functor.prod_obj,
        Functor.comp_obj, leftDerivedUpperStarTensorIso_hom,
        CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id]
        using cart F V
    have sq₀ (F : ProperOpenDerived Λ C) (V : ProperOpenDerived Λ D) :
        Pp.map ((properOpenDelta Λ i).hom.app (F, V)) ≫
          α₀.app (TC.obj (F, (ProperOpenPull Λ i).obj V)) ≫
          (L ⋙ B').map (μ₀.hom.app (F, (ProperOpenPull Λ i).obj V)) ≫
          (L ⋙ B').map (TA'.map (Prod.mkHom (𝟙 _) (θ₀.hom.app V))) =
        (properOpenMu Λ p).hom.app (J.obj F, V) ≫
          TB'.map (Prod.mkHom (α₀.app F) (𝟙 _)) ≫
          δ₀.hom.app ((Pq ⋙ S).obj F, Pp.obj V) := by
      have hf := tensor_square_clopen_factors (ProperOpenPull Λ i) Pp Pq Pb S L B' J
        TA' TB' TC TD' TE (properOpenMu Λ p).hom (properOpenMu Λ q).hom
        (properOpenMu Λ s).hom (properOpenDelta Λ i).hom (properOpenDelta Λ b).hom
        (properOpenDelta Λ s).hom β.hom θb ρ cart'
        (fun F V ↦ by
          simpa only [L, TE, properOpenMu_hom, properOpenDelta_hom, ρ,
            Functor.uncurry_obj_obj, Functor.uncurry_obj_map,
            CategoryTheory.Functor.map_id, Category.comp_id] using
            properOpenClopen_tensor Λ s F V) F V
      simpa only [α₀, μ₀, δ₀, θ₀, tensorComparisonComp, openTensorComp,
        NatIso.ofComponents, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.isoWhiskerRight_hom,
        Functor.associator_hom_app, Functor.associator_inv_app, Functor.mapIso_hom,
        Iso.app_hom, Functor.comp_map, Functor.comp_obj, Functor.map_comp,
        Category.id_comp, Category.comp_id, Category.assoc] using hf
    have hmu (F V : ProperOpenDerived Λ C) :
        t.hom.app (TC.obj (F, V)) ≫ (properOpenMu Λ r).hom.app (F, V) =
          μ₀.hom.app (F, V) ≫ TA'.map (Prod.mkHom (t.hom.app F) (t.hom.app V)) := by
      simpa only [TC, TA', TA, t, S, Pq, μ₀, tensorComparisonComp, NatIso.ofComponents,
        Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, properOpenMu_hom,
        Functor.uncurry_obj_obj, Category.assoc] using
        properOpenPull_factorization_tensor Λ s q r (pullback.lift_snd k r h) F V
    have hθ (V : ProperOpenDerived Λ D) :
        t.hom.app ((ProperOpenPull Λ i).obj V) ≫ θ.hom.app V =
          θ₀.hom.app V ≫ c.hom.app (Pp.obj V) := by
      simpa only [t, c, θ₀, θb, θ, properOpenPullSquareIso, Iso.trans_hom, Iso.symm_hom,
        NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
        Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
        Category.comp_id, Category.assoc] using
        properOpenPull_factorization_square Λ s b q k r p i
          (pullback.lift_fst k r h) (pullback.lift_snd k r h)
          (pullback.condition (f := p) (g := i)).symm h V
    have hδ (F : ProperOpenDerived Λ A) (V : ProperOpenDerived Λ B) :
        δ₀.hom.app (F, V) ≫ e.hom.app (TA'.obj (F, (Pb ⋙ S).obj V)) ≫
          K.map (TA'.map (Prod.mkHom (𝟙 F) (c.hom.app V))) =
        TB'.map (Prod.mkHom (e.hom.app F) (𝟙 V)) ≫
          (properOpenDelta Λ k).hom.app (F, V) := by
      simpa only [δ₀, L, B', Pb, S, K, e, c, TA, TB, openTensorComp,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.ofComponents,
    Iso.trans_hom, Iso.app_hom,
        Functor.mapIso_hom, properOpenDelta_hom, TA', TB', Functor.uncurry_obj_obj,
        Functor.prod_obj, Functor.comp_obj, Functor.id_obj,
        Functor.uncurry_obj_map, NatTrans.id_app, CategoryTheory.Functor.map_id,
        Category.id_comp, Category.comp_id, Category.assoc] using
        properOpenTensor_factorization Λ s b k (pullback.lift_fst k r h) F V
    have result := tensor_square_transport (ProperOpenPull Λ i) Pp (Pq ⋙ S) Pr
      (Pb ⋙ S) (ProperOpenPull Λ k) J (L ⋙ B') K TA' TB' TC TD'
      (properOpenMu Λ p).hom μ₀.hom (properOpenMu Λ r).hom
      (properOpenDelta Λ i).hom δ₀.hom (properOpenDelta Λ k).hom
      α₀ θ₀ θ e t c hmu hθ hδ sq₀ H N₀
    simpa only [properOpenAlpha, a, α₀, e, t, β, ρ, s, b, q, Pq, S, B', L,
      TA', TB', TC, Functor.uncurry_obj_obj, Functor.uncurry_obj_map,
      Functor.prod_obj, Functor.comp_obj, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, properOpenDelta_hom, properOpenMu_hom,
      leftDerivedUpperStarTensorIso_hom, Functor.uncurry_obj_obj,
      Functor.uncurry_obj_map, Functor.map_comp, NatTrans.id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc]
      using result
  have ht := forward_mate_transfer Pr Rr Pp Rp ar ap
    (ProperOpenPull Λ i) (ProperOpenPull Λ k) J K θ
    (Functor.uncurry.obj TA) (Functor.uncurry.obj TB)
    (Functor.uncurry.obj (ProperOpenTensor Λ C)) (Functor.uncurry.obj TD)
    (properOpenMu Λ r).hom (properOpenMu Λ p).hom
    (properOpenDelta Λ i).hom (properOpenDelta Λ k).hom a
    (fun H N₀ ↦ by
      simpa only [properOpenDelta_hom, properOpenMu_hom, leftDerivedUpperStarTensorIso_hom,
        Functor.uncurry_obj_obj, Functor.uncurry_obj_map, Functor.prod_obj,
        CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
        Category.comp_id] using square H N₀) M N
  simpa only [Pr, Rr, Pp, Rp, J, K, ar, ap, a, θ, TA, TB, TD,
    properOpenProjection_tensorSquare, properOpenDelta_hom, properOpenMate,
    properOpenMateTensorMap, Functor.uncurry_obj_obj, Functor.uncurry_obj_map,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Category.comp_id, ProperOpenPull, Functor.comp_obj, eqToHom_refl] using ht

attribute [instance] CategoryTheory.sheafToPresheaf_isRightAdjoint

end ProofHelpers

end AlgebraicGeometry.ProEtale

namespace WeilConjectures.IntegralSystemRealization

section SystemProofHelpers
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions

section Generic
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
private theorem system_mate_tensor_of_exchange
    (Pr : C ⥤ A) (Rr : A ⥤ C) (Pp : D ⥤ B) (Rp : B ⥤ D)
    (Pi : D ⥤ C) (Pk : B ⥤ A) (Ji : C ⥤ D) (Jk : A ⥤ B)
    (ai : Ji ⊣ Pi) (ui : 𝟭 C ≅ Ji ⋙ Pi) (uk : 𝟭 A ≅ Jk ⋙ Pk)
    (hui : ∀ H : C, ui.hom.app H = ai.unit.app H)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (mi : TD ⋙ Pi ≅ Pi.prod Pi ⋙ TC)
    (mk : TB ⋙ Pk ≅ Pk.prod Pk ⋙ TA)
    (di : Ji.prod (𝟭 D) ⋙ TD ≅ (𝟭 C).prod Pi ⋙ TC ⋙ Ji)
    (dk : Jk.prod (𝟭 B) ⋙ TB ≅ (𝟭 A).prod Pk ⋙ TA ⋙ Jk)
    (theta : Pi ⋙ Pr ≅ Pp ⋙ Pk)
    (pir : ∀ (M : A) (N : C), TC.obj (Rr.obj M, N) ⟶ Rr.obj (TA.obj (M, Pr.obj N)))
    (pip : ∀ (M : B) (N : D), TD.obj (Rp.obj M, N) ⟶ Rp.obj (TB.obj (M, Pp.obj N)))
    (pn : ∀ {M M' : A} (f : M ⟶ M') (N : C),
      TC.map (Prod.mkHom (Rr.map f) (𝟙 N)) ≫ pir M' N =
        pir M N ≫ Rr.map (TA.map (Prod.mkHom f (𝟙 (Pr.obj N)))))
    (gamma : Rr ⋙ Ji ⟶ Jk ⋙ Rp) (chi : Rp ⋙ Pi ⟶ Pk ⋙ Rr)
    (lam : (Jk ⋙ Rp) ⋙ Pi ≅ Rr)
    (hg₀ : ∀ M : A, ai.homEquiv _ _ (gamma.app M) = lam.inv.app M)
    (hl : OpenExchangeUnitFormula Jk Rp Pi Pk Rr uk chi lam)
    (hi₀ : ∀ (H : C) (N : D),
      ai.homEquiv _ _ (di.inv.app (H, N)) =
        TC.map (Prod.mkHom (ai.unit.app H) (𝟙 (Pi.obj N))) ≫ mi.inv.app (Ji.obj H, N))
    (hk : ∀ (M : A) (N : B),
      Pk.map (dk.hom.app (M, N)) ≫ uk.inv.app (TA.obj (M, Pk.obj N)) =
        mk.hom.app (Jk.obj M, N) ≫ TA.map (Prod.mkHom (uk.inv.app M) (𝟙 (Pk.obj N))))
    (hc₀ : ∀ (M : B) (N : D),
      Pi.map (pip M N) ≫ chi.app (TB.obj (M, Pp.obj N)) ≫
          Rr.map (mk.hom.app (M, Pp.obj N) ≫
            TA.map (Prod.mkHom (𝟙 (Pk.obj M)) (theta.inv.app N))) =
        mi.hom.app (Rp.obj M, N) ≫
          TC.map (Prod.mkHom (chi.app M) (𝟙 (Pi.obj N))) ≫
          pir (Pk.obj M) (Pi.obj N))
    (M : A) (N : D) :
    di.hom.app (Rr.obj M, N) ≫ Ji.map (pir M (Pi.obj N)) ≫
        Ji.map (Rr.map (TA.map (Prod.mkHom (𝟙 M) (theta.hom.app N)))) ≫
        gamma.app (TA.obj (M, Pk.obj (Pp.obj N))) =
      TD.map (Prod.mkHom (gamma.app M) (𝟙 N)) ≫ pip (Jk.obj M) N ≫
        Rp.map (dk.hom.app (M, Pp.obj N)) := by
  dsimp only [OpenExchangeUnitFormula] at hl
  have hg (M : A) : ui.hom.app (Rr.obj M) ≫ Pi.map (gamma.app M) = lam.inv.app M := by
    simpa only [Adjunction.homEquiv_unit, ← hui] using hg₀ M
  have hi (H : C) (N : D) :
      ui.hom.app (TC.obj (H, Pi.obj N)) ≫ Pi.map (di.inv.app (H, N)) =
        TC.map (Prod.mkHom (ui.hom.app H) (𝟙 (Pi.obj N))) ≫ mi.inv.app (Ji.obj H, N) := by
    simpa only [Adjunction.homEquiv_unit, ← hui, Functor.prod_obj, Functor.id_obj] using hi₀ H N
  have hc : ∀ (M : B) (N : D),
      Pi.map (pip M N) ≫ chi.app (TB.obj (M, Pp.obj N)) ≫
          Rr.map (mk.hom.app (M, Pp.obj N)) =
        mi.hom.app (Rp.obj M, N) ≫
          TC.map (Prod.mkHom (chi.app M) (𝟙 (Pi.obj N))) ≫
          pir (Pk.obj M) (Pi.obj N) ≫
          Rr.map (TA.map (Prod.mkHom (𝟙 (Pk.obj M)) (theta.hom.app N))) := by
    intro M N
    have he := congrArg (fun f ↦ f ≫ Rr.map
      (TA.map (Prod.mkHom (𝟙 (Pk.obj M)) (theta.hom.app N)))) (hc₀ M N)
    have hcancel : TA.map (Prod.mkHom (𝟙 (Pk.obj M)) (theta.inv.app N)) ≫
        TA.map (Prod.mkHom (𝟙 (Pk.obj M)) (theta.hom.app N)) = 𝟙 _ := by
      rw [← TA.map_comp]
      have hp : Prod.mkHom (𝟙 (Pk.obj M)) (theta.inv.app N) ≫
          Prod.mkHom (𝟙 (Pk.obj M)) (theta.hom.app N) =
          𝟙 (Pk.obj M, Pk.obj (Pp.obj N)) := by
        ext <;> simp
      erw [hp, TA.map_id]
    simp only [Functor.map_comp, Category.assoc] at he
    erw [← Rr.map_comp, hcancel, Rr.map_id, Category.comp_id] at he
    exact he
  apply (cancel_epi (di.inv.app (Rr.obj M, N))).1
  simp only [di.inv_hom_id_app_assoc]
  apply (ai.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← hui, Functor.prod_obj, Functor.id_obj]
  have hn₁ := ui.hom.naturality (pir M (Pi.obj N))
  have hn₂ := ui.hom.naturality
    (Rr.map (TA.map (Prod.mkHom (𝟙 M) (theta.hom.app N))))
  dsimp only [Functor.id_map, Functor.comp_map] at hn₁ hn₂
  rw [← reassoc_of% hn₁, ← reassoc_of% hn₂, hg, reassoc_of% (hi (Rr.obj M) N)]
  have hm := mi.inv.naturality (Prod.mkHom (gamma.app M) (𝟙 N))
  dsimp only [Functor.comp_map, Functor.prod_map] at hm
  simp only [Pi.map_id] at hm
  rw [← reassoc_of% hm, ← TC.map_comp_assoc]
  simp only [prod_comp, Category.id_comp, hg]
  apply (cancel_mono (lam.hom.app (TA.obj (M, Pk.obj (Pp.obj N))))).1
  simp only [Category.assoc, lam.inv_hom_id_app, Category.comp_id]
  rw [hl]
  have hn := chi.naturality (dk.hom.app (M, Pp.obj N))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.prod_obj, Functor.id_obj] at hn
  rw [reassoc_of% hn, ← Rr.map_comp, hk, Rr.map_comp]
  rw [reassoc_of% (hc (Jk.obj M) N)]
  simp only [mi.inv_hom_id_app_assoc]
  have ht : TA.map (Prod.mkHom (𝟙 (Pk.obj (Jk.obj M))) (theta.hom.app N)) ≫
      TA.map (Prod.mkHom (uk.inv.app M) (𝟙 (Pk.obj (Pp.obj N)))) =
    TA.map (Prod.mkHom (uk.inv.app M) (𝟙 (Pr.obj (Pi.obj N)))) ≫
      TA.map (Prod.mkHom (𝟙 M) (theta.hom.app N)) := by
    rw [← TA.map_comp, ← TA.map_comp]
    congr 1
    ext <;> simp
  rw [← Rr.map_comp, ht, Rr.map_comp]
  rw [← reassoc_of% (pn (uk.inv.app M) (Pi.obj N))]
  simp only [← TC.map_comp_assoc, prod_comp, ← hl,
    lam.inv_hom_id_app, Category.comp_id]
  rw [← prod_id, TC.map_id, Category.id_comp]

end Generic

section Restrict
variable {C D : Type*} [Category C] [Category D]
private theorem open_tensor_restrict
    (J : C ⥤ D) (P : D ⥤ C) (adj : J ⊣ P) (u : 𝟭 C ≅ J ⋙ P)
    (hu : ∀ M : C, u.hom.app M = adj.unit.app M)
    (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (mu : TD ⋙ P ≅ P.prod P ⋙ TC)
    (delta : J.prod (𝟭 D) ⋙ TD ≅ (𝟭 C).prod P ⋙ TC ⋙ J)
    (h₀ : ∀ (M : C) (N : D),
      adj.homEquiv _ _ (delta.inv.app (M, N)) =
        TC.map (Prod.mkHom (adj.unit.app M) (𝟙 (P.obj N))) ≫ mu.inv.app (J.obj M, N))
    (M : C) (N : D) :
    P.map (delta.hom.app (M, N)) ≫ u.inv.app (TC.obj (M, P.obj N)) =
      mu.hom.app (J.obj M, N) ≫
        TC.map (Prod.mkHom (u.inv.app M) (𝟙 (P.obj N))) := by
  have h (M : C) (N : D) :
      u.hom.app (TC.obj (M, P.obj N)) ≫ P.map (delta.inv.app (M, N)) =
        TC.map (Prod.mkHom (u.hom.app M) (𝟙 (P.obj N))) ≫ mu.inv.app (J.obj M, N) := by
    simpa only [Adjunction.homEquiv_unit, ← hu, Functor.prod_obj, Functor.id_obj] using h₀ M N
  have he : u.app (TC.obj (M, P.obj N)) ≪≫ (P.mapIso (delta.app (M, N))).symm =
      TC.mapIso ((u.app M).prod (Iso.refl (P.obj N))) ≪≫ (mu.app (J.obj M, N)).symm := by
    apply Iso.ext
    exact h M N
  exact congrArg Iso.inv he

end Restrict

/-- The same projection-mate identity, for the intrinsic Gamma of the recorded simultaneous
realization, as equality of maps of unbounded strict semilinear systems before evaluation.
The realization argument supplies canonical operations and their normalized comparisons;
there is no boundedness, normalization or Tor hypothesis on the two input objects.
Source: Stacks 0F7B--0F7D and the node's ringed-diagram-site calculation
(blueprint: lem-sf-proper-open-projection-mate).

Proof: perform Steps 1--6 of the preceding theorem on the ringed diagram sites. In Step 1,
use the clopen lift from lem-cbc-strict-tower-proper-open-calculus. Step 2 restricts the
beta/tensor square to the open and uses full faithfulness and the open-unit normalization
of lem-sf-open-tensor-normalization. Step 3 checks the (identity,zero) clopen projection
on strict complexes, including every coefficient transition, and pastes with Step 2 to
obtain the alpha/tensor square. Step 4 transposes the left composite under the system
proper adjunction and obtains K(a_r) alpha_(R_r M tensor P_i N) P_p(delta_i). Step 5
transposes the right composite: use counit and tensor-comparison naturality, the proper
mate equation and the alpha/tensor square to obtain that same transpose. Step 6 observes
that the operations and comparisons act on all unbounded objects, without inverting
projection or the proper/open comparison.

Step 7 identifies this proper mate with z.properOpen.gamma, using exactly its intrinsic
adjunct characterization: restrict to i, factor k=b s, use the open unit, the clopen
identification J_s=S_s and direct-image composition. The normalized beta and projector
become identity; mate pasting reduces lambda P_i(gamma) to S_r epsilon_r followed by
eta_r S_r, which is identity by the triangle equation. The open Hom bijection makes this
the Gamma_Q of lem-sf-integral-compactification-system-realization.

Step 8 applies the single system adjunction Hom bijection to the equal transposes from
Steps 4--5. The equality is in System l E D, whose objects are derived complexes of strict
semilinear module systems. No evaluation or total-limit functor is applied; no faithfulness
of derived evaluation is assumed. All comparisons are natural in M and N. -/
theorem properOpenProjectionMateSystems
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (o : Operations l E) (z : Realizations l E F o)
    {A B C D : Scheme.{u}}
    [A.Over (Spec (.of F.k))] [B.Over (Spec (.of F.k))]
    [C.Over (Spec (.of F.k))] [D.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (A ↘ Spec (.of F.k))] [QuasiCompact (A ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of F.k))] [QuasiCompact (B ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (C ↘ Spec (.of F.k))] [QuasiCompact (C ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (D ↘ Spec (.of F.k))] [QuasiCompact (D ↘ Spec (.of F.k))]
    (k : A ⟶ B) (r : A ⟶ C) (p : B ⟶ D) (i : C ⟶ D)
    [k.IsOver (Spec (.of F.k))] [r.IsOver (Spec (.of F.k))]
    [p.IsOver (Spec (.of F.k))] [i.IsOver (Spec (.of F.k))]
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : System l E A) (N : System l E D) :
    (z.openComparisons.projection i).hom.app ((Operations.push l E o r).obj M, N) ≫
      (Operations.shriek l E o i).map
        (((properProjection l E o r).app M).app ((pull l E i).obj N)) ≫
      (Operations.shriek l E o i).map ((Operations.push l E o r).map
        ((calculus l E A).systemClosed.tensor.map
          (Prod.mkHom (𝟙 M) ((z.compositors.square l E k r p i h).hom.app N)))) ≫
      (z.properOpen.gamma k r p i h).app
        ((calculus l E A).systemClosed.tensor.obj
          (M, (pull l E k).obj ((pull l E p).obj N))) =
    (calculus l E D).systemClosed.tensor.map
        (Prod.mkHom ((z.properOpen.gamma k r p i h).app M) (𝟙 N)) ≫
      ((properProjection l E o p).app ((Operations.shriek l E o k).obj M)).app N ≫
      (Operations.push l E o p).map
        ((z.openComparisons.projection k).hom.app (M, (pull l E p).obj N)) := by
  refine system_mate_tensor_of_exchange (pull l E r) (Operations.push l E o r)
    (pull l E p) (Operations.push l E o p)
    (pull l E i) (pull l E k) (Operations.shriek l E o i) (Operations.shriek l E o k)
    (o.extension i).adj (z.openComparisons.unit l E o z.compositors i)
    (z.openComparisons.unit l E o z.compositors k) (fun H ↦ rfl)
    (calculus l E A).systemClosed.tensor (calculus l E B).systemClosed.tensor
    (calculus l E C).systemClosed.tensor (calculus l E D).systemClosed.tensor
    (pullbackTensorSystemComparison l E i) (pullbackTensorSystemComparison l E k)
    (z.openComparisons.projection i) (z.openComparisons.projection k)
    (z.compositors.square l E k r p i h)
    (fun M Q ↦ ((properProjection l E o r).app M).app Q)
    (fun M Q ↦ ((properProjection l E o p).app M).app Q)
    ?_ (z.properOpen.gamma k r p i h) (properExchange l E o z.compositors k r p i h)
    (properOpenLambda l E o z.compositors z.openComparisons k r p i h)
    ?_ ?_ ?_ ?_ ?_ M N
  · intro M M' f Q
    have hn := congr_app ((properProjection l E o r).naturality f) Q
    simpa [Functor.comp_map, Functor.curryObj] using hn
  · intro M
    exact z.properOpen.adjunct k r p i h M
  · exact systemProperOpenLambdaExchange l E o z.compositors z.openComparisons k r p i h
  · intro H Q
    exact z.openComparisons.projection_transpose i H Q
  · intro M Q
    exact open_tensor_restrict (Operations.shriek l E o k) (pull l E k)
      (o.extension k).adj (z.openComparisons.unit l E o z.compositors k) (fun H ↦ rfl)
      (calculus l E A).systemClosed.tensor (calculus l E B).systemClosed.tensor
      (pullbackTensorSystemComparison l E k) (z.openComparisons.projection k)
      (fun H Q ↦ z.openComparisons.projection_transpose k H Q) M Q
  · intro M Q
    exact z.ringedTensorCoherence k r p i h M Q

end SystemProofHelpers

end WeilConjectures.IntegralSystemRealization
