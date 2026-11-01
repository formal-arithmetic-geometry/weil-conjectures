/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperCoefficientOperations
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackExactCounits
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackCoefficientMap
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.NativeIntegralCoefficientFlat
import all WeilConjectures.WeilSheaf.Ordinary.OrdinaryIntegralPullbackConstruction

/-! # Derived finite integral balance with its representative equation

Source: Bhatt--Scholze, Remark 6.8.15; Stacks Tags 03EK and 06YY.
(blueprint: lem-sf-native-pullback-integral-derived-balance)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper
open AlgebraicallyClosedCoefficients (Index Coefficient)

private def scalarCounitNat {X : Scheme.{u}}
    {A B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (c : A ⟶ B) :
    DerivedCategory.Q ⋙ pbcDerivedExtend c ⟶
      (pbcExtend c).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv (pbcDerivedExtend c) ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ _) (pbcExtensionCounit c) ≫
    Functor.whiskerRight ((pbcExtend c).mapHomotopyCategoryFactors (.up ℤ)).hom
      DerivedCategory.Qh ≫
    Functor.whiskerLeft ((pbcExtend c).mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso _).hom

set_option maxHeartbeats 1600000 in
-- The final representative equation unfolds the two composite computation counits.
/-- Any ordinary balanced comparison has a derived comparison normalized on every
cochain representative. Source: Bhatt--Scholze, Remark 6.8.15; Stacks Tag 06YY.
(blueprint: lem-sf-native-pullback-integral-derived-balance).

Proof: the integral coefficient inclusions are flat on noetherian schemes, so their
ordinary scalar extensions are exact. Ordinary integral pullback and native inverse
image are exact too. Consequently all four published computation counits are
invertible on every cochain complex. Compose the first pair, the localization of the
ordinary balanced isomorphism, and the inverse of the second pair. This is a natural
isomorphism after precomposition with cochain localization. Localization's fully
faithful precomposition functor descends it uniquely. Its component equation cancels
the second pair of counits and gives exactly the displayed representative square.
This treats unbounded complexes, without choosing resolutions or bounded truncations. -/
theorem nativePullbackIntegralDerivedBalance (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (p : X ⟶ Y)
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    (O : Operations l p R S) (E : Index l (PadicAlgCl l))
    (b : ordinaryIntegralModulePull l (Coefficient.{u} l (PadicAlgCl l) E) p ⋙
        pbcExtend (coefficientMap l X R E) ≅
      pbcExtend (coefficientMap l Y S E) ⋙ ContinuousRational.modulePull p O.coefficient) :
    ∃ d : ordinaryIntegralDerivedPull l (Coefficient.{u} l (PadicAlgCl l) E) p ⋙
          pbcDerivedExtend (coefficientMap l X R E) ≅
        pbcDerivedExtend (coefficientMap l Y S E) ⋙
          ContinuousRational.derivedPull p O.coefficient,
      ∀ P : CochainComplex (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) Y) ℤ,
      d.hom.app (DerivedCategory.Q.obj P) ≫
        (ContinuousRational.derivedPull p O.coefficient).map
          (pbcComplexCounit (coefficientMap l Y S E) P) ≫
        O.pullCounit.app ((integralComplex l Y S E).obj P) =
      (pbcDerivedExtend (coefficientMap l X R E)).map
          (ordinaryIntegralPullComplexCounit l (Coefficient.{u} l (PadicAlgCl l) E) p P) ≫
        pbcComplexCounit (coefficientMap l X R E)
          ((ordinaryIntegralPullComplex l (Coefficient.{u} l (PadicAlgCl l) E) p).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app P) := by
  let K := Coefficient.{u} l (PadicAlgCl l) E
  let aX := coefficientMap l X R E
  let aY := coefficientMap l Y S E
  let := R.commutative
  let := S.commutative
  have : PreservesFiniteLimits (pbcExtend aX) :=
    LocallyFiniteAdicRealization.nativeIntegralCoefficient_flat l X K
      (LocallyFiniteAdicRealization.embedding l E) (R.coefficient E)
  have : PreservesFiniteLimits (pbcExtend aY) :=
    LocallyFiniteAdicRealization.nativeIntegralCoefficient_flat l Y K
      (LocallyFiniteAdicRealization.embedding l E) (S.coefficient E)
  have : PreservesColimitsOfSize.{0, 0} (pbcExtend aX) :=
    (pbcScalarAdjunction aX).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{0, 0} (pbcExtend aY) :=
    (pbcScalarAdjunction aY).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (pbcExtend aX) := inferInstance
  have : PreservesFiniteColimits (pbcExtend aY) := inferInstance
  have := nativePullbackCoefficient_isIso l p R S O
  have (P : CochainComplex (integralTowerModules l K Y) ℤ) :
      IsIso ((ordinaryIntegralComplexCounitNat l K p).app P) :=
    nativePullbackIntegralCounit_isIso l K p P
  have {W : Scheme.{u}} {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
      (c : A ⟶ B) [PreservesFiniteLimits (pbcExtend c)]
      [PreservesFiniteColimits (pbcExtend c)] : IsIso (scalarCounitNat c) := by
    exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (scalarCounitNat c)
      (fun P ↦ nativePullbackScalarCounit_isIso c P)
  have : IsIso (ordinaryIntegralComplexCounitNat l K p) :=
    NatIso.isIso_of_isIso_app _
  have : IsIso O.pullCounit :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ O.pullCounit
      (fun P ↦ nativePullbackNormalizedCounit_isIso p O.coefficient O.pullCounit
        O.pull_normalized P)
  let L := ordinaryIntegralDerivedPull l K p ⋙ pbcDerivedExtend aX
  let H := pbcDerivedExtend aY ⋙ ContinuousRational.derivedPull p O.coefficient
  let βL : DerivedCategory.Q ⋙ L ⟶
      ((ordinaryIntegralModulePull l K p ⋙ pbcExtend aX).mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q :=
    Functor.whiskerRight (ordinaryIntegralComplexCounitNat l K p) (pbcDerivedExtend aX) ≫
      Functor.whiskerLeft (ordinaryIntegralPullComplex l K p) (scalarCounitNat aX)
  let βH : DerivedCategory.Q ⋙ H ⟶
      ((pbcExtend aY ⋙ ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex
        (.up ℤ)) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (scalarCounitNat aY)
        (ContinuousRational.derivedPull p O.coefficient) ≫
      Functor.whiskerLeft ((pbcExtend aY).mapHomologicalComplex (.up ℤ)) O.pullCounit
  let γ : DerivedCategory.Q ⋙ L ≅ DerivedCategory.Q ⋙ H :=
    asIso βL ≪≫ Functor.isoWhiskerRight (NatIso.mapHomologicalComplex b (.up ℤ))
      DerivedCategory.Q ≪≫ (asIso βH).symm
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (integralTowerModules l K Y) (.up ℤ))
    (DerivedCategory (modules l X R))
  let d : L ≅ H := ff.preimageIso γ
  refine ⟨d, ?_⟩
  intro P
  have h := congrArg (fun t ↦ t.app P) (ff.map_preimage γ.hom)
  change d.hom.app (DerivedCategory.Q.obj P) =
    βL.app P ≫ DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app P) ≫
      (asIso βH).inv.app P at h
  have hi : (asIso βH).inv.app P ≫ βH.app P = 𝟙 _ :=
    (asIso βH).inv_hom_id_app P
  have hc : d.hom.app (DerivedCategory.Q.obj P) ≫ βH.app P =
      βL.app P ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app P) := by
    rw [h, Category.assoc, Category.assoc, hi]
    exact congrArg (fun f ↦ βL.app P ≫ f)
      (Category.comp_id (DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app P)))
  have hβL : βL.app P = (pbcDerivedExtend aX).map
      (ordinaryIntegralPullComplexCounit l K p P) ≫ pbcComplexCounit aX
        ((ordinaryIntegralPullComplex l K p).obj P) := rfl
  have hβH : βH.app P = (ContinuousRational.derivedPull p O.coefficient).map
      (pbcComplexCounit aY P) ≫ O.pullCounit.app ((integralComplex l Y S E).obj P) := rfl
  simpa only [hβL, hβH, Category.assoc] using hc

end WeilConjectures.AdicQbarRealization.Proper
