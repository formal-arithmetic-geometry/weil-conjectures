/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module
public import Sheaf.Paper.TwistedPullbackScalarFamilies
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Normalized shifts of the completed tensor Tate twist

Source: blueprint sec-smooth-purity/sk-thm-purity-transport, purity transport,
canonical cochain shifts and the degree-zero Tate line
(blueprint: def-pur-twisted-pullback-shift-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.TwistedPullbackScalars
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L)
variable {X X' Y Y' : Scheme.{u}}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ x : X', Invertible (l : X'.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ y : Y', Invertible (l : Y'.residueField y)]
section ShiftNormalization
variable (W : Scheme.{u}) [∀ x : W, Invertible (l : W.residueField x)] (d : ℕ)

/-- The actual tensor twist on integral objects, before raw localization.
Source: purity transport, shift calculation
(blueprint: def-pur-twisted-pullback-shift-normalization). -/
def integralTwist :=
  (𝟭 (sfIntegralConstructibleCategory l E W)).prod'
    ((Functor.const (sfIntegralConstructibleCategory l E W)).obj
      (sfIntegralTwistingCoefficient l E W (d : ℤ))) ⋙ constructibleIntegralTensor l E W

/-- The even shift of the actual integral tensor twist.
Source: purity transport, shift calculation
(blueprint: def-pur-twisted-pullback-shift-normalization). -/
def integralD := integralTwist l E W d ⋙ shiftFunctor _ (2 * (d : ℤ))

/-- The fixed comparison on a good representative: remove completion by its inverse
augmentation, identify the ordinary tensor model, collapse its degree-zero second
factor, and use the termwise derived comparison. Each factor is already specified.
Source: purity transport, Steps 10--11
(blueprint: def-pur-twisted-pullback-shift-normalization). -/
def tensorToTermwiseOnGood
    (P : CochainComplex (integralTowerModules l E W) ℤ)
    (hP : integralOperationsGoodComplex l E W P)
    (hM : finiteTorConstructibleIntegral l E W (DerivedCategory.Q.obj P))
    (hN : finiteTorConstructibleIntegral l E W (sfIntegralTwistingObject l E W (d : ℤ))) :=
  RationalSmoothPurityCanonical.tensorToOrdinaryOnGood l E W P
      (CanonicalTate.integralComplex l E W d) hP (CanonicalTate.integralGood l E W d)
      hM hN ≪≫
    ((RationalSmoothPurityCanonical.ordinaryModel l E W).representative.app
      (⟨P, RationalSmoothPurityCanonical.goodOrdinary l E W P hP⟩,
        ⟨CanonicalTate.integralComplex l E W d,
          RationalSmoothPurityCanonical.goodOrdinary l E W _
            (CanonicalTate.integralGood l E W d)⟩)).symm ≪≫
    DerivedCategory.Q.mapIso
      (CochainComplex.mapBifunctorSingle₂Iso
        (proEtaleOrdinaryTensor W (completedIntegralCommRingSheafUnrestricted l E W))
        (integralTwistLine l E W (d : ℤ)) P) ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex
        (SheafOfModules.siteSheafTensorRightIso
          (completedIntegralCommRingSheafUnrestricted l E W)
          (integralTwistLine l E W (d : ℤ))).symm (.up ℤ)).app P) ≪≫
    ((integralSheafTwist l E W (d : ℤ)).mapDerivedCategoryFactors.app P).symm

/-- Tensor-to-termwise comparison after the actual full-subcategory shift.
Source: purity transport, normalization of the common even shift
(blueprint: def-pur-twisted-pullback-shift-normalization). -/
def shiftedBetaFrom
    (beta : ∀ K : sfIntegralConstructibleCategory l E W,
      ((integralTwist l E W d).obj K).obj ≅
        (sfIntegralTwistingFunctor l E W (d : ℤ)).obj K.obj)
    (K : sfIntegralConstructibleCategory l E W) :=
  ((sfIntegralConstructible l E W).ι.commShiftIso (2 * (d : ℤ))).app
      ((integralTwist l E W d).obj K) ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso (beta K)

/-- Canonical shift data for D. The comparison with termwise twist is fixed on every
flat K-flat representative, and integral and rational shifts are pinned by it.
These are conclusions of the theorem, never extra hypotheses on the square.
Source: purity transport, canonical cochain shifts and degree-zero line
(blueprint: def-pur-twisted-pullback-shift-normalization). -/
structure ShiftData where
  beta : ∀ K : sfIntegralConstructibleCategory l E W,
    ((integralTwist l E W d).obj K).obj ≅ (sfIntegralTwistingFunctor l E W (d : ℤ)).obj K.obj
  beta_naturality : ∀ (K N : sfIntegralConstructibleCategory l E W) (b : K ⟶ N),
    ((integralTwist l E W d).map b).hom ≫ (beta N).hom =
      (beta K).hom ≫ (sfIntegralTwistingFunctor l E W (d : ℤ)).map b.hom
  beta_normalization : ∀
    (P : CochainComplex (integralTowerModules l E W) ℤ)
    (hP : integralOperationsGoodComplex l E W P)
    (hK : sfIntegralConstructible l E W (DerivedCategory.Q.obj P))
    (hM : finiteTorConstructibleIntegral l E W (DerivedCategory.Q.obj P))
    (hN : finiteTorConstructibleIntegral l E W (sfIntegralTwistingObject l E W (d : ℤ))),
    HEq (beta ⟨DerivedCategory.Q.obj P, hK⟩).hom
      (tensorToTermwiseOnGood l E W d P hP hM hN).hom
  integralShift : (integralD l E W d).CommShift ℤ
  integral_normalization : ∀ (K : sfIntegralConstructibleCategory l E W) (n : ℤ),
    HEq (((Functor.commShiftIso (integralD l E W d)
      (self := integralShift) n).hom.app K).hom)
      ((shiftedBetaFrom l E W d beta (K⟦n⟧)).hom ≫
        (sfIntegralTwistingFunctor l E W (d : ℤ) ⋙
          shiftFunctor _ (2 * (d : ℤ))).map
            (((sfIntegralConstructible l E W).ι.commShiftIso n).hom.app K) ≫
        (((sfIntegralTwistingFunctor l E W (d : ℤ) ⋙
          shiftFunctor _ (2 * (d : ℤ))).commShiftIso n).hom.app K.obj) ≫
        (shiftFunctor _ n).map (shiftedBetaFrom l E W d beta K).inv ≫
        (((sfIntegralConstructible l E W).ι.commShiftIso n).inv.app
          ((integralD l E W d).obj K)))
  rationalShift : (D l E W d).CommShift ℤ
  rational_normalization : ∀ (K : sfIntegralConstructibleCategory l E W) (n : ℤ),
    HEq ((Functor.commShiftIso (D l E W d) (self := rationalShift) n).hom.app
      ((sfRationalConstructibleLocalization l E W).obj K))
      ((sfRationalConstructibleLocalization l E W).map
        ((Functor.commShiftIso (integralD l E W d) (self := integralShift) n).hom.app K))

end ShiftNormalization

section FamilyShifts
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Component form of w_(K[n])=w_K[n] under the specified canonical shifts.
Source: purity transport, shift clause
(blueprint: def-pur-twisted-pullback-shift-normalization). -/
def ShiftCompatible {A B : Scheme.{u}} (F : Family l Ω A B)
    (s : ∀ R : Fields l Ω, (F.F R).CommShift ℤ) : Prop :=
  ∀ (R S : Fields l Ω) (h : R ≤ S) (n : ℤ)
    (K : sfRationalConstructibleCategory l R.val A),
    (F.w R S h (K⟦n⟧)).hom ≫
      (F.F S).map ((Functor.commShiftIso
        (T l R.val S.val (IntermediateField.inclusion h) A)
        (self := RationalSmoothPurityCanonical.scalarShift l R.val S.val
          (IntermediateField.inclusion h) A) n).hom.app K) ≫
      (Functor.commShiftIso (F.F S) (self := s S) n).hom.app
        ((T l R.val S.val (IntermediateField.inclusion h) A).obj K) =
    (T l R.val S.val (IntermediateField.inclusion h) B).map
        ((Functor.commShiftIso (F.F R) (self := s R) n).hom.app K) ≫
      (Functor.commShiftIso (T l R.val S.val (IntermediateField.inclusion h) B)
        (self := RationalSmoothPurityCanonical.scalarShift l R.val S.val
          (IntermediateField.inclusion h) B) n).hom.app ((F.F R).obj K) ≫
      (F.w R S h K).hom⟦n⟧'

/-- Composition of specified shift structures, as used for all composite families.
Source: purity transport, shift clause
(blueprint: def-pur-twisted-pullback-shift-normalization). -/
abbrev composeShift := @AdicPurityScalarNaturality.composeShift

end FamilyShifts
end WeilConjectures.TwistedPullbackScalars
