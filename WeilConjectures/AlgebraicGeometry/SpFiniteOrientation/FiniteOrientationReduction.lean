/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRing
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import WeilConjectures.AlgebraicGeometry.SpFiniteOrientation.CoefficientUnitTowerNormalized
import all WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationTensorComplex
import all WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionCompatibilities
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence

/-! # Finite diagonal orientations at the unit and under reduction

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md, (1)--(3)
(blueprint: lem-sp-finite-orientation-reduction).

The natural index n means the positive coefficient exponent n+1. All ordinary-etale
arrows below are the recorded presentations of the finite pro-etale arrows, with
coefficient units identified by their multiplication and pullback constraints.
An orientation parameter is constrained by the dependency's diagonal/DNC normalization;
it is a presentation of the specified orientation, never a freely chosen endpoint iso.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme WeilConjectures
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.SpFiniteOrientation

/-- The positive-level uniformizer presentation; it keeps the fixed field and extension.
Source: gamma proof (1), R_n=A_(E,en)
(blueprint: lem-sp-finite-orientation-reduction). -/
def setting (P : PurityFiniteSetting.{u}) (e : ℕ) (he : 1 ≤ e) (n : ℕ) :
    PurityFiniteSetting.{u} :=
  { P with level := e * (n + 1), level_pos := Nat.mul_pos he (Nat.succ_pos n) }

/-- Equality of the actual quotient ideals, including ramification.
Source: gamma proof (1), ell=u varpi^e
(blueprint: lem-sp-finite-orientation-reduction).
Proof: the unit factor generates the unit ideal. Thus (ell)=(varpi)^e.
Raise this equality to n+1 and use the ideal-power multiplication formula. -/
theorem coefficient_ideal (P : PurityFiniteSetting.{u}) (e : ℕ)
    (v : (Padic.coefficientExtensionIntegers P.coefficients.l P.extension)ˣ)
    (_hv : (P.coefficients.l : Padic.coefficientExtensionIntegers
      P.coefficients.l P.extension) = v *
        Padic.coefficientExtensionUniformizer P.coefficients.l P.extension ^ e) (n : ℕ) :
    spEllIdeal P.coefficients.l P.extension ^ (n + 1) =
      Padic.coefficientExtensionIdeal P.coefficients.l P.extension (e * (n + 1)) := by
  unfold spEllIdeal Padic.coefficientExtensionIdeal
  rw [_hv, Ideal.span_singleton_mul_left_unit v.isUnit,
    ← Ideal.span_singleton_pow, ← pow_mul]

/-- The canonical coefficient equivalence, induced by the identity on O_E.
Source: gamma proof (1), quotient identification
(blueprint: lem-sp-finite-orientation-reduction). -/
def coefficientEquiv (P : PurityFiniteSetting.{u}) (e : ℕ) (he : 1 ≤ e)
    (v : (Padic.coefficientExtensionIntegers P.coefficients.l P.extension)ˣ)
    (hv : (P.coefficients.l : Padic.coefficientExtensionIntegers
      P.coefficients.l P.extension) = v *
        Padic.coefficientExtensionUniformizer P.coefficients.l P.extension ^ e) (n : ℕ) :
    SpTowerShriek.R P.coefficients.l P.extension n ≃+* (setting P e he n).Ring :=
  Ideal.quotEquivOfEq (coefficient_ideal P e v hv n)

/-- The inverse diagonal comparison with the tensor unit as coefficient object.
Only the canonical single-complex unit comparison changes the source coordinates.
Source: gamma proof (1), finite diagonal orientation
(blueprint: lem-sp-finite-orientation-reduction). -/
def ordinaryOrientation (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (d : ℕ)
    (alpha : P.diagonalOrdinaryDualizing f ≅ P.diagonalTwistEtale X d) :
    Etale.dualizingComplex P.Coefficient f ≅
      P.diagonalTwistEtale X d :=
  (Etale.rightDerivedUpperShriek P.Coefficient f).mapIso
    (PurityFiniteSetting.smoothPurityUnitIso P.Coefficient Y).symm ≪≫ alpha

private theorem tensor_mate_unit
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : D ⥤ C} {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (π : ∀ (M : C) (N : D), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N))
    [∀ M N, IsIso (π M N)] (u : F.obj (𝟙_ D) ≅ 𝟙_ C)
    (hπ : π (R.obj (𝟙_ D)) (𝟙_ D) ≫
      L.map (R.obj (𝟙_ D) ◁ u.hom ≫ (ρ_ (R.obj (𝟙_ D))).hom) =
        (ρ_ (L.obj (R.obj (𝟙_ D)))).hom) :
    adj.projectionTensorMap π (𝟙_ D) (𝟙_ D) ≫ R.map (λ_ (𝟙_ D)).hom =
      R.obj (𝟙_ D) ◁ u.hom ≫ (ρ_ (R.obj (𝟙_ D))).hom := by
  apply Adjunction.ext_of_comp_counit (adj := adj)
  rw [Functor.map_comp, Category.assoc]
  erw [adj.counit_naturality]
  rw [Adjunction.map_projectionTensorMap_comp_counit_assoc]
  apply (cancel_epi (π (R.obj (𝟙_ D)) (𝟙_ D))).1
  simp only [IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, hπ]
  simpa only [Functor.comp_obj, Functor.id_obj, unitors_equal] using
    (rightUnitor_naturality (adj.counit.app (𝟙_ D)))

private theorem gamma_unit
    {C : Type*} [Category* C] [MonoidalCategory C]
    {P W L : C} (u : P ≅ 𝟙_ C) (alpha : W ≅ L) (theta : P ⊗ W ⟶ W)
    (h : u.inv ▷ W ≫ theta = (λ_ W).hom) :
    (λ_ L).inv ≫ u.inv ▷ L ≫ P ◁ alpha.inv ≫ theta = alpha.inv := by
  rw [← whisker_exchange_assoc, h]
  simp

universe uA

private theorem tensor_unit_general
    {A : Type uA} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
    {FC : A → A → Type (u + 1)} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [HasCompactification f]
    [IsIso (Etale.projectionMap A f)]
    {G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (adj : Etale.rightDerivedLowerShriek A f ⊣ G) :
    Etale.lowerShriekRightAdjointUnitTensorMap adj (𝟙_ _) =
      G.obj (𝟙_ _) ◁ (Etale.leftDerivedUpperStarUnitIso A f).hom ≫ (ρ_ (G.obj (𝟙_ _))).hom :=
  tensor_mate_unit adj
    (fun M N ↦ ((Etale.projectionMap A f).app M).app N)
    (Etale.leftDerivedUpperStarUnitIso A f) (Etale.projectionMap_rightUnitality A f _)

section
open AlgebraicGeometry.Etale
open scoped AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

private theorem tensor_unit :
    Etale.dualizingComplexTensorMap Λ f (𝟙_ _) =
      (Etale.dualizingComplex Λ f) ◁
          (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) f).hom ≫
        (ρ_ (Etale.dualizingComplex Λ f)).hom := by
  exact tensor_unit_general (Etale.rightDerivedUpperShriekAdjunction Λ f)
private theorem tensor_naturality
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (g : K ⟶ K') :
    ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj (Etale.dualizingComplex Λ f)).map
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.map g) ≫
        Etale.dualizingComplexTensorMap Λ f K' =
      Etale.dualizingComplexTensorMap Λ f K ≫
        (Etale.rightDerivedUpperShriek Λ f).map g := by
  let := Etale.derivedBraidedCategory Λ X
  have h := Adjunction.projectionTensorMap_naturality_right
    (Etale.rightDerivedUpperShriekAdjunction Λ f)
    (fun M N ↦ ((Etale.projectionMap (ModuleCat.{u + 1} Λ) f).app M).app N)
    (Etale.projectionMap_app_app_naturality_right f) (𝟙_ _) g
  dsimp only [Etale.dualizingComplexTensorMap, Etale.lowerShriekRightAdjointUnitTensorMap]
  rw [← Category.assoc]
  erw [h]
  simp only [Category.assoc, ← Functor.map_comp]
  exact congrArg (fun k ↦ _ ≫ (Etale.rightDerivedUpperShriek Λ f).map k)
    (leftUnitor_naturality g)

end

/-- The fixed-ring source identification at the coefficient unit: pull back the
single-complex unit, identify the pulled-back unit, then apply the left unitor.
Source: gamma proof (2), tensor-unit identifications
(blueprint: lem-sp-finite-orientation-reduction). -/
def sourceUnitIso (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Etale.DerivedCategoryModule A X) :
    ((Etale.ordinaryFiniteTensor A X).obj
      ((Etale.ordinaryFinitePullback A f).obj (Etale.ordinaryFiniteUnit A Y))).obj L ≅ L :=
  ((Etale.ordinaryFiniteTensor A X).mapIso
    ((Etale.ordinaryFinitePullback A f).mapIso
      (PurityFiniteSetting.smoothPurityUnitIso A Y) ≪≫
      Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f)).app L ≪≫ λ_ L

end AlgebraicGeometry.ProEtale.SpFiniteOrientation

namespace AlgebraicGeometry.ProEtale.SpFiniteOrientation

private def pushforwardUnitIso
    {C D : Type*} [Category* C] [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{u})
    (S : Sheaf J RingCat.{u})
    (h : S = (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    (SheafOfModules.pushforward.{u} (eqToHom h)).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit S := by
  subst S
  exact Iso.refl _

private def evaluationUnitIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :
    (SpTowerShriek.ev l E T n).obj (SpTowerClasses.coefficient T
      (SpTowerClasses.Arings l E T)) ≅
    SheafOfModules.unit ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing T (SpTowerShriek.R l E n))) := by
  exact pushforwardUnitIso _ _ _
    (SemilinearSections.evaluation_ring (ProEt.topology T)
      (fun n ↦ SpTowerShriek.B l E T n) (SpTowerShriek.tau l E T) n).symm

private theorem isIso_app_of_iso
    {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (τ : F ⟶ G) {K L : C} (e : K ≅ L)
    [IsIso (τ.app L)] : IsIso (τ.app K) := by
  exact IsIso.of_isIso_fac_right (τ.naturality e.hom).symm

end AlgebraicGeometry.ProEtale.SpFiniteOrientation
