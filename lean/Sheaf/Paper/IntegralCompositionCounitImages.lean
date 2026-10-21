/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.Paper.IntegralTowerInverseImageUnit
public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.Paper.IntegralPullbackResolutionMatching
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition

/-!
# The whole-tower counit images of integral comparison composites

Source: blueprint `sec-trace-formula/sk-thm-trace-transport/`
`thm-trf-l-function-euler-product.proof.md`, Step 1, Global powers;
Stacks Project, Tag 0941 (blueprint: lem-trf-integral-composition-counit-images).

Strict quotient presentations and their canonical localization comparisons are explicit.
The two equalities have the same inverse-image resolution denominator. Positive
exponent m is represented by n = m - 1, including exponent one.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual finite pullback tower of a strict quotient presentation, as a complex
of completed-module towers. Source: blueprint Global powers; Stacks 0941
(blueprint: lem-trf-integral-composition-counit-images). -/
abbrev integralCounitImagesTower {Y X : Scheme.{u}} (g : X ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :=
  ((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
    (((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)).obj C)

/-- The actual iterated finite pullback tower, with all quotient transitions.
Source: blueprint Global powers; Stacks 0941
(blueprint: lem-trf-integral-composition-counit-images). -/
abbrev integralCounitImagesDoubleTower {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V)
    (C : CochainComplex (coefficientSequenceModules l E V) ℤ) :=
  integralCounitImagesTower l E h
    (((integralComparisonSequencePullback l E k).mapHomologicalComplex (.up ℤ)).obj C)

/-- Localization of the iterated strict tower, using the canonical comparisons at
both pullbacks and scalar restriction. Source: blueprint Global powers; Stacks 0941
(blueprint: lem-trf-integral-composition-counit-images). -/
def integralCounitImagesDoublePresentation {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) (A : coefficientSequenceDerived l E V)
    (C : CochainComplex (coefficientSequenceModules l E V) ℤ)
    (e : A ≅ DerivedCategory.Q.obj C) :
    (coefficientSequenceDerivedRestriction l E Z).obj
        ((integralComparisonDerivedSequencePullback l E h).obj
          ((integralComparisonDerivedSequencePullback l E k).obj A)) ≅
      DerivedCategory.Q.obj (integralCounitImagesDoubleTower l E h k C) :=
  (coefficientSequenceDerivedRestriction l E Z).mapIso
    ((integralComparisonDerivedSequencePullback l E h).mapIso
      ((integralComparisonDerivedSequencePullback l E k).mapIso e ≪≫
        (integralComparisonSequencePullback l E k).mapDerivedCategoryFactors.app C) ≪≫
      (integralComparisonSequencePullback l E h).mapDerivedCategoryFactors.app _) ≪≫
    (coefficientSequenceRestriction l E Z).mapDerivedCategoryFactors.app _

/-- The strict tensor unit is specified on every section, after the chosen
identification of the quotient presentation with P tensor A_n. This condition fixes
an entire strict tower map, including compatibility with transitions.
Source: blueprint Global powers; Stacks 03D6, 0941
(blueprint: lem-trf-integral-composition-counit-images). -/
def IntegralCounitImagesTheta {Y X : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj P)
    (θ : ((Functor.const ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).obj
        (((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      integralCounitImagesTower l E g C) : Prop :=
  ∀ (n : ℕ) (i : ℤ) (U : X.ProEt)
    (x : (P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
    ((θ.f i).app (op n)).val.app (op U) x =
      integralComparisonRestrictedSection l E X
        ((integralComparisonSequencePullback l E g).obj (C.X i)) n (op U)
        (((integralComparisonSequencePullback l E g).obj (C.X i)).val.map
          (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
          (integralComparisonSequenceGenerator l E g (C.X i) n
            ((proEtaleIsoPostcompose g).obj U)
            (integralComparisonSequenceSection l E Y (C.X i) n
              (op ((proEtaleIsoPostcompose g).obj U))
              (((κ n).inv.f i).val.app (op ((proEtaleIsoPostcompose g).obj U))
                (unrestrictedIntegralTensorSection l E Y n (P.X i)
                  (op ((proEtaleIsoPostcompose g).obj U)) 1 x)))))

/-- Localize that strict unit with the canonical exact-functor endpoint comparisons.
Source: blueprint Global powers; Stacks 05RU, 0941
(blueprint: lem-trf-integral-composition-counit-images). -/
def integralCounitImagesThetaDerived {Y X : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (θ : ((Functor.const ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).obj
        (((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      integralCounitImagesTower l E g C) :
    (integralComparisonConstantTower l E X).obj
        ((inverseImageIntegralDerived l E g).obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj (integralCounitImagesTower l E g C) :=
  (integralComparisonConstantTower l E X).map
      ((inverseImageIntegralModules l E g).mapDerivedCategoryFactors.hom.app P) ≫
    (Functor.const ℕᵒᵖ : integralTowerModules l E X ⥤ _).mapDerivedCategoryFactors.hom.app _ ≫
    DerivedCategory.Q.map θ

/-- Transport a quotient presentation through the one resolution denominator.
Source: blueprint Global powers; Stacks 05RU, 0941
(blueprint: lem-trf-integral-composition-counit-images). -/
def integralCounitImagesResolutionPresentation {V : Scheme.{u}}
    (S : CoefficientDerivedSystemCalculus l E V)
    {P K : CochainComplex (integralTowerModules l E V) ℤ}
    (q : P ⟶ K) [QuasiIso q]
    (C : CochainComplex (coefficientSequenceModules l E V) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C) :
    S.reduction.obj (DerivedCategory.Q.obj K) ≅ DerivedCategory.Q.obj C :=
  (S.reduction.mapIso (asIso (DerivedCategory.Q.map q))).symm ≪≫ e

/-- Both counit images, as equalities in the derived category of entire strict
completed-module towers. The normalized presentations transport the system models
back to the actual quotient tower of the common chosen resolution q.

Source: blueprint `sec-trace-formula/sk-thm-trace-transport/`
`thm-trf-l-function-euler-product.proof.md`, Step 1, Global powers;
Stacks Project, Tag 0941 (blueprint: lem-trf-integral-composition-counit-images).

Proof, following the five DAG steps:
1. Exactness of completed inverse image makes HG(q) and J(q) invertible after
   localization. The finite coefficient composition formula of
   lem-trf-constant-coefficient-composition, projected to every quotient, gives
   completed linearity of the section-normalized compositor d. Naturality at q
   gives J(q) inverse followed by d_K = d_P followed by HG(q) inverse.
2. Apply lem-trf-integral-comparison-counit-characterization to kh and k, using
   the same q and the actual quotient presentation C. Its whole-tower equations
   identify the counit of kappa with the localized strict theta and its inverse
   resolution denominator. The presentation and exact-functor comparisons merely
   identify the endpoints of these equations.
3. Counit naturality at the finite pullback compositor, and the definition
   eta after c^E = Rlim(c), give the first equality. Use step 1 to move the
   compositor across the inverse resolution. Here c^E followed by eta is expanded
   using integralComparisonComposition, so no freely chosen comparison appears.
4. Apply lem-trf-integral-pullback-resolution-matching to h,k and the same input.
   This computes the counit of eta after kappa_h as the strict tower unit after
   inverse image of the original tower counit.
5. Precompose step 4 with Delta H(kappa_k). Commute exact inverse image with
   Delta using integralTowerInverseImageDiagonal, and apply it to step 2 for k.
   Functoriality preserves the common inverse HG(q), proving the second equation.
   These are whole-tower equalities; no separate evaluation is cancelled. -/
theorem integralCompositionCounitImages
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : IntegralComparisonSystem.{u} l)
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k]
    (hV : ∀ v : V, IsUnit (l : V.presheaf.stalk v))
    (hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w))
    (hZ : ∀ z : Z, IsUnit (l : Z.presheaf.stalk z))
    (K : CochainComplex (integralTowerModules l E V) ℤ)
    (hK : sfIntegralConstructible l E V (DerivedCategory.Q.obj K))
    (P : (integralOperationsGoodComplex l E V).FullSubcategory)
    (q : P.obj ⟶ K) [QuasiIso q]
    (C : CochainComplex (coefficientSequenceModules l E V) ℤ)
    (e : ((D.coefficient E).system V).reduction.obj (DerivedCategory.Q.obj P.obj) ≅
      DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E V n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E V n).obj P.obj)
    (hC : CoefficientReductionPresentation l E V
      ((D.coefficient E).system V).toCoefficientDerivedSystemReduction P.obj P.property.1 C e κ)
    (d : inverseImageIntegralModules l E k ⋙ inverseImageIntegralModules l E h ≅
      inverseImageIntegralModules l E (h ≫ k))
    (hd : ∀ (F : integralTowerModules l E V) (U : Z.ProEt)
      (x : F.val.obj (op ((proEtaleIsoPostcompose k).obj
        ((proEtaleIsoPostcompose h).obj U)))),
      (d.hom.app F).val.app (op U) x =
        F.val.map ((MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale k)).hom.app U).op x)
    (θk : ((Functor.const ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).obj
        (((inverseImageIntegralModules l E k).mapHomologicalComplex (.up ℤ)).obj P.obj) ⟶
      integralCounitImagesTower l E k C)
    (hθk : IntegralCounitImagesTheta l E k P.obj C κ θk)
    (θkh : ((Functor.const ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).obj
        (((inverseImageIntegralModules l E (h ≫ k)).mapHomologicalComplex (.up ℤ)).obj P.obj) ⟶
      integralCounitImagesTower l E (h ≫ k) C)
    (hθkh : IntegralCounitImagesTheta l E (h ≫ k) P.obj C κ θkh) :
    ((integralComparisonConstantTower l E Z).map
        ((Functor.mapDerivedCategoryCompIso (inverseImageIntegralModules l E k)
            (inverseImageIntegralModules l E h)).inv.app (DerivedCategory.Q.obj K) ≫
          (Functor.mapDerivedCategoryNatIso d).hom.app (DerivedCategory.Q.obj K) ≫
          inverseImagePullbackComparison l E (h ≫ k) hZ hV K P q ≫
          ((D.coefficient E).pullback (h ≫ k)).realization.hom.app (DerivedCategory.Q.obj K) ≫
          (coefficientSequenceLimit l E Z).map
            ((integralComparisonSystemComposition l E h k).hom.app
              (((D.coefficient E).system V).reduction.obj (DerivedCategory.Q.obj K))) ≫
          (coefficientConstantTowerLimit l E Z).map
            (integralCounitImagesDoublePresentation l E h k _ C
              (integralCounitImagesResolutionPresentation l E ((D.coefficient E).system V)
                q C e)).hom) ≫
        (integralComparisonTowerCounit l E Z).app
          (DerivedCategory.Q.obj (integralCounitImagesDoubleTower l E h k C)) =
      (integralComparisonConstantTower l E Z).map
          (inv ((inverseImageIntegralDerived l E h).map
            ((inverseImageIntegralDerived l E k).map (DerivedCategory.Q.map q)))) ≫
        (integralComparisonConstantTower l E Z).map
          ((Functor.mapDerivedCategoryCompIso (inverseImageIntegralModules l E k)
              (inverseImageIntegralModules l E h)).inv.app (DerivedCategory.Q.obj P.obj) ≫
            (Functor.mapDerivedCategoryNatIso d).hom.app (DerivedCategory.Q.obj P.obj)) ≫
        integralCounitImagesThetaDerived l E (h ≫ k) P.obj C θkh ≫
        DerivedCategory.Q.map
          (((coefficientSequenceRestriction l E Z).mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex
              (integralComparisonSequenceComposition l E h k).hom (.up ℤ)).app C))) ∧
    ((integralComparisonConstantTower l E Z).map
        ((inverseImageIntegralDerived l E h).map
            (inverseImagePullbackComparison l E k hW hV K P q) ≫
          inverseImagePullbackComparisonDerived l E h hZ hW
            ((integralDerivedPullback l E k).obj (DerivedCategory.Q.obj K)) ≫
          (integralResolutionMatchingEta l E D h k hV hW hZ
            ⟨DerivedCategory.Q.obj K, hK⟩).hom ≫
          (coefficientConstantTowerLimit l E Z).map
            (integralCounitImagesDoublePresentation l E h k _ C
              (integralCounitImagesResolutionPresentation l E ((D.coefficient E).system V)
                q C e)).hom) ≫
        (integralComparisonTowerCounit l E Z).app
          (DerivedCategory.Q.obj (integralCounitImagesDoubleTower l E h k C)) =
      (integralComparisonConstantTower l E Z).map
          (inv ((inverseImageIntegralDerived l E h).map
            ((inverseImageIntegralDerived l E k).map (DerivedCategory.Q.map q)))) ≫
        (integralTowerInverseImageDiagonal l E h).hom.app
          ((inverseImageIntegralDerived l E k).obj (DerivedCategory.Q.obj P.obj)) ≫
        (integralDerivedTowerInverseImage l E h).map
          (integralCounitImagesThetaDerived l E k P.obj C θk) ≫
        (integralTowerInverseImage l E h).mapDerivedCategoryFactors.hom.app
          (integralCounitImagesTower l E k C) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (integralTowerInverseImageUnit l E h).hom
            (.up ℤ)).app
            (((integralComparisonSequencePullback l E k).mapHomologicalComplex
              (.up ℤ)).obj C))) := by
  sorry

end WeilConjectures
