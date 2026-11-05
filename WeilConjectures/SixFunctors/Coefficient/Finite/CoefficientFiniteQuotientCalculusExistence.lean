/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.CoefficientActualScalarDerivedPair
import WeilConjectures.SixFunctors.Coefficient.CoefficientPrescribedPairTensorModels
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement

/-! # Existence of the finite quotient calculus

Source: Stacks 06YY, 07A4 and 0941
(blueprint: lem-coef-finite-quotient-calculus-existence).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance] WeilConjectures.coefficientFiniteQuotientExtensionAdditive
universe t u c v r w a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

attribute [local irreducible] SheafOfModules.instPreadditive HomologicalComplex.instPreadditive

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

-- Normalize the sheafification unit before substituting the large coefficient rings.

section OrdinaryCore
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {A B : Sheaf J CommRingCat.{r}} (a : A ⟶ B)
  (F : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) ⥤
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
  (hobj : ∀ M, F.obj M = SheafOfModules.changeOfRings a M)
  (hmap : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (hobj M) ≫
    SheafOfModules.changeOfRingsHom a M f ≫ eqToHom (hobj N).symm)

end OrdinaryCore

section GenericPair
open SheafOfModules
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{max c v r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
  [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
  [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))]

@[no_expose] private noncomputable def scalarPairWithSectionAdjunction
    (E : scalarModules J R ⥤ scalarModules J S)
    (hobj : ∀ M, E.obj M = changeOfRings a M)
    (hmap : ∀ {M N : scalarModules J R} (f : M ⟶ N),
      E.map f = eqToHom (hobj M) ≫ changeOfRingsHom a M f ≫
        eqToHom (hobj N).symm)
    (hadd : E.Additive)
    (F : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S))
    (ε : DerivedCategory.Qh ⋙ F ⟶ scalarHomotopy E hadd ⋙ DerivedCategory.Qh)
    (hF : F.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (scalarModules J R) (.up ℤ)))
    (hc : ∀ P : CochainComplex (scalarModules J R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
        IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (am : E ⊣ scalarRestriction a)
    (hu : OrdinaryForwardUnit.{r, c, v} a E hobj am)
    (d : F ⊣ scalarDerivedRestriction a)
    (hd : ∀ (P : CochainComplex (scalarModules J R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      d.unit.app (DerivedCategory.Q.obj P) ≫
        (scalarDerivedRestriction a).map
          (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (scalarRestriction a).mapDerivedCategoryFactorsh.hom.app
          ((E.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
        DerivedCategory.Qh.map ((am.mapHomotopyCategory (.up ℤ)).unit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) :
    ScalarDerivedPair a :=
  CategoryTheory.ScalarHomTensor.scalarPairWithAdjunction.{c, v, r, w} a E hobj hmap hadd
    F ε hF hc am (fun M V x ↦ hu M V x) d hd

end GenericPair

private theorem replaceGeneratorUnits {A B C D : Type*} {f : A → D} {g : B → C → D}
    {x x' : A} {y y' : B} {z z' : C} (h : f x = g y z)
    (hx : x = x') (hy : y = y') (hz : z = z') : f x' = g y' z' := by
  cases hx
  cases hy
  cases hz
  exact h

section GenericSquare
open SheafOfModules CategoryTheory.ScalarHomTensor

end GenericSquare

attribute [local implicit_reducible] CategoryTheory.uniformProd
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
attribute [local irreducible] coefficientFiniteQuotientExistence
  coefficientFiniteQuotientDerivedExistence HasDerivedCategory.standard
  coefficientTotalTensor coefficientFiniteTensorModelIso
  CoefficientTensorModels.iso CoefficientClosedStructure.tensor

attribute [local irreducible] quotientOrdinaryModel

attribute [local irreducible] coefficientFiniteQuotientExtension
  coefficientFiniteQuotientDerived coefficientFiniteQuotientCounit

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
@[no_expose] private noncomputable def quotientDerivedAdj {m n : ℕ} (h : n ≤ m) :
    coefficientFiniteQuotientDerived l E W h ⊣ normalizedDVRRes l E W h :=
  (quotientDerivedAdjunction l E W h (quotientOrdinaryModel l E W h).adjunction).choose

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [local irreducible] scalarPairWithSectionAdjunction in
@[no_expose] private noncomputable def quotientPair {m n : ℕ} (h : n ≤ m) :
    SheafOfModules.ScalarDerivedPair
      (J := Scheme.ProEt.topology W) (coefficientFiniteQuotient l E W h) :=
    scalarPairWithSectionAdjunction.{t+1, t, u, max (t+2) (u+1)}
      (coefficientFiniteQuotient l E W h)
      (coefficientFiniteQuotientExtension l E W h)
      (coefficientFiniteQuotientExtension_obj l E W h)
      (quotientExtension_map l E W h)
      (coefficientFiniteQuotientExtensionAdditive l E W h)
      (coefficientFiniteQuotientDerived l E W h) (coefficientFiniteQuotientCounit l E W h)
      (quotientDerived_isLeftDerived l E W h)
      (coefficientFiniteQuotientCounit_isIso l E W h) ((quotientOrdinaryModel l E W h).adjunction)
      (quotientForwardUnit l E W h) (quotientDerivedAdj l E W h)
      (quotientDerivedUnit l E W h)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
@[instance_reducible] private noncomputable def quotientHasDerivedFamily :
    ∀ A : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t+1)},
      HasDerivedCategory.{max (t+2) (u+1)}
        (SheafOfModules.scalarModules (Scheme.ProEt.topology W) A) :=
  fun _ ↦ HasDerivedCategory.standard _

attribute [local instance] quotientHasDerivedFamily

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
@[no_expose] private noncomputable def quotientComparison
    (T : CoefficientDerivedSystemTensors l E W) {m n : ℕ} (h : n ≤ m) :
    CategoryTheory.ScalarHomTensor.PairTensorComparison.{t+1, t, u, max (t+2) (u+1)}
      (coefficientFiniteQuotient l E W h) (quotientPair l E W h)
      (T.finiteClosed m) (T.finiteClosed n) (T.finiteTensorModel m)
      (T.finiteTensorModel n) := by
  exact (coefficientPrescribedPairTensorComparison.{t+1, t, u, max (t+2) (u+1)}
    (coefficientFiniteQuotient l E W h) (quotientPair l E W h)
    (T.finiteClosed m) (T.finiteClosed n) (T.finiteTensorModel m)
    (T.finiteTensorModel n)).some

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
@[no_expose] private noncomputable def quotientData
    (T : CoefficientDerivedSystemTensors l E W) : CoefficientFiniteQuotientData l E W T where
  ordinaryAdjunction := fun h ↦ (quotientOrdinaryModel l E W h).adjunction
  adjunction := fun h ↦ (quotientDerivedAdjunction l E W h
    (quotientOrdinaryModel l E W h).adjunction).choose
  preservesKFlat := fun h ↦ (quotientComparison l E W T h).preservesKFlat
  tensor := fun h ↦ (quotientComparison l E W T h).iso

end WeilConjectures
