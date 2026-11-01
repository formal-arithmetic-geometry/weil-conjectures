/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure
public import WeilConjectures.PoincareDuality.SemilinearFieldOperationLifts
public import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusGeometricExchange
public import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.ConstantGeometricStalkUnit
import WeilConjectures.SmoothPurity.ConstantPurityFrobenius.IntegralConstantUnitFrobenius

/-! # Rational-stage coherence of the normalized constant unit

Source: constant comparison in the proof of purity/trace equivariance, preceding Step 1.
(blueprint: lem-pur-common-constant-unit-frobenius-rational).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstantPurityFrobenius

/-- The rationalized normalized unit, prior to passage to the common coefficient stage.
Source: constant-comparison proof, Step 2
(blueprint: lem-pur-common-constant-unit-frobenius-rational).
-/
def rationalizedUnit
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    (rationalDerivedPullback l E f).obj
        (constantWeilRationalObject l E D hl Y) ≅
      constantWeilRationalObject l E D hl X :=
  eqToIso ((rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 _) ≪≫
    (sfRationalConstructibleLocalization l E X).mapIso
      (ObjectProperty.isoMk _ (ConstantGeometricStalkUnit.integralUnit l E f))

private theorem identity_heq {C : Type*} [Category* C] {A B : C}
    (h : A = B) : HEq (𝟙 A) (𝟙 B) := by
  cases h
  rfl

private theorem inverse_heq {C : Type*} [Category* C] {A B A' B' : C}
    (hA : A = A') (hB : B = B') (e : A ≅ B) (e' : A' ≅ B')
    (h : HEq e.hom e'.hom) : HEq e.inv e'.inv := by
  subst A' B'
  have he : e = e' := Iso.ext (eq_of_heq h)
  cases he
  rfl

section Localization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem pull_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfRationalConstructibleCategory l E Y) :
    (rationalDerivedPullback l E f).obj K =
      (sfRationalConstructibleLocalization l E X).obj
        ((constructibleIntegralPullback l E f).obj K.obj) := by
  unfold rationalDerivedPullback
  exact (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K

private theorem pull_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    {A B : sfRationalConstructibleCategory l E Y}
    {A' B' : sfIntegralConstructibleCategory l E Y}
    (hA : A = (sfRationalConstructibleLocalization l E Y).obj A')
    (hB : B = (sfRationalConstructibleLocalization l E Y).obj B')
    (a : A ⟶ B) (b : A' ⟶ B')
    (hab : HEq a ((sfRationalConstructibleLocalization l E Y).map b)) :
    HEq ((rationalDerivedPullback l E f).map a)
      ((sfRationalConstructibleLocalization l E X).map
        ((constructibleIntegralPullback l E f).map b)) := by
  subst A B
  cases hab
  unfold rationalDerivedPullback
  simpa only [sfRationalConstructibleLocalization,
    ScalarLocalization.localization] using
    (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.2 A' B' b 1

private theorem pull_twice_obj {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K : sfRationalConstructibleCategory l E Y) :
    (rationalDerivedPullback l E g).obj ((rationalDerivedPullback l E f).obj K) =
      (sfRationalConstructibleLocalization l E Z).obj
        ((constructibleIntegralPullback l E g).obj
          ((constructibleIntegralPullback l E f).obj K.obj)) := by
  rw [pull_obj, pull_obj]
  rfl

private theorem pull_eqToHom {X Y : Scheme.{u}} (a b : X ⟶ Y) (h : a = b)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfRationalConstructibleCategory l E Y) :
    HEq (eqToHom (congrArg (fun f ↦ (rationalDerivedPullback l E f).obj K) h))
      ((sfRationalConstructibleLocalization l E X).map
        (eqToHom (congrArg
          (fun f ↦ (constructibleIntegralPullback l E f).obj K.obj) h))) := by
  subst b
  rw [eqToHom_refl, eqToHom_refl, CategoryTheory.Functor.map_id]
  exact identity_heq (pull_obj l E a K)

private theorem square_localization {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (gX : X ⟶ X) (gY : Y ⟶ Y) (h : gX ≫ f = f ≫ gY)
    (K : sfRationalConstructibleCategory l E Y) :
    HEq (podRationalSquarePullbackComponent l E f gX gY h K).hom
      ((sfRationalConstructibleLocalization l E X).map
        (integralSquarePullbackComponent l E f gX gY h K.obj).hom) := by
  let Q := sfRationalConstructibleLocalization l E X
  have hi := inverse_heq (pull_obj l E (gX ≫ f) K)
    (pull_twice_obj l E f gX K)
    (pullbackTensorRationalComposition l E f gX K)
    (Q.mapIso ((pullbackTensorIntegralComposition l E f gX).app K.obj))
    (pullbackTensorRationalComposition_existsUnique l E f gX K).exists.choose_spec
  have he := pull_eqToHom l E (gX ≫ f) (f ≫ gY) h K
  have hc : HEq (pullbackTensorRationalComposition l E gY f K).hom
      (Q.map ((pullbackTensorIntegralComposition l E gY f).hom.app K.obj)) := by
    unfold pullbackTensorRationalComposition
    exact (pullbackTensorRationalComposition_existsUnique l E gY f K).exists.choose_spec
  have h1 := heq_comp (pull_twice_obj l E f gX K)
    (pull_obj l E (gX ≫ f) K) (pull_obj l E (f ≫ gY) K) hi he
  have h2 := heq_comp (pull_twice_obj l E f gX K)
    (pull_obj l E (f ≫ gY) K) (pull_twice_obj l E gY f K) h1 hc
  dsimp only [podRationalSquarePullbackComponent, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom]
  rw [← Category.assoc]
  refine h2.trans ?_
  apply heq_of_eq
  dsimp only [integralSquarePullbackComponent, Q, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, eqToIso.hom]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

end Localization

/-- Rational-stage Frobenius coherence for the normalized constant unit.
Source: constant comparison in the proof of purity/trace equivariance, preceding Step 1.
Proof: identify the two finite quotient maps by the constant-ring composition lemma;
apply the normalized strict Roos unit and its canonical Frobenius comparison at every
quotient; then pass through the derived-limit and rationalization functors. -/
theorem rationalizedUnit_frobenius
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) :
    letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
    letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
    let f := FrobeniusExchange.fiberMap D f₀
    let K := constantWeilRationalObject l E D hl (D.geometricFiber Y₀).left
    let u := rationalizedUnit D l hl E f
    (podRationalSquarePullbackComponent l E f
        (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
        (zlFrobenius_naturality D f₀) K).hom ≫
        (rationalDerivedPullback l E f).map
          (constantWeilRationalComplex l E D hl Y₀).str.hom ≫ u.hom =
      (sfWeilFrobeniusPullback D l hl X₀ E).map u.hom ≫
        (constantWeilRationalComplex l E D hl X₀).str.hom := by
  let := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  let f := FrobeniusExchange.fiberMap D f₀
  let gX := (D.geometricFrobenius X₀).hom
  let gY := (D.geometricFrobenius Y₀).hom
  let KY := constantWeilRationalObject l E D hl (D.geometricFiber Y₀).left
  let KX := constantWeilRationalObject l E D hl (D.geometricFiber X₀).left
  let Q := sfRationalConstructibleLocalization l E (D.geometricFiber X₀).left
  let uI : (constructibleIntegralPullback l E f).obj
      (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left) ≅
      constantWeilIntegralObject l E D hl (D.geometricFiber X₀).left :=
    ObjectProperty.isoMk _ (ConstantGeometricStalkUnit.integralUnit l E f)
  have hu : HEq (rationalizedUnit D l hl E f).hom (Q.map uI.hom) := by
    simp only [rationalizedUnit, Iso.trans_hom, eqToIso.hom,
      CategoryTheory.Functor.mapIso_hom, eqToHom_comp_heq_iff]
    rfl
  have ht (Z₀ : Over (Spec (.of D.k₀)))
      [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] :
      HEq (constantWeilRationalComplex l E D hl Z₀).str.hom
        ((sfRationalConstructibleLocalization l E (D.geometricFiber Z₀).left).map
          (constantWeilConstructibleIntegralTheta l E D hl Z₀).hom) := by
    change HEq (constantWeilRationalTheta l E D hl Z₀).hom _
    simp only [constantWeilRationalTheta, Iso.trans_hom, eqToIso.hom,
      CategoryTheory.Functor.mapIso_hom, eqToHom_comp_heq_iff]
    rfl
  have hs := square_localization l E f gX gY (zlFrobenius_naturality D f₀) KY
  have hm := pull_map l E f (pull_obj l E gY KY) rfl
    (constantWeilRationalComplex l E D hl Y₀).str.hom
    (constantWeilConstructibleIntegralTheta l E D hl Y₀).hom (ht Y₀)
  have hleft₁ := heq_comp (pull_twice_obj l E f gX KY)
    (pull_twice_obj l E gY f KY) (pull_obj l E f KY) hs hm
  have hleft := heq_comp (pull_twice_obj l E f gX KY)
    (pull_obj l E f KY) (rfl : KX = _) hleft₁ hu
  have hmu := pull_map l E gX (pull_obj l E f KY) rfl
    (rationalizedUnit D l hl E f).hom uI.hom hu
  have hright := heq_comp (pull_twice_obj l E f gX KY)
    (pull_obj l E gX KX) (rfl : KX = _) hmu (ht X₀)
  have hi := congrArg Q.map (integralUnit_frobenius D l hl E X₀ Y₀ f₀)
  simp only [CategoryTheory.Functor.map_comp] at hi
  rw [← Category.assoc] at hi
  simpa only [Category.assoc, sfWeilFrobeniusPullback] using
    eq_of_heq (hleft.trans ((heq_of_eq hi).trans hright.symm))

end WeilConjectures.ConstantPurityFrobenius
