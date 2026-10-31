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
import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.IntegralPullbackUnitComposition

/-! Integral normalized-unit Frobenius square used by the rational-stage comparison.
Source: constant comparison in the proof of purity/trace equivariance, preceding Step 1.
(blueprint: lem-pur-common-constant-unit-frobenius-integral).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstantPurityFrobenius

attribute [local implicit_reducible] CategoryTheory.Aut

/-- The integral square component through the normalized pullback compositors.
Source: constant comparison proof, finite and completed integral stages.
(blueprint: lem-pur-common-constant-unit-frobenius-integral).
-/
def integralSquarePullbackComponent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    (h : gX ≫ f = f ≫ gY)
    (K : sfIntegralConstructibleCategory l E Y) :
    (constructibleIntegralPullback l E gX).obj
        ((constructibleIntegralPullback l E f).obj K) ≅
      (constructibleIntegralPullback l E f).obj
        ((constructibleIntegralPullback l E gY).obj K) :=
  (pullbackTensorIntegralComposition l E f gX).symm.app K ≪≫
    eqToIso (congrArg (fun m : X ⟶ Y ↦
      (constructibleIntegralPullback l E m).obj K) h) ≪≫
    (pullbackTensorIntegralComposition l E gY f).app K

private theorem unit_eqToHom
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    {f g : X ⟶ Y} (h : f = g) :
    let KX := constantWeilIntegralObject l E D hl X
    let KY := constantWeilIntegralObject l E D hl Y
    let uf : (constructibleIntegralPullback l E f).obj KY ≅ KX :=
      ObjectProperty.isoMk _ (ConstantGeometricStalkUnit.integralUnit l E f)
    let ug : (constructibleIntegralPullback l E g).obj KY ≅ KX :=
      ObjectProperty.isoMk _ (ConstantGeometricStalkUnit.integralUnit l E g)
    eqToHom (congrArg (fun k ↦ (constructibleIntegralPullback l E k).obj KY) h) ≫
      ug.hom = uf.hom := by
  subst g
  simp

/-- The normalized completed constant unit commutes with the geometric Frobenius square
at the integral coefficient stage.
Source: constant comparison proof, finite quotient composition followed by the normalized
Roos unit and its canonical integral Frobenius comparison.
(blueprint: lem-pur-common-constant-unit-frobenius-integral).
-/
theorem integralUnit_frobenius
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) :
    letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
    letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
    let f := FrobeniusExchange.fiberMap D f₀
    let K := constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left
    let u := ObjectProperty.isoMk _ (ConstantGeometricStalkUnit.integralUnit l E f)
    (integralSquarePullbackComponent l E f
        (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
        (zlFrobenius_naturality D f₀) K).hom ≫
        (constructibleIntegralPullback l E f).map
          (constantWeilConstructibleIntegralTheta l E D hl Y₀).hom ≫ u.hom =
      (constructibleIntegralPullback l E (D.geometricFrobenius X₀).hom).map u.hom ≫
        (constantWeilConstructibleIntegralTheta l E D hl X₀).hom := by
  let := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  let f := FrobeniusExchange.fiberMap D f₀
  let gX := (D.geometricFrobenius X₀).hom
  let gY := (D.geometricFrobenius Y₀).hom
  let KX := constantWeilIntegralObject l E D hl (D.geometricFiber X₀).left
  let KY := constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left
  let uf : (constructibleIntegralPullback l E f).obj KY ≅ KX :=
    ObjectProperty.isoMk _ (ConstantGeometricStalkUnit.integralUnit l E f)
  let uX : (constructibleIntegralPullback l E gX).obj KX ≅ KX :=
    ObjectProperty.isoMk _ (ConstantGeometricStalkUnit.integralUnit l E gX)
  let uY : (constructibleIntegralPullback l E gY).obj KY ≅ KY :=
    ObjectProperty.isoMk _ (ConstantGeometricStalkUnit.integralUnit l E gY)
  have htX : constantWeilConstructibleIntegralTheta l E D hl X₀ = uX := by
    unfold constantWeilConstructibleIntegralTheta uX gX
    rw [ConstantGeometricStalkUnit.integralUnit_canonicalWeil]
  have htY : constantWeilConstructibleIntegralTheta l E D hl Y₀ = uY := by
    unfold constantWeilConstructibleIntegralTheta uY gY
    rw [ConstantGeometricStalkUnit.integralUnit_canonicalWeil]
  change (integralSquarePullbackComponent l E f gX gY _ KY).hom ≫
    (constructibleIntegralPullback l E f).map
      (constantWeilConstructibleIntegralTheta l E D hl Y₀).hom ≫ uf.hom =
    (constructibleIntegralPullback l E gX).map uf.hom ≫
      (constantWeilConstructibleIntegralTheta l E D hl X₀).hom
  rw [htX, htY]
  delta integralSquarePullbackComponent
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, eqToIso.hom, Category.assoc]
  have hcY := ConstantGeometricStalkUnit.integralUnit_composition D l hl E f gY
  change (pullbackTensorIntegralComposition l E gY f).hom.app KY ≫
    (constructibleIntegralPullback l E f).map uY.hom ≫ uf.hom = _ at hcY
  rw [hcY]
  have he := unit_eqToHom D l hl E (zlFrobenius_naturality D f₀)
  have he' : eqToHom (congrArg (fun k ↦ (constructibleIntegralPullback l E k).obj KY)
      (show gX ≫ f = f ≫ gY from zlFrobenius_naturality D f₀)) ≫
      (ObjectProperty.isoMk _ (ConstantGeometricStalkUnit.integralUnit l E (f ≫ gY)) :
        (constructibleIntegralPullback l E (f ≫ gY)).obj KY ≅ KX).hom =
      (ObjectProperty.isoMk _ (ConstantGeometricStalkUnit.integralUnit l E (gX ≫ f)) :
        (constructibleIntegralPullback l E (gX ≫ f)).obj KY ≅ KX).hom := he
  rw [he']
  have hc := ConstantGeometricStalkUnit.integralUnit_composition D l hl E gX f
  rw [← hc]
  change (pullbackTensorIntegralComposition l E f gX).inv.app KY ≫
    ((pullbackTensorIntegralComposition l E f gX).hom.app KY ≫
      (constructibleIntegralPullback l E gX).map uf.hom ≫ uX.hom) = _
  rw [← Category.assoc, Iso.inv_hom_id_app]
  simp only [Category.id_comp]

end WeilConjectures.ConstantPurityFrobenius
