/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module

public import Sheaf.Paper.RationalFibrePathConstruction
public import Sheaf.Paper.RationalFibreScalarComparison

/-!
# Rational scalar extension commutes with fibre paths

Source: Weil II (1.1.1) c), d), pp.146-147.
(blueprint: new-e5-rational-fibre-path-scalar-square).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
  (i : IntegralFibrePathTransport l Y Q)
  {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
  {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
  (t : flcFiber y ≅ flcFiber z) (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L)

attribute [local irreducible] GrothendieckTopology.Point.sheafFiber
  GrothendieckTopology.Point.presheafFiber lisseRationalFiberFunctor

private theorem integralScalar_path_unit (F : LisseIntegralSheaf l E.val Y)
    (x : (lisseIntegralFiberFunctor l E.val Y y).obj F) :
    integralFibreScalarUnit l Y z E.val L.val (IntermediateField.inclusion h) F
        (((i.linear E).map y z t).hom.app F x) =
      ((i.linear L).map y z t).hom.app
        ((lisseIntegralScalarExtension l E.val Y L.val (IntermediateField.inclusion h)).obj F)
        (integralFibreScalarUnit l Y y E.val L.val (IntermediateField.inclusion h) F x) := by
  unfold integralFibreScalarUnit
  let α := lisseIntegerInclusion l E.val L.val (IntermediateField.inclusion h)
  let f := ((i.linear E).map y z t).hom.app F
  have hu := ConcreteCategory.congr_hom
    ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} α).unit.naturality f) x
  have hs := ConcreteCategory.congr_hom
    (integralFibreScalarIso_path l Y Q i y z t E L h F)
    ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} α).unit.app _ x)
  exact (congrArg
    ((integralFibreScalarIso l Y z E.val L.val (IntermediateField.inclusion h)).hom.app F)
    hu).trans hs

private theorem rationalScalarTargetPath (F : LisseRationalSheaf l E.val Y)
    (x : (lisseIntegralFiberFunctor l E.val Y y).obj F.integral) :
    ((rationalFibrePathFamily l L.val Y (i.linear L)).map y z t).hom.app
      ((lisseRationalScalarExtension l E.val Y L.val (IntermediateField.inclusion h)).obj F)
      (eqToHom (lisseRationalFiberFunctor_obj l L.val Y y
        ((lisseRationalScalarExtension l E.val Y L.val
          (IntermediateField.inclusion h)).obj F)).symm
        ((1 : L.val) ⊗ₜ[Padic.coefficientExtensionIntegers l L.val]
          (integralFibreScalarUnit l Y y E.val L.val (IntermediateField.inclusion h)
            F.integral x))) =
    eqToHom (lisseRationalFiberFunctor_obj l L.val Y z
      ((lisseRationalScalarExtension l E.val Y L.val
        (IntermediateField.inclusion h)).obj F)).symm
      ((1 : L.val) ⊗ₜ[Padic.coefficientExtensionIntegers l L.val]
        (((i.linear L).map y z t).hom.app
          ((lisseIntegralScalarExtension l E.val Y L.val
            (IntermediateField.inclusion h)).obj F.integral)
          (integralFibreScalarUnit l Y y E.val L.val (IntermediateField.inclusion h)
            F.integral x))) := by
  exact rationalFibrePathFamily_apply l L.val Y (i.linear L) y z t _ 1 _

set_option maxRecDepth 2000 in
/-- Scalar comparison into a common field commutes with rationalized paths.
Source: Weil II (1.1.1) c), d), pp.146-147.
(blueprint: new-e5-rational-fibre-path-scalar-square).
Proof: the scalar-extension adjunction reduces to unit tensors. Transport the rational
fibre object and use tensor induction. On b tensor x the two sides are the same pure
tensor by the scalar comparison formula, the rational path formula and the integral
scalar/path square evaluated on the scalar-extension unit. -/
theorem rationalFibreComparisonIso_path (K : Type (u + 1)) [Field K]
    (j : E.val →+* K) (k : L.val →+* K)
    (hjk : k.comp (IntermediateField.inclusion h).toRingHom = j)
    (F : LisseRationalSheaf l E.val Y) :
    (ModuleCat.extendScalars j).map
        (((rationalFibrePathFamily l E.val Y (i.linear E)).map y z t).hom.app F) ≫
      (rationalFibreComparisonIso l Y z E.val L.val
        (IntermediateField.inclusion h) K j k hjk).hom.app F =
    (rationalFibreComparisonIso l Y y E.val L.val
        (IntermediateField.inclusion h) K j k hjk).hom.app F ≫
      (ModuleCat.extendScalars k).map
        (((rationalFibrePathFamily l L.val Y (i.linear L)).map y z t).hom.app
          ((lisseRationalScalarExtension l E.val Y L.val
            (IntermediateField.inclusion h)).obj F)) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro v
  obtain ⟨w, rfl⟩ :=
    ((eqToIso (lisseRationalFiberFunctor_obj l E.val Y y F)).toLinearEquiv.symm).surjective v
  with_unfolding_all
    change E.val ⊗[Padic.coefficientExtensionIntegers l E.val]
      ((lisseIntegralFiberFunctor l E.val Y y).obj F.integral) at w
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.tmul_zero]
  | add a b ha hb =>
    simp only [map_add, TensorProduct.tmul_add] at ha hb ⊢
    exact congrArg₂ (· + ·) ha hb
  | tmul b x =>
    change
      (rationalFibreComparisonIso l Y z E.val L.val
        (IntermediateField.inclusion h) K j k hjk).hom.app F
        ((ModuleCat.extendScalars j).map
          (((rationalFibrePathFamily l E.val Y (i.linear E)).map y z t).hom.app F)
          ((1 : K) ⊗ₜ[E.val,j] (eqToHom
            (lisseRationalFiberFunctor_obj l E.val Y y F).symm
              (b ⊗ₜ[Padic.coefficientExtensionIntegers l E.val] x)))) =
      (ModuleCat.extendScalars k).map
        (((rationalFibrePathFamily l L.val Y (i.linear L)).map y z t).hom.app
          ((lisseRationalScalarExtension l E.val Y L.val
            (IntermediateField.inclusion h)).obj F))
        ((rationalFibreComparisonIso l Y y E.val L.val
          (IntermediateField.inclusion h) K j k hjk).hom.app F
          ((1 : K) ⊗ₜ[E.val,j] (eqToHom
            (lisseRationalFiberFunctor_obj l E.val Y y F).symm
              (b ⊗ₜ[Padic.coefficientExtensionIntegers l E.val] x))))
    rw [ModuleCat.ExtendScalars.map_tmul, rationalFibrePathFamily_apply,
      rationalFibreComparisonIso_tmul, rationalFibreComparisonIso_tmul,
      ModuleCat.ExtendScalars.map_tmul,
      rationalScalarTargetPath l Y Q i y z t E L h F x]
    rw [integralScalar_path_unit l Y Q i y z t E L h F.integral x]

/-- Removing scalar extension by the identity preserves the path square.
Source: Weil II (1.1.1) d), pp.146-147.
(blueprint: new-e5-rational-fibre-path-scalar-square).
Proof: apply the common-field square with field L. Naturality of the scalar-extension
identity isomorphism gives the square after removing its last scalar extension. -/
theorem rationalFibreScalarIso_path [Algebra E.val L.val]
    (ha : algebraMap E.val L.val = (IntermediateField.inclusion h).toRingHom)
    (F : LisseRationalSheaf l E.val Y) :
    (ModuleCat.extendScalars (algebraMap E.val L.val)).map
        (((rationalFibrePathFamily l E.val Y (i.linear E)).map y z t).hom.app F) ≫
      (rationalFibreScalarIso l Y z E.val L.val (IntermediateField.inclusion h) ha).hom.app F =
    (rationalFibreScalarIso l Y y E.val L.val (IntermediateField.inclusion h) ha).hom.app F ≫
      (((rationalFibrePathFamily l L.val Y (i.linear L)).map y z t).hom.app
        ((lisseRationalScalarExtension l E.val Y L.val
          (IntermediateField.inclusion h)).obj F)) := by
  have hs := rationalFibreComparisonIso_path l Y Q i y z t E L h L.val
    (algebraMap E.val L.val) (RingHom.id L.val) ha.symm F
  have hn := (ModuleCat.extendScalarsId.{u + 1, u + 1} L.val).hom.naturality
    (((rationalFibrePathFamily l L.val Y (i.linear L)).map y z t).hom.app
      ((lisseRationalScalarExtension l E.val Y L.val
        (IntermediateField.inclusion h)).obj F))
  unfold rationalFibreScalarIso
  change _ ≫ ((rationalFibreComparisonIso l Y z E.val L.val
      (IntermediateField.inclusion h) L.val (algebraMap E.val L.val)
      (RingHom.id L.val) ha.symm).hom.app F ≫
        (ModuleCat.extendScalarsId.{u + 1, u + 1} L.val).hom.app _) =
    ((rationalFibreComparisonIso l Y y E.val L.val
      (IntermediateField.inclusion h) L.val (algebraMap E.val L.val)
      (RingHom.id L.val) ha.symm).hom.app F ≫
        (ModuleCat.extendScalarsId.{u + 1, u + 1} L.val).hom.app _) ≫ _
  rw [← Category.assoc, hs, Category.assoc, hn]
  exact (Category.assoc _ _ _).symm

end AlgebraicGeometry.Scheme
