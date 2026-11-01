/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstantPurityFrobenius.ConstantPurityFrobeniusSquare

/-! # Coefficient Frobenius pairs and their two endpoints

These are the unchanged coefficient-side definitions used by the native cohomology
comparison. They are separated so that each endpoint lemma can import them.
The exceptional action is the inverse-exchange mate, and the shifted Tate action
is the canonical root-line, tensor-unit and shift action. No smoothness is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

attribute [local instance 1100] CategoryTheory.instOverClass

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.ConstantPurityFrobenius

namespace WeilConjectures.NativeCoefficientCohomology

variable (P : PurityFiniteSetting.{u})
  (X₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

local instance nativeStructureOver : X₀.hom.IsOver (Spec (.of P.field.k₀)) := by
  constructor
  dsimp only [autoParam]
  change X₀.hom ≫ 𝟙 _ = X₀.hom
  rw [Category.comp_id]

local instance pointFiniteType : LocallyOfFiniteType (point P.field).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of P.field.k₀))))
local instance pointQuasiCompact : QuasiCompact (point P.field).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of P.field.k₀))))
local instance pointSeparated : IsSeparated (point P.field).hom :=
  inferInstanceAs (IsSeparated (𝟙 (Spec (.of P.field.k₀))))
local instance pointMapSeparated : IsSeparated (pointMap P.field X₀).left :=
  inferInstanceAs (IsSeparated X₀.hom)
local instance pointMapFiniteType : LocallyOfFiniteType (pointMap P.field X₀).left :=
  inferInstanceAs (LocallyOfFiniteType X₀.hom)
local instance pointMapQuasiCompact : QuasiCompact (pointMap P.field X₀).left :=
  inferInstanceAs (QuasiCompact X₀.hom)
local instance sourceFiniteType :
    LocallyOfFiniteType ((P.field.geometricFiber X₀).left ↘ Spec (.of P.field.k)) :=
  (FrobeniusExchange.fiber_finiteType P.field X₀).1
local instance sourceQuasiCompact :
    QuasiCompact ((P.field.geometricFiber X₀).left ↘ Spec (.of P.field.k)) :=
  (FrobeniusExchange.fiber_finiteType P.field X₀).2
local instance targetFiniteType :
    LocallyOfFiniteType ((P.field.geometricFiber (point P.field)).left ↘
      Spec (.of P.field.k)) :=
  (FrobeniusExchange.fiber_finiteType P.field (point P.field)).1
local instance targetQuasiCompact :
    QuasiCompact ((P.field.geometricFiber (point P.field)).left ↘ Spec (.of P.field.k)) :=
  (FrobeniusExchange.fiber_finiteType P.field (point P.field)).2
local instance geometricMapOver :
    (FrobeniusExchange.fiberMap P.field (pointMap P.field X₀)).IsOver
      (Spec (.of P.field.k)) := zlFiberMap_isOver P.field (pointMap P.field X₀)
local instance geometricMapSeparated :
    IsSeparated (FrobeniusExchange.fiberMap P.field (pointMap P.field X₀)) :=
  (FrobeniusExchange.fiberMap_properties P.field (pointMap P.field X₀)).1
local instance geometricMapFiniteType :
    LocallyOfFiniteType (FrobeniusExchange.fiberMap P.field (pointMap P.field X₀)) :=
  (FrobeniusExchange.fiberMap_properties P.field (pointMap P.field X₀)).2.1
local instance geometricMapQuasiCompact :
    QuasiCompact (FrobeniusExchange.fiberMap P.field (pointMap P.field X₀)) :=
  (FrobeniusExchange.fiberMap_properties P.field (pointMap P.field X₀)).2.2
local instance sourceUnits : ∀ x : (P.field.geometricFiber X₀).left,
    Invertible (P.coefficients.l : (P.field.geometricFiber X₀).left.residueField x) :=
  fun x ↦ sfWeilPrimeInvertible P.field P.coefficients.l P.coefficients.different X₀ x
local instance targetUnits : ∀ x : (P.field.geometricFiber (point P.field)).left,
    Invertible (P.coefficients.l :
      (P.field.geometricFiber (point P.field)).left.residueField x) :=
  fun x ↦ sfWeilPrimeInvertible P.field P.coefficients.l P.coefficients.different
    (point P.field) x

/-- The actual coefficient Frobenius pairs on the geometric fibre.
Source: constant-purity Frobenius square, Q.
(blueprint: def-sf-coefficient-endpoint-objects) -/
abbrev Pairs :=
  Endofunctor.IsoAlgebra (sourceFrobenius P.field P.coefficients.l
    P.coefficients.different P.coefficients.Qbar X₀)

variable (c₀ : Compactification X₀.hom)
  (S : systems P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar X₀)

/-- The ordinary exceptional constant pair, with the inverse-exchange adjunction mate.
Source: constant-purity Frobenius square, G(theta_0) e.
(blueprint: def-sf-coefficient-endpoint-objects) -/
def exceptionalConstant : Pairs P X₀ :=
  let D := P.field
  let l := P.coefficients.l
  let hl := P.coefficients.different
  let Ω := P.coefficients.Qbar
  let G := (operation D l hl Ω X₀ (point D) (pointMap D X₀) c₀ S .closed).G
  let K := unit D l hl Ω (D.geometricFiber (point D)).left
  Endofunctor.IsoAlgebra.mk (G.obj K)
    ((exceptionalIso D l hl Ω X₀ (point D) (pointMap D X₀) c₀ S).app K ≪≫
      G.mapIso (constantWeilAlgebraicallyClosedComplex l D hl (point D) Ω).str)

/-- The purity-source pair, with its canonical constant, Tate and shift Frobenius.
It exists on any separated finite-type model, with no smoothness assumption.
Source: constant-purity Frobenius square, H(Lambda), theta_H,can.
(blueprint: def-sf-coefficient-endpoint-objects) -/
def twistedConstant (d : ℕ) : Pairs P X₀ :=
  let D := P.field
  let l := P.coefficients.l
  let hl := P.coefficients.different
  let Ω := P.coefficients.Qbar
  Endofunctor.IsoAlgebra.mk
    ((source D l hl Ω X₀ (point D) (pointMap D X₀) d).obj
      (unit D l hl Ω (D.geometricFiber (point D)).left))
    (canonicalSourceTheta D l hl Ω X₀ (point D) (pointMap D X₀) d)

end WeilConjectures.NativeCoefficientCohomology
