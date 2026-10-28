/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ConstantPurityFrobeniusSquare
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.TateTwist

/-! # Cohomology comparison between coefficient Frobenius pairs and native Weil sheaves

This comparison concerns cohomology, not an equivalence of the two derived categories.
It requires no smoothness. The exceptional endpoint uses the inverse-exchange mate;
the Tate endpoint uses the root-line Frobenius. Smooth purity is a separate input.
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
(blueprint: lem-sf-native-coefficient-cohomology-comparison) -/
abbrev Pairs :=
  Endofunctor.IsoAlgebra (sourceFrobenius P.field P.coefficients.l
    P.coefficients.different P.coefficients.Qbar X₀)

variable (c₀ : Compactification X₀.hom)
  (S : systems P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar X₀)

/-- The ordinary exceptional constant pair, with the inverse-exchange adjunction mate.
Source: constant-purity Frobenius square, G(theta_0) e.
(blueprint: lem-sf-native-coefficient-cohomology-comparison) -/
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
(blueprint: lem-sf-native-coefficient-cohomology-comparison) -/
def twistedConstant (d : ℕ) : Pairs P X₀ :=
  let D := P.field
  let l := P.coefficients.l
  let hl := P.coefficients.different
  let Ω := P.coefficients.Qbar
  Endofunctor.IsoAlgebra.mk
    ((source D l hl Ω X₀ (point D) (pointMap D X₀) d).obj
      (unit D l hl Ω (D.geometricFiber (point D)).left))
    (canonicalSourceTheta D l hl Ω X₀ (point D) (pointMap D X₀) d)

variable [Fact (ringChar P.field.k₀ ≠ P.coefficients.l)]

/-- Cohomology of ordinary coefficient Frobenius pairs has a native Weil-sheaf model.
The same functors work in every degree, for every native exceptional adjoint, and for
all nonnegative Tate powers. No smoothness or geometric purity is asserted here.

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, exceptional
adjunction paragraph; cor-pur-adic-and-rational-smooth-dualizing-complexes.proof.md,
constant-unit identification; lem-pur-constant-purity-frobenius-square, canonical
Tate-source convention.
(blueprint: lem-sf-native-coefficient-cohomology-comparison)

Proof: realize a common-stage complex as an ordinary complex of modules over the
continuous, finite-extension-valued coefficient sheaf. Use the normalized section-module
equivalence and change of algebraic closure to put it on the native geometric fibre.
The realization comparisons for geometric Frobenius transport a coefficient fixed pair
to a fixed pair of ordinary derived objects. Apply degree n cohomology. Exactness of
Frobenius pullback gives its cohomology commutation isomorphism, so this is a pair of
sheaves, functorially on every intertwining morphism. Realization preserves bounded
constructibility; thus these sheaf pairs lie in the full subcategory WeilSheaf. This
constructs the functors C, without identifying the native derived category with fixed
pairs of derived objects.

For the exceptional endpoint, apply the counit-normalized native exceptional-forgetting
comparison and its scalar-unit normalization at the constant point object. Transport the
native counit's equivariance through the normalized compact-support comparison. The
ordinary adjunction hom-equivalence uniquely determines the transported action: transpose
the counit equation to obtain the inverse-exchange right mate followed by G(theta_0).
The scalar Frobenius counit theorem gives exactly that mate and its invariant counit.
Take cohomology of this comparison; exact forgetting computes the native cohomology and
hence gives the first family of Weil-sheaf isomorphisms, in every degree.

For the other endpoint, pullback takes the scalar unit to the scalar unit. The normalized
root-line realization identifies its d-th Tate power with the native Tate sheaf, including
its cyclotomic Frobenius; tensor normalization adds the native constant factor. Exact
realization takes the even shift to the shift by 2d. Its degree -2d cohomology is therefore
the native Tate sheaf tensor the constant sheaf. All maps respect the root, tensor-unit
and shift comparisons used in canonicalSourceTheta. This proves the second family.
The construction is valid at d=0 and on the empty scheme; neither part uses smoothness.
-/
theorem coefficient_cohomology_comparison :
    ∃ C : ℤ → (Pairs P X₀ ⥤ WeilSheaf P.field.k₀ P.coefficients.l X₀.left),
      (∀ (J : WeilComplex P.field.k₀ P.coefficients.l (Spec (.of P.field.k₀)) ⥤
          WeilComplex P.field.k₀ P.coefficients.l X₀.left)
        (adj : WeilComplex.derivedLowerShriek P.field.k₀ P.coefficients.l X₀.hom ⊣ J)
        (n : ℤ),
        Nonempty ((WeilComplex.homologySheaf n).obj
            (J.obj (WeilSheaf.toComplex.obj
              (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l
                (Spec (.of P.field.k₀))))) ≅
          (C n).obj (exceptionalConstant P X₀ c₀ S))) ∧
      (∀ d : ℕ, Nonempty ((C (-2 * (d : ℤ))).obj (twistedConstant P X₀ d) ≅
        (WeilSheaf.tateTwistSheaf P.field.k₀ P.coefficients.l X₀.left d).tensorObj
          (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l X₀.left)
          (WeilSheaf.isLisse_tateTwistSheaf P.field.k₀ P.coefficients.l X₀.left d))) := by
  sorry

end WeilConjectures.NativeCoefficientCohomology
