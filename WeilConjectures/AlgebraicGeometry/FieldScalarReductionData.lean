/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldScalarSystemData

public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerNormalized
public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionWellDefined
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.AlgebraicGeometry.Noetherian


/-! # Normalized field-scalar reduction data

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md, paragraph (1)
(blueprint: def-sp-field-scalar-reduction-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard
universe u a v w
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale.FieldScalar

variable {l : ℕ} [Fact l.Prime] {E F : Type u} [Field E] [Field F]
  [Algebra (Padic l) E] [Algebra (Padic l) F]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
  {ι : E →ₐ[Padic l] F} {T : Scheme.{u}}
  {DA : SpCoefficientTowersAbelian.{u, u} l E T} {DB : SpCoefficientTowersAbelian.{u, u} l F T}
  {RA : SpReductionTower l E T DA} {RB : SpReductionTower l F T DB}
  (c : Coefficients l E F ι T DA DB RA RB) (H : ExactExtension DA DB RA RB c)

/-- The integral derived extension is the existing normalized scalar model.
Source: paragraph (1), C-hat (blueprint: def-sp-field-scalar-reduction-data). -/
abbrev integralScalar := DA.scalar c.integral

/-- The local generator (x tensor s) tensor b, before localization.
Source: paragraph (1), balancing formula
(blueprint: def-sp-field-scalar-reduction-data). -/
def sourceTensor (M : spIntegralSectionModules l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
    (s : (spIntegralSectionRing l F T).obj.obj U)
    (b : ((spCoefficientCommRings.{u, u} l F T).obj (op n)).obj.obj U) (x : M.val.obj U) :
    ((DB.equivalence.functor.obj
      (RB.ordinary.obj ((integralScalar c).model.E.obj M))).level n).val.obj U :=
  ((RB.level n).inv.app ((integralScalar c).model.E.obj M)).val.app U
    (systemModelTmul (DB.scalar (spIntegralReductionScalar l F T RB.coefficient n)).model
      _ U b (systemModelTmul (integralScalar c).model M U s x))

/-- The local generator (x tensor a) tensor b, before localization.
Source: paragraph (1), balancing formula
(blueprint: def-sp-field-scalar-reduction-data). -/
def targetTensor (M : spIntegralSectionModules l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
    (a : ((spCoefficientCommRings.{u, u} l E T).obj (op n)).obj.obj U)
    (b : ((spCoefficientCommRings.{u, u} l F T).obj (op n)).obj.obj U) (x : M.val.obj U) :
    ((DB.equivalence.functor.obj (H.ordinary.obj (RA.ordinary.obj M))).level n).val.obj U :=
  ((H.level n).inv.app (RA.ordinary.obj M)).val.app U
    (systemModelTmul (DA.scalar (c.tower.app (op n))).model _ U b
      (((RA.level n).inv.app M).val.app U
        (systemModelTmul (DA.scalar (spIntegralReductionScalar l E T RA.coefficient n)).model
          M U a x)))

/-- A balancing isomorphism of entire ordinary tower functors, fixed in both
 directions on local tensor generators. Thus every quotient transition and every
module morphism is respected before passage to complexes or to the derived category.
Source: paragraph (1), reduction associativity
(blueprint: def-sp-field-scalar-reduction-data). -/
structure OrdinaryComparison where
  iso : (integralScalar c).model.E ⋙ RB.ordinary ≅ RA.ordinary ⋙ H.ordinary
  forward : ∀ (M : spIntegralSectionModules l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
    (s : (spIntegralSectionRing l F T).obj.obj U)
    (b : ((spCoefficientCommRings.{u, u} l F T).obj (op n)).obj.obj U) (x : M.val.obj U),
    ((spCoefficientEvaluation.{u, u} l F T DB.equivalence n).map (iso.hom.app M)).val.app U
      (sourceTensor c M n U s b x) =
    targetTensor c H M n U 1
      ((spIntegralReductionScalar l F T RB.coefficient n).hom.app U s * b) x
  inverse : ∀ (M : spIntegralSectionModules l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
    (a : ((spCoefficientCommRings.{u, u} l E T).obj (op n)).obj.obj U)
    (b : ((spCoefficientCommRings.{u, u} l F T).obj (op n)).obj.obj U) (x : M.val.obj U),
    ((spCoefficientEvaluation.{u, u} l F T DB.equivalence n).map (iso.inv.app M)).val.app U
      (targetTensor c H M n U a b x) =
    sourceTensor c M n U 1 ((c.tower.app (op n)).hom.app U a * b) x

/-- Apply the specified balancing isomorphism in every degree of the same strict
 tower complex. Source: paragraph (1), one K-flat representative
(blueprint: def-sp-field-scalar-reduction-data). -/
def comparisonChain (A : OrdinaryComparison c H)
    (P : CochainComplex (spIntegralSectionModules l E T) ℤ) :=
  letI := RA.additive
  letI := RB.additive
  letI := H.additive
  (NatTrans.mapHomologicalComplex A.iso.hom (.up ℤ)).app P

/-- The canonical comparison on the entire ordinary derived category of strict
 systems. Its representative equation fixes it by the universal derived counits,
including roofs; no equality of arbitrary derived maps is inferred from evaluation.
Source: paragraph (1), derived reduction formula and naturality
(blueprint: def-sp-field-scalar-reduction-data). -/
structure ReductionComparison extends OrdinaryComparison c H where
  isoDerived : (integralScalar c).model.T ⋙ RB.red ≅ RA.red ⋙ H.derived
  representative : ∀ (P : CochainComplex (spIntegralSectionModules l E T) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T) P →
    isoDerived.hom.app (DerivedCategory.Q.obj P) ≫
        H.derived.map (RA.counit.app P) ≫
        H.counit.app ((RA.ordinary.mapHomologicalComplex (.up ℤ)).obj P) =
      RB.red.map ((integralScalar c).model.ε.app P) ≫
        RB.counit.app (((integralScalar c).model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (spTowerLocalization l F T DB).map (comparisonChain c H toOrdinaryComparison P)

end AlgebraicGeometry.ProEtale.FieldScalar

namespace AlgebraicGeometry.ProEtale.FieldScalar

variable {l : ℕ} [Fact l.Prime] {E F : Type u} [Field E] [Field F]
  [Algebra (Padic l) E] [Algebra (Padic l) F]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
  {ι : E →ₐ[Padic l] F} {T : Scheme.{u}}
  {DA : SpCoefficientTowersAbelian.{u, u} l E T}
  {DB : SpCoefficientTowersAbelian.{u, u} l F T}
  {RA : SpReductionTower l E T DA} {RB : SpReductionTower l F T DB}
  (c : Coefficients l E F ι T DA DB RA RB) (H : ExactExtension DA DB RA RB c)

/-- Termwise derived restriction, on the exact ordinary restriction already specified.
Source: paragraph (1), underlying restricted complex
(blueprint: def-sp-field-scalar-reduction-data). -/
def derivedRestriction : spDerivedCoefficientTowers l F T DB ⥤
    spDerivedCoefficientTowers l E T DA :=
  letI := DA.hasDerived
  letI := DB.hasDerived
  letI := H.restrictionAdditive
  letI := H.restrictionLimits
  letI := H.restrictionColimits
  H.restriction.mapDerivedCategory

/-- The same finite power on the ordinary derived category, with its existing exact
finite products. Source: paragraph (1), fixed finite sum
(blueprint: def-sp-field-scalar-reduction-data). -/
def derivedPower (r : ℕ) : spDerivedCoefficientTowers l E T DA ⥤
    spDerivedCoefficientTowers l E T DA :=
  letI := DA.hasDerived
  power r

/-- A constant integral scalar in the reconstructed completed section ring.
Source: paragraph (1), integral basis before reduction
(blueprint: def-sp-field-scalar-reduction-data). -/
def integralConstant (b : Padic.coefficientExtensionIntegers l F) (U : T.ProEtᵒᵖ) :
    (spIntegralSectionRing l F T).obj.obj U :=
  ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    RB.coefficient.inv).hom.app U
      ((WeilConjectures.integralConstantToCompletionOfUniverses.{u, u} l F T).hom.app U
        ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of
            (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l F))))).app U
          (ULift.up b)))

/-- The rank-one integral module, with the existing coefficient universe fixed.
Source: paragraph (1), integral basis (blueprint: def-sp-field-scalar-reduction-data). -/
def integralUnit (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :
    spIntegralSectionModules l E T :=
  SheafOfModules.unit ((sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (spIntegralSectionRing l E T))

/-- Restriction of integral modules along the specified completed inclusion.
Source: paragraph (1), completed basis (blueprint: def-sp-field-scalar-reduction-data). -/
def integralRestriction : spIntegralSectionModules l F T ⥤ spIntegralSectionModules l E T :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.integral)

/-- The completed finite basis and the finite sum on derived systems, using precisely
 the basis already reduced in ExactExtension. Source: paragraph (1), compatible bases
(blueprint: def-sp-field-scalar-reduction-data). -/
structure Coordinates where
  integral : (power (C := spIntegralSectionModules l E T) (degree l E F ι)).obj
      (integralUnit l E T) ≅ (integralRestriction c).obj (integralUnit l F T)
  integral_column : ∀ (i : Fin (degree l E F ι)) (U : T.ProEtᵒᵖ),
    ((column (degree l E F ι) _ i ≫ integral.hom).val.app U)
      (1 : (spIntegralSectionRing l E T).obj.obj U) =
        integralConstant.{u} (RB := RB) (H.basis i) U
  derived : H.derived ⋙ derivedRestriction.{u} c H ≅ derivedPower.{u} (DA := DA) (degree l E F ι)

end AlgebraicGeometry.ProEtale.FieldScalar
