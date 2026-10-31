/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.SecSmoothPurity.ScalarExtensionFunctor
public import WeilConjectures.SecSmoothPurity.FiniteGeneralRing
public import WeilConjectures.SecSmoothPurity.ReductionExceptional
public import WeilConjectures.AlgebraicGeometry.SmoothPurityMap
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowers
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGluing
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGamma
import WeilConjectures.SecSmoothPurity.ReductionDirectImage
import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowersAbelian
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Retagging, finite coefficient extension, and strict tower orientations

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
thm-pur-weil-equivariance-of-purity-and-trace.proof.md, Steps 1 and 5
(blueprint: lem-pur-retagging-coefficient-tower-transfer).

All finite comparisons use the recorded ordinary, uncompleted coefficient categories.
The tower conclusion is equality after the section-preserving equivalence back to
D(Tow), retaining the quotient transitions. It does not assert that evaluation is
faithful on arbitrary derived morphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale

/-- The prime-power orientation equality, with precisely the identity of underlying sites.
Only the target structural map enters the recorded normalized diagonal comparison.
Source: equivariance proof Step 1 (blueprint: lem-pur-retagging-coefficient-tower-transfer). -/
def RetaggingPrimeOrientation (P : PurityFiniteSetting.{u})
    (σ : P.field.k ≃ₐ[P.field.k₀] P.field.k) {X Y : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] : Prop :=
  (P.diagonalDualizingObject d f (aY ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))).hom =
    (P.diagonalDualizingObject d f aY).hom

/-- Both normalized finite-A orientations, their common counit-defined coefficient
comparison, and the scalar-extension formulas. The direct diagonal normalization
and comparison-unit equations fix the orientations; they are not arbitrary isos.
The equation c >> Pi_A = (Pi_R)_A is the inverse-free form of the displayed formula.
Source: equivariance proof Step 1, finite coefficients
(blueprint: lem-pur-retagging-coefficient-tower-transfer). -/
def RetaggingFiniteTransfer (P : PurityFiniteSetting.{u})
    (σ : P.field.k ≃ₐ[P.field.k₀] P.field.k) {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (hf : f ≫ aY = aX)
    (A : Type u) [CommRing A] [Finite A] (hA : (P.diagonalExponent : A) = 0) : Prop :=
  letI := isNoetherian_of_locallyOfFiniteType aX
  letI := isNoetherian_of_locallyOfFiniteType aY
  letI : HasCompactification f := inferInstance
  letI : HasCompactification
      ((Over.map (Spec.map (CommRingCat.ofHom σ.toRingHom))).map
        (Over.homMk f hf : Over.mk aX ⟶ Over.mk aY)).left :=
    inferInstanceAs (HasCompactification f)
  ∃ e : P.Ring ≃+* ULift.{u} (ZMod P.diagonalExponent),
  ∃ t : Etale.FiniteSmoothPurity.CoefficientLineComparison
      (RingHom.ulift.{u + 1, u + 1, u, u} (finiteGeneralRingCoefficientMap P A hA e))
      P.diagonalExponent P.diagonalExponent P.diagonalExponent_annihilates
      (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) X,
  ∃ theta thetaσ :
      (Etale.FiniteSmoothPurity.exceptional (ULift.{u + 1, u} A) f).obj
        (finiteGeneralRingUnit (ULift.{u + 1, u} A) Y) ≅
      (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).obj
        (Etale.FiniteSmoothPurity.line (ULift.{u + 1, u} A) P.diagonalExponent
          (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) X d),
  ∃ alpha alphaσ : Etale.dualizingComplex (ULift.{u + 1, u} A) f ≅
      Etale.FiniteSmoothPurity.line (ULift.{u + 1, u} A) P.diagonalExponent
        (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) X d,
  ∃ geometry : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f),
    IsIso (finiteGeneralRingReduction P (finiteGeneralRingCoefficientMap P A hA e) f) ∧
    finiteGeneralRingReduction P (finiteGeneralRingCoefficientMap P A hA e)
        ((Over.map (Spec.map (CommRingCat.ofHom σ.toRingHom))).map
          (Over.homMk f hf : Over.mk aX ⟶ Over.mk aY)).left =
      finiteGeneralRingReduction P (finiteGeneralRingCoefficientMap P A hA e) f ∧
    finiteGeneralRingReduction P (finiteGeneralRingCoefficientMap P A hA e) f ≫ theta.hom =
      (finiteGeneralRingOrientationExtension P (finiteGeneralRingCoefficientMap P A hA e)
        (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) d f aY t).hom ∧
    finiteGeneralRingReduction P (finiteGeneralRingCoefficientMap P A hA e) f ≫ thetaσ.hom =
      (finiteGeneralRingOrientationExtension P (finiteGeneralRingCoefficientMap P A hA e)
        (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) d f
        (aY ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) t).hom ∧
    finiteGeneralRingDualizingUnitMap (ULift.{u + 1, u} A) f ≫ theta.hom =
      (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).map alpha.hom ∧
    finiteGeneralRingDualizingUnitMap (ULift.{u + 1, u} A) f ≫ thetaσ.hom =
      (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).map alphaσ.hom ∧
    Etale.FiniteSmoothPurity.OrientationNormalized (ULift.{u + 1, u} A)
      P.diagonalExponent (pow_pos P.coefficients.prime.out.pos P.level)
      (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) f d geometry
      (P.diagonalExponent_isUnit (f ≫ aY)) alpha ∧
    Etale.FiniteSmoothPurity.OrientationNormalized (ULift.{u + 1, u} A)
      P.diagonalExponent (pow_pos P.coefficients.prime.out.pos P.level)
      (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) f d geometry
      (P.diagonalExponent_isUnit (f ≫ aY ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)))
      alphaσ ∧
    (RetaggingPrimeOrientation P σ d f aY → thetaσ.hom = theta.hom)

/-- Retagging preserves the canonical exceptional coefficient comparison and its
normalized diagonal-orientation formula for every finite ring killed by ell^m.
Source: equivariance proof Steps 1 and 5
(blueprint: lem-pur-retagging-coefficient-tower-transfer).

Proof:
1. In det-sp-reduction-direct-image the proper transpose and open tensor comparison
   use the same sites, ring map and compactification. Their b arrows agree.
2. The counit-preserving right-adjoint identification gives the same two counits.
   The defining transpose in det-sp-reduction-exceptional therefore gives the same c.
3. det-sp-finite-general-ring gives both displayed formulas and identifies their
   orientations with the normalized direct diagonal construction over A.
4. Apply det-sp-scalar-extension-functor to the prime-power orientation equality and
   cancel the common invertible c. No flatness of R_m -> A is required. -/
theorem retagging_finite_coefficient_transfer (P : PurityFiniteSetting.{u})
    (_hE : P.extension = ⊥) (σ : P.field.k ≃ₐ[P.field.k₀] P.field.k)
    {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) [IsSeparated aX]
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    (aY : Y ⟶ Spec (.of P.field.k)) [IsSeparated aY]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] (hf : f ≫ aY = aX)
    (A : Type u) [CommRing A] [Finite A] (hA : (P.diagonalExponent : A) = 0) :
    RetaggingFiniteTransfer P σ aX aY d f hf A hA := by
  sorry

/-- Transfer to every positive uniformizer quotient, including ramified extensions.
The quantified P has the fixed field and coefficient extension and an arbitrary
positive level, hence it is exactly O_E/varpi^n, not only the cofinal ell-power levels.
Source: equivariance proof Step 1, passage to A_E,n
(blueprint: lem-pur-retagging-coefficient-tower-transfer).

Proof:
1. Choose m >= 1 with e*m >= n, where ell=u*varpi^e in the coefficient DVR.
2. The quotient A_E,n is finite by def-weil-l-adic-coefficient-extension and is
   killed by ell^m. Apply retagging_finite_coefficient_transfer at that m.
3. det-sp-finite-general-ring identifies its scalar orientation with the direct
   normalized orientation. Kummer exponent independence removes the choice of m.
   This includes n=1, e=1 and every ramified finite extension. -/
theorem retagging_uniformizer_coefficient_transfer (P : PurityFiniteSetting.{u})
    (σ : P.field.k ≃ₐ[P.field.k₀] P.field.k) {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) [IsSeparated aX]
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    (aY : Y ⟶ Spec (.of P.field.k)) [IsSeparated aY]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] (_hf : f ≫ aY = aX)
    (_hprime : ∀ (m : ℕ) (hm : 1 ≤ m),
      RetaggingPrimeOrientation
        (finiteGeneralRingPrimeSetting P.field P.coefficients.l
          P.coefficients.different m hm) σ d f aY) :
    RetaggingPrimeOrientation P σ d f aY := by
  sorry

/-- Equality of the normalized orientations in the ordinary derived category of
strict towers, with the same quotient-coefficient transitions. G and adj are the
common counit-preserving presentation stipulated in the node; lv retains the actual
coefficient-mate reduction composites of det-sp-tower-gluing. Both a and aσ are
normalized tower orientations of det-sp-tower-gamma, not freely chosen arrows.
Source: equivariance proof Steps 1 and 5, strict coefficient towers
(blueprint: lem-pur-retagging-coefficient-tower-transfer).

Proof:
1. Apply the finite transfer to A_E,n and then B_r=O_E/ell^r. Their quotient ring
   maps and the exceptional comparison c are unchanged by the counit transpose.
2. det-sp-tower-gluing identifies tower counits with finite counits and its
   reduction arrow with f^!(r) after c. Thus all quotient transitions agree.
3. det-sp-tower-gamma identifies the evaluations of a and aσ with the inverses
   of these finite normalized orientations, so their evaluations agree.
4. Conjugate to an endomorphism of the shifted Tate sheaf tower and remove the
   common shift. The degree-zero embedding is fully faithful by
   lem-weil-pbc-derived-single-fully-faithful. Exact evaluation, from
   det-sp-coefficient-towers-abelian, makes each component of the resulting actual
   tower map the identity. Strict tower morphisms are component families, so this
   map is the identity. Restore the shift and conjugate back.
5. The section-preserving equivalence transports this equality to D(Tow). No
   faithfulness of evaluation on arbitrary derived morphisms has been used. -/
theorem retagging_strict_tower_orientation_transfer
    (P : PurityFiniteSetting.{u})
    (σ : P.field.k ≃ₐ[P.field.k₀] P.field.k)
    (b : SpTowerShriek.Base P.coefficients.l P.extension)
    (o : SpTowerShriek.Operations P.coefficients.l P.extension b)
    (q : SpTowerCalculus.Coordinates P.coefficients.l P.extension b)
    {X Z Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (aX : X ⟶ Spec (.of P.field.k)) [IsSeparated aX]
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    (aY : Y ⟶ Spec (.of P.field.k)) [IsSeparated aY]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [IsSeparated (j ≫ p)] [LocallyOfFiniteType (j ≫ p)] [QuasiCompact (j ≫ p)]
    [HasCompactification (j ≫ p)] (d : ℕ) [SmoothOfRelativeDimension d (j ≫ p)]
    (_hf : (j ≫ p) ≫ aY = aX)
    (w : SpChartAdmissibility.Twists P.coefficients.l P.extension X)
    (hF : ∀ M : SpTowerCalculus.C P.coefficients.l P.extension b q X,
      spConstructibleTorTowers P.coefficients.l P.extension Y (q.abelian Y)
        ((SpTowerCalculus.F P.coefficients.l P.extension b o q
          (SpTowerGamma.factorization j p)).obj M.obj))
    (G : SpTowerCalculus.C P.coefficients.l P.extension b q Y ⥤
      SpTowerCalculus.C P.coefficients.l P.extension b q X)
    (adj : SpTowerGluing.support P.coefficients.l P.extension b o q
      (SpTowerGamma.factorization j p) hF ⊣ G)
    (lv : SpTowerGluing.Levels P.coefficients.l P.extension b o q
      (SpTowerGamma.factorization j p) hF G adj)
    (a aσ : SpTowerGamma.Purity P.coefficients.l P.extension b o q j p d w hF G adj lv)
    (_hprime : ∀ (m : ℕ) (hm : 1 ≤ m),
      RetaggingPrimeOrientation
        (finiteGeneralRingPrimeSetting P.field P.coefficients.l
          P.coefficients.different m hm) σ d (j ≫ p) aY) :
    (SpTowerCalculus.realization P.coefficients.l P.extension b X
      (q.abelian X)).inverse.map aσ.orientation.hom =
    (SpTowerCalculus.realization P.coefficients.l P.extension b X
      (q.abelian X)).inverse.map a.orientation.hom := by
  sorry

end AlgebraicGeometry.ProEtale
