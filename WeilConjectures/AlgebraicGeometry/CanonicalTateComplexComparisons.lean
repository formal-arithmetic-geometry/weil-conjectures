/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.SixFunctors.SchemeGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralOperationsScalarComparisons
public import WeilConjectures.AlgebraicGeometry.OrientationIntegralCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.IntegralTwistBaseChange
public import WeilConjectures.AlgebraicGeometry.SignedTwistReductionComparison
import WeilConjectures.AlgebraicGeometry.PositiveRootTensorProduct
import all WeilConjectures.AlgebraicGeometry.OrientationIntegralCoefficientTwists
import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization

/-! # Canonical Tate comparisons: ComplexComparisons

Source: current blueprint, def-pur-tate-datum, canonical root-line comparisons.
This module preserves the original unshifted comparison declarations.
(blueprint: def-pur-canonical-tate-complex-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u v a b c d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures.CanonicalTate
open FrobeniusCoefficientTwists

attribute [local instance 5000] integralTowerHasDerivedCategory scalarReductionTargetDerived

attribute [-instance] PrincipalKoszulStrictReplacement.abSheafify
  PrincipalKoszulStrictReplacement.abLocallyBijective
  PrincipalKoszulStrictReplacement.siteSmall
attribute [local irreducible] IntegralOnSlice.completion
  IntegralOnSlice.completionComparison IntegralOnSlice.completionUnit
  IntegralOnSlice.duality IntegralOnSlice.roosUnit IntegralAmbient.tensorTowerIso
  HasDerivedCategory.standard completedIntegralCoefficientSheafUnrestricted
  coefficientTotalTensor SheafOfModules.monoidalCategory IntegralOnSlice.tower
  IntegralOnSlice.augmentation integralOperationsTensorTowerFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
/-- Finite positive line comparisons for arbitrary morphisms.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-complex-comparisons).
Proof: Apply the roots-of-unity comparison at every level. Extend coefficients and
then tensor the first line map. At zero use the constant coefficient comparison.
The displayed local generators determine the maps uniquely. Local rank-one
trivializations prove that they are invertible; no inverse to the scheme map is used. -/
theorem finitePullSheaf_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃! t : ∀ r : ℕ, (finiteModulePull l E f n).obj
        (finiteCoefficientTwist l E Y n (r : ℤ)) ≅ finiteCoefficientTwist l E X n (r : ℤ),
      ∀ (r : ℕ) (V : Y.ProEt) (a : finiteTateCoefficient l E n)
        (x : Fin r → (purTwistZlOne Y l).obj.obj (op V)),
        (t r).hom.val.app (op ((proEtaleBaseChange f).obj V))
          (finiteModuleSection l E f n (finiteCoefficientTwist l E Y n (r : ℤ)) V
            (finiteTateProPowerGenerator l E n Y (op V) a r x)) =
        finiteTateProPowerGenerator l E n X (op ((proEtaleBaseChange f).obj V)) a r
          (fun i ↦ rootSection l f V (x i)) := by
  sorry

/-- The finite pullback comparison fixed by its scalar/root formula.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-complex-comparisons). -/
def finitePullSheaf {X Y : Scheme.{u}} (f : X ⟶ Y) (n r : ℕ)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :=
  (finitePullSheaf_existsUnique l E f n).exists.choose r

/-- The existing integral line as its degree-zero flat complex.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-complex-comparisons). -/
abbrev integralComplex (X : Scheme.{u}) (r : ℕ) :=
  (CochainComplex.singleFunctor _ 0).obj (positiveLine l E X r)

/-- Insert an ordered root tensor in degree zero at integral coefficients.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-complex-comparisons). -/
def integralGenerator (X : Scheme.{u}) (r : ℕ) (U : X.ProEtᵒᵖ)
    (a : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U) (x : Fin r →
      (purTwistZlOne X l).obj.obj U) :
    ((integralComplex l E X r).X 0).val.obj U :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (positiveLine l E X r)).inv.val.app U
    (generator l E X U a r x)

section IntegralRootTensor
attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
attribute [local semireducible] coefficientTotalTensor
attribute [local implicit_reducible] coefficientTotalTensor

/-- The canonical integral product of flat single complexes.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-complex-comparisons).
Proof: The total tensor has only its (0,0) summand. Concatenate the ordered
root lists and multiply the coefficients there. Splitting the list gives the
inverse; the tensor universal property proves uniqueness. Empty lists give the
unitors. Both differentials vanish, so these are maps of the entire complexes. -/
theorem integralProductComplex_existsUnique (X : Scheme.{u}) (r s : ℕ) :
    ∃! e : (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E X)).obj
          (integralComplex l E X r, integralComplex l E X s) ≅
        integralComplex l E X (r + s),
      ∀ (U : X.ProEtᵒᵖ) (a b : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U)
        (x : Fin r → (purTwistZlOne X l).obj.obj U)
        (y : Fin s → (purTwistZlOne X l).obj.obj U),
        (e.hom.f 0).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l E X) (integralComplex l E X r)
              (integralComplex l E X s)
            0 0 0 (by omega) U
            (integralGenerator l E X r U a x) (integralGenerator l E X s U b y)) =
        integralGenerator l E X (r + s) U (a * b) (Fin.addCases x y) := by
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let M := positiveLine l E X r
  let N := positiveLine l E X s
  let L := positiveLine l E X (r + s)
  obtain ⟨μ, hμ, hμunique⟩ := positiveRootTensorProduct_existsUnique l E X r s
  let m := singleTensorLift M N L 0 0 μ
  have hext := singleTensorExtract_lift M N L 0 0 μ
  refine ⟨m, ?_, ?_⟩
  · intro U a b x y
    apply (ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation _ U).map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).hom)).1
    have h := rootTensorExtract_pure l E X M N L 0 0 m U
      (FrobeniusCoefficientTwists.generator l E X U a r x)
      (FrobeniusCoefficientTwists.generator l E X U b s y)
    rw [hext] at h
    exact h.symm.trans ((hμ U a b x y).trans (congrArg (fun f ↦ f.val.app U
      (FrobeniusCoefficientTwists.generator l E X U (a * b) (r + s)
        (Fin.addCases x y)))
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).inv_hom_id).symm)
  · intro other hother
    apply singleTensorExtract_injective M N L 0 0
    rw [hext]
    apply hμunique
    intro U a b x y
    exact (rootTensorExtract_pure l E X M N L 0 0 other U
      (FrobeniusCoefficientTwists.generator l E X U a r x)
      (FrobeniusCoefficientTwists.generator l E X U b s y)).trans
      ((congrArg
        (fun z ↦ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).hom.val.app U z)
        (hother U a b x y)).trans
        (congrArg (fun f ↦ f.val.app U
          (FrobeniusCoefficientTwists.generator l E X U (a * b) (r + s)
            (Fin.addCases x y)))
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).inv_hom_id))

end IntegralRootTensor

/-- The integral product selected by its unique formula on root tensors.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-complex-comparisons). -/
def integralProductComplex (X : Scheme.{u}) (r s : ℕ) :=
  (integralProductComplex_existsUnique l E X r s).exists.choose

/-- The existing finite line as its degree-zero flat complex.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-complex-comparisons). -/
abbrev finiteComplex (X : Scheme.{u}) (n : ℕ) (r : ℕ) :=
  (CochainComplex.singleFunctor _ 0).obj (finiteCoefficientTwist l E X n (r : ℤ))

/-- Insert an ordered root tensor in degree zero at finite coefficients.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-complex-comparisons). -/
def finiteGenerator (X : Scheme.{u}) (n : ℕ) (r : ℕ) (U : X.ProEtᵒᵖ)
    (a : finiteTateCoefficient l E n) (x : Fin r → (purTwistZlOne X l).obj.obj U) :
    ((finiteComplex l E X n r).X 0).val.obj U :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (finiteCoefficientTwist l E X n (r :
    ℤ))).inv.val.app U
    (finiteTateProPowerGenerator l E n X U a r x)

/-- The canonical finite product of flat single complexes.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-complex-comparisons).
Proof: The total tensor has only its (0,0) summand. Concatenate the ordered
root lists and multiply the coefficients there. Splitting the list gives the
inverse; the tensor universal property proves uniqueness. Empty lists give the
unitors. Both differentials vanish, so these are maps of the entire complexes. -/
theorem finiteProductComplex_existsUnique (X : Scheme.{u}) (n : ℕ) (r s : ℕ) :
    ∃! e : (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)).obj
          (finiteComplex l E X n r, finiteComplex l E X n s) ≅
        finiteComplex l E X n (r + s),
      ∀ (U : X.ProEtᵒᵖ) (a b : finiteTateCoefficient l E n)
        (x : Fin r → (purTwistZlOne X l).obj.obj U)
        (y : Fin s → (purTwistZlOne X l).obj.obj U),
        (e.hom.f 0).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
            (integralCoefficientCommRingSheaf l E X n) (finiteComplex l E X n r) (finiteComplex l
              E X n s)
            0 0 0 (by omega) U
            (finiteGenerator l E X n r U a x) (finiteGenerator l E X n s U b y)) =
        finiteGenerator l E X n (r + s) U (a * b) (Fin.addCases x y) := by
  sorry

/-- The finite product selected by its unique formula on root tensors.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-complex-comparisons). -/
def finiteProductComplex (X : Scheme.{u}) (n : ℕ) (r s : ℕ) :=
  (finiteProductComplex_existsUnique l E X n r s).exists.choose

/-- The integral degree-zero line is a good flat-term K-flat representative.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-complex-comparisons).
Proof: Locally the line is the coefficient unit, including exponent zero.
It is flat, and its single complex is bounded and K-flat. Every other term is
zero and hence flat. These are the two clauses of integralOperationsGoodComplex. -/
theorem integralGood (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (r : ℕ) :
    integralOperationsGoodComplex l E X (integralComplex l E X r) := by
  obtain ⟨hK, hF, _⟩ :=
    SheafOfModules.FlatSingleDerivedNormalization.flat_single_derived_normalization
      (completedIntegralCommRingSheafUnrestricted l E X) (positiveLine l E X r)
      (coefficientTwistLine_exact X
        (R := completedIntegralCommRingSheafUnrestricted l E X)
        (purTwistIntegralModule X l E) (r : ℤ)).2
  exact ⟨hK, hF⟩

/-- The finite degree-zero line is K-flat at the full small-site coefficient size.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-complex-comparisons).
Proof: The roots line is locally free of rank one, as are all nonnegative
powers and the coefficient unit. Its degree-zero complex is a bounded complex
of flat modules, hence is K-flat against arbitrary coefficient-universe tests. -/
theorem finiteGood (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (n r : ℕ) :
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := integralCoefficientCommRingSheaf l E X n)
      (finiteComplex l E X n r) := by
  obtain ⟨hK, _⟩ :=
    SheafOfModules.FlatSingleDerivedNormalization.flat_single_derived_normalization
      (integralCoefficientCommRingSheaf l E X n)
      (finiteCoefficientTwist l E X n (r : ℤ))
      (coefficientTwistLine_exact X (purTwistFiniteOne X l E n) (r : ℤ)).2
  exact hK

end WeilConjectures.CanonicalTate
