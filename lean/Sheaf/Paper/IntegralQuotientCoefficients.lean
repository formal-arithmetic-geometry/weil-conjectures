/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Sheaf.Paper.CartesianCoefficients
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.Paper.PerfectProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Algebra.Homology.FlatScalarCyclicResolution
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Sheaf.Paper.SectionDerivedPushpullNormalization
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.ProjectionFormulaBaseChangeNaturality
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction

/-! # Integral quotient scalar comparison for unbounded direct image

Source: blueprint main-20261015, proper-base-change integral proof, paragraphs (1), (3);
Stacks Project, Tags 093M, 0D6D, 0D6E, 07A6 and 0944
(blueprint: def-sfb-integral-quotient-coefficients).

Positive quotient levels are indexed by n + 1. All categories are ordinary unbounded
derived categories of the recorded internal module objects. No completion is applied.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open MonoidalLeftAction
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The recorded continuous integral condensed ring.
Source: blueprint paragraph (1)
(blueprint: def-sfb-integral-quotient-coefficients). -/
abbrev integral := (sfbCondensedIntegers l E).X

/-- Commutativity is inherited from the continuous-map ring sheaf.
Source: blueprint paragraph (1)
(blueprint: def-sfb-integral-quotient-coefficients). -/
instance integral_comm : IsCommMonObj (integral l E) := by
  let := spectralNorm.normedField (Padic l) E
  exact Profinite.isCommMonObj_continuousMapRingObjOfUniverse
    (Padic.coefficientExtensionIntegers l E)

/-- The discrete topology on the existing finite quotient, at exponent n + 1.
Source: blueprint paragraph (1)
(blueprint: def-sfb-integral-quotient-coefficients). -/
instance quotientTopology (n : ℕ) :
    TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥

/-- The finite quotient has its discrete topology.
Source: blueprint paragraph (1)
(blueprint: def-sfb-integral-quotient-coefficients). -/
instance quotientDiscrete (n : ℕ) :
    DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := ⟨rfl⟩

/-- A discrete ring is a topological ring.
Source: blueprint paragraph (1)
(blueprint: def-sfb-integral-quotient-coefficients). -/
instance quotientTopologicalRing (n : ℕ) :
    IsTopologicalRing (Padic.coefficientExtensionRing l E (n + 1)) :=
  inferInstance

/-- The discrete finite condensed quotient, using the existing continuous-map construction.
Source: blueprint paragraph (1)
(blueprint: def-sfb-integral-quotient-coefficients). -/
abbrev finite (n : ℕ) :=
  Profinite.continuousMapRingObjOfUniverse.{u, u}
    (Padic.coefficientExtensionRing l E (n + 1))

/-- The finite condensed ring has the recorded ring-sheaf monoid structure.
Source: blueprint paragraph (1)
(blueprint: def-sfb-integral-quotient-coefficients). -/
instance finiteMonObj (n : ℕ) : MonObj (finite l E n) :=
  Sheaf.monObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafOfUniverse (Padic.coefficientExtensionRing l E (n + 1)))

/-- Commutativity is inherited from the finite quotient ring.
Source: blueprint paragraph (1)
(blueprint: def-sfb-integral-quotient-coefficients). -/
instance finite_comm (n : ℕ) : IsCommMonObj (finite l E n) :=
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse
    (Padic.coefficientExtensionRing l E (n + 1))

/-- Continuity of the actual quotient, rather than a choice of a finite projection.
Source: blueprint paragraph (1); the uniformizer coset basis of the integer topology
(blueprint: def-sfb-integral-quotient-coefficients).
Proof: the fibres of reduction are uniformizer-power cosets. The recorded coset basis
makes them open. A map to a discrete space with open fibres is continuous. -/
theorem reduction_continuous (n : ℕ) :
    @Continuous _ _ (Padic.coefficientExtensionIntegersTopology l E)
      (quotientTopology l E n)
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) := by
  sorry

/-- The actual finite projection on condensed coefficients, induced by postcomposition.
Source: blueprint paragraph (1)
(blueprint: def-sfb-integral-quotient-coefficients). -/
def reduction (n : ℕ) : integral l E ⟶ finite l E n :=
  letI := spectralNorm.normedField (Padic l) E
  Profinite.continuousMapRingObjMapOfUniverse
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))
    (reduction_continuous l E n)

/-- The finite projection is the underlying map of a morphism of ring sheaves.
Source: blueprint paragraph (1)
(blueprint: def-sfb-integral-quotient-coefficients). -/
instance reductionMonHom (n : ℕ) : IsMonHom (reduction l E n) := by
  let := spectralNorm.normedField (Padic l) E
  exact Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafMapOfUniverse
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))
      (reduction_continuous l E n))

/-- The scalar-extension functor in the quotient coefficient category.
Source: Stacks 06YY, blueprint paragraph (1)
(blueprint: def-sfb-integral-quotient-coefficients). -/
def scalar (T : Scheme.{u}) (n : ℕ) :=
  (Mod.extendScalars (coefficientMap (reduction l E n) T)).leftDerivedFunctor

/-- Exact scalar restriction, descended termwise to the unbounded derived category.
Source: Stacks 07A6, blueprint paragraph (1)
(blueprint: def-sfb-integral-quotient-coefficients). -/
def restrict (T : Scheme.{u}) (n : ℕ) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (finite l E n) T)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (integral l E) T)) :=
  (Mod.comap (C := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (coefficientMap (reduction l E n) T)).mapDerivedCategory

/-- The specified derived extension/restriction adjunction.
Source: Stacks 07A6, blueprint paragraph (1)
(blueprint: def-sfb-integral-quotient-coefficients). -/
def scalarAdjunction (T : Scheme.{u}) (n : ℕ) :
    scalar l E T n ⊣ restrict l E T n :=
  Mod.derivedExtendMapDerivedCategoryAdjunction _

end AlgebraicGeometry.ProEtale.IntegralQuotient

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual quotient transition for any two positive levels.
Source: blueprint paragraph (3)
(blueprint: def-sfb-integral-quotient-coefficients). -/
def transition (n m : ℕ) (h : m ≤ n) :
    Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l E (m + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- The induced condensed quotient transition is postcomposition by the quotient factor.
Source: blueprint paragraph (3)
(blueprint: def-sfb-integral-quotient-coefficients). -/
def finiteMap (n m : ℕ) (h : m ≤ n) : finite l E n ⟶ finite l E m :=
  Profinite.continuousMapRingObjMapOfUniverse
    (transition l E n m h) continuous_of_discreteTopology

/-- The actual transition is a homomorphism of the specified coefficient ring objects.
Source: blueprint paragraph (3)
(blueprint: def-sfb-integral-quotient-coefficients). -/
instance finiteMapMonHom (n m : ℕ) (h : m ≤ n) :
    IsMonHom (finiteMap l E n m h) :=
  Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafMapOfUniverse
      (transition l E n m h) continuous_of_discreteTopology)

/-- Multiplication by the actual uniformizer power on continuous integral sections.
Source: blueprint paragraph (1), cone of the uniformizer
(blueprint: def-sfb-integral-quotient-coefficients). -/
def multiplicationPoint (n : ℕ) : integral l E ⟶ integral l E := by
  letI := spectralNorm.normedField (Padic l) E
  refine ⟨{ app := fun S ↦ AddCommGrpCat.ofHom {
    toFun := fun x ↦ ULift.up
      ((ContinuousMap.const S.unop (Padic.coefficientExtensionUniformizer l E ^ (n + 1))) *
        x.down)
    map_zero' := by
      apply ULift.ext
      exact mul_zero _
    map_add' := by
      intro x y
      apply ULift.ext
      exact mul_add _ _ _ }, naturality := ?_ }⟩
  intro S T g
  rfl

/-- Multiplication by the scalar power on the pulled-back ring sheaf.
Source: blueprint paragraph (1)
(blueprint: def-sfb-integral-quotient-coefficients). -/
def multiplicationHom (T : Scheme.{u}) (n : ℕ) :
    condensedRingObj (integral l E) T ⟶ condensedRingObj (integral l E) T :=
  (upperStarFromPoint T).map (multiplicationPoint l E n)

/-- The scalar multiplication map is linear for the regular module structure.
Source: blueprint paragraph (1)
(blueprint: def-sfb-integral-quotient-coefficients).
Proof: on continuous sections it is multiplication by the fixed scalar pi^(n+1),
which commutes with multiplication by every section because the coefficient ring is
commutative. The monoidal inverse image preserves this equation. -/
theorem multiplication_linear (T : Scheme.{u}) (n : ℕ) :
    γ[condensedRingObj (integral l E) T,
      (Mod.regular (condensedRingObj (integral l E) T)).X] ≫
        multiplicationHom l E T n =
      condensedRingObj (integral l E) T ◁ multiplicationHom l E T n ≫
        γ[condensedRingObj (integral l E) T,
      (Mod.regular (condensedRingObj (integral l E) T)).X] := by
  sorry

/-- The linear endomorphism of the rank-one free module used in the displayed resolution.
Source: blueprint paragraph (1)
(blueprint: def-sfb-integral-quotient-coefficients). -/
def multiplication (T : Scheme.{u}) (n : ℕ) :
    Mod.regular (condensedRingObj (integral l E) T) ⟶
      Mod.regular (condensedRingObj (integral l E) T) :=
  Mod.Hom.mk' (multiplicationHom l E T n) (multiplication_linear l E T n)

/-- The cone of pi^(n+1) on the ring in degree zero, in degrees -1 and 0.
Source: blueprint paragraph (1)
(blueprint: def-sfb-integral-quotient-coefficients). -/
def resolution (T : Scheme.{u}) (n : ℕ) :=
  CochainComplex.mappingCone ((CochainComplex.singleFunctor _ 0).map
    (multiplication l E T n))

/-- The actual projection to the quotient is linear after scalar restriction.
Source: blueprint paragraph (1)
(blueprint: def-sfb-integral-quotient-coefficients).
Proof: the projection is a homomorphism of the coefficient ring objects. Its multiplicative
compatibility is exactly linearity into the restricted regular quotient module. -/
theorem projection_linear (T : Scheme.{u}) (n : ℕ) :
    γ[condensedRingObj (integral l E) T,
      (Mod.regular (condensedRingObj (integral l E) T)).X] ≫
        coefficientMap (reduction l E n) T =
      condensedRingObj (integral l E) T ◁ coefficientMap (reduction l E n) T ≫
        γ[condensedRingObj (integral l E) T, ((Mod.comap (coefficientMap (reduction l E n) T)).obj
          (Mod.regular (condensedRingObj (finite l E n) T))).X] := by
  sorry

/-- The augmentation in degree zero is the actual finite projection.
Source: blueprint paragraph (1)
(blueprint: def-sfb-integral-quotient-coefficients). -/
def projection (T : Scheme.{u}) (n : ℕ) :
    Mod.regular (condensedRingObj (integral l E) T) ⟶
      (Mod.comap (coefficientMap (reduction l E n) T)).obj
        (Mod.regular (condensedRingObj (finite l E n) T)) :=
  Mod.Hom.mk' (coefficientMap (reduction l E n) T) (projection_linear l E T n)

end AlgebraicGeometry.ProEtale.IntegralQuotient

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual finite projections commute with every quotient transition.
Source: blueprint paragraph (3)
(blueprint: def-sfb-integral-quotient-coefficients).
Proof: on each continuous section and each point both composites take its class modulo
pi^(m+1). The quotient factor is defined by this equality on quotient generators, and
postcomposition of continuous functions preserves the equality. -/
theorem reduction_comp (n m : ℕ) (h : m ≤ n) :
    reduction l E n ≫ finiteMap l E n m h = reduction l E m := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralQuotient
