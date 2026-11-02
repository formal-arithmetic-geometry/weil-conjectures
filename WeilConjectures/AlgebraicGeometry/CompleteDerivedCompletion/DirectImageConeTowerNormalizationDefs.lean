/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompletePullbackReduction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# Normalization predicates for the direct-image reduction cone tower

Source: `literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/prop-weil-pbc-direct-image-limits.proof.md`, proof (2),
the strict equality of reduction towers on a K-injective representative
(blueprint: `def-weil-pbc-direct-image-cone-tower-normalizations`).

The comparison is normalized on both summands of every mapping cone in every
tower level. The final clause records its K-injective realization through the
canonical right-derived-functor units and the direct-image mate.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived AdicCompletion.finiteRingMonoidalObject
  AdicCompletion.finiteRingCommutative AdicCompletion.finiteModulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

/-- The canonical identification used to normalize the constant cone summands.
Source: proof (2), the tensor-unit comparison under direct image (blueprint:
`def-weil-pbc-direct-image-cone-tower-normalizations`). -/
def constantPushIso :
    constant l E X ⋙ push l E f ≅
      CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f ⋙ constant l E Y :=
  NatIso.ofComponents
    (fun M ↦ Functor.constComp ℕᵒᵖ M
      (CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f))
    (by intros M N g; rfl)

/-- The strict comparison is normalized on both cone summands in all degrees and
levels, and is natural in the input complex. Source: proof (2), the strict
scalar-cone calculation
(blueprint: `def-weil-pbc-direct-image-cone-tower-normalizations`). -/
def IsStrictDirectImageConeTower
    (e : strictRed l E X ⋙ (push l E f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      Functor.mapHomologicalComplex
        (CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f) (ComplexShape.up ℤ) ⋙
        strictRed l E Y) : Prop :=
  (∀ (I : CochainComplex (AdicCompletion.Modules l E X) ℤ) (i : ℤ) (n : ℕ),
    ((push l E f).map
        ((CochainComplex.mappingCone.inl ((complexPowerMap l E X).app I)).v
          (i + 1) i (by omega))).app (op n) ≫
        ((e.hom.app I).f i).app (op n) =
      ((constantPushIso l E f).hom.app (I.X (i + 1))).app (op n) ≫
        ((CochainComplex.mappingCone.inl ((complexPowerMap l E Y).app
          (((CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f).mapHomologicalComplex
            (.up ℤ)).obj I))).v (i + 1) i (by omega)).app (op n)) ∧
  (∀ (I : CochainComplex (AdicCompletion.Modules l E X) ℤ) (i : ℤ) (n : ℕ),
    ((push l E f).map
        ((CochainComplex.mappingCone.inr ((complexPowerMap l E X).app I)).f i)).app
      (op n) ≫ ((e.hom.app I).f i).app (op n) =
      ((constantPushIso l E f).hom.app (I.X i)).app (op n) ≫
        ((CochainComplex.mappingCone.inr ((complexPowerMap l E Y).app
          (((CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f).mapHomologicalComplex
            (.up ℤ)).obj I))).f i).app (op n))

/-- The K-injective normalization of the strict comparison. For a K-injective
complex, the canonical module right-derived unit, the direct-image mate, and
`redFactors` agree with the strict map and the tower right-derived unit.
Source: proof (2), K-injective representative calculation (blueprint:
`def-weil-pbc-direct-image-cone-tower-normalizations`). -/
def IsKInjectiveDirectImageNormalization
    (e : strictRed l E X ⋙ (push l E f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      Functor.mapHomologicalComplex
        (CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f) (ComplexShape.up ℤ) ⋙
        strictRed l E Y) : Prop :=
  ∀ (I : CochainComplex (AdicCompletion.Modules l E X) ℤ)
    (_hI : I.IsKInjective),
    (red l E Y).map
        ((CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f).rightDerivedFunctorUnitQ I) ≫
      (mateEquiv (moduleAdjunction l E f) (towerAdjunction l E f)
        (.mk _ _ _ _ (pullReduction l E f).hom)).natTrans.app
        (DerivedCategory.Q.obj I) ≫
      (rpush l E f).map ((redFactors l E X).hom.app I) =
    (redFactors l E Y).hom.app
        (((CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f).mapHomologicalComplex
          (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((e.inv.app I)) ≫
      (push l E f).rightDerivedFunctorUnitQ ((strictRed l E X).obj I)

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
