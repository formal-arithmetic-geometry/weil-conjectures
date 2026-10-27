/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismExistence

/-! Six-arrow normalization for a factorized integral scalar morphism. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (P : CoefficientConstruction l (ULift.{u} (PadicAlgCl l)) D hl (f := f))
  (c : Compactification f)

/--
Given the factorized natural transformation, its integral representative has the
six-arrow formula. This is the component calculation in the construction of the
native compact-support scalar morphism.
Source: Bhatt--Scholze, Definition 6.7.6, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-native-integral-scalar-morphism-normalization).
-/
theorem native_integral_scalar_morphism_normalization [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (stage : StageAction l D hl P c)
    (change : ∀ E : Index l (PadicAlgCl l),
      PurCompactSupport.Change (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (hs : ∀ E, (change E).map X = (source.coefficient E).integralMap l X)
    (ht : ∀ E, (change E).map Y = (target.coefficient E).integralMap l Y)
    (E : Index l (PadicAlgCl l))
    (tau : sfRationalConstructibleLocalization l
        (Coefficient l (PadicAlgCl l) E) X ⋙
        finiteSourceAux l D hl P c target stage E ⟶
      sfRationalConstructibleLocalization l
        (Coefficient l (PadicAlgCl l) E) X ⋙
        finiteTargetAux l c source E)
    (hfac : ∀ K : finiteTorConstructibleIntegralCategory l
        (Coefficient l (PadicAlgCl l) E) X,
      ∃ (b : (sections l Y).mapDerivedCategory.obj
            ((sfRationalConstructibleLocalization l
              (Coefficient l (PadicAlgCl l) E) X ⋙
              finiteSourceAux l D hl P c target stage E).obj
                ((PurCompactSupport.finiteTorIntegralInclusion l
                  (Coefficient l (PadicAlgCl l) E) X).obj K)) ≅
          (PurCompactSupport.image (PurCompactSupport.completed l
            (Coefficient l (PadicAlgCl l) E)) c ⋙
            pbcDerivedExtend ((change E).map Y)).obj K.obj)
        (d : (pbcDerivedExtend ((change E).map X) ⋙
            PurCompactSupport.image (nativeCoefficients l) c).obj K.obj ≅
          (sections l Y).mapDerivedCategory.obj
            ((sfRationalConstructibleLocalization l
              (Coefficient l (PadicAlgCl l) E) X ⋙
              finiteTargetAux l c source E).obj
                ((PurCompactSupport.finiteTorIntegralInclusion l
                  (Coefficient l (PadicAlgCl l) E) X).obj K))),
        (sections l Y).mapDerivedCategory.map
            (tau.app ((PurCompactSupport.finiteTorIntegralInclusion l
              (Coefficient l (PadicAlgCl l) E) X).obj K)) =
          b.hom ≫ (PurCompactSupport.comparison (change E) c).app K.obj ≫ d.hom)
    (K : finiteTorConstructibleIntegralCategory l
      (Coefficient l (PadicAlgCl l) E) X) :
    let rationalInput :=
      (rationalization l (ULift.{u} (PadicAlgCl l)) (finiteField l E) X).obj K
    let input := (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj rationalInput
    ∃ (A B : sfRationalConstructibleCategory l
          (Coefficient l (PadicAlgCl l) E) Y) (r : A ⟶ B),
      HEq r ((P.ring.rationalLeft c (finiteField l E)).hom.app rationalInput) ∧
    ∃ (M₁ M₂ M₃ M₄ M₅ : DerivedCategory
          (proEtaleRingModules Y (ringSheaf l Y)))
      (a₀ : (sections l Y).mapDerivedCategory.obj
        ((sfRationalConstructibleLocalization l
          (Coefficient l (PadicAlgCl l) E) X ⋙
          finiteSourceAux l D hl P c target stage E).obj
            ((PurCompactSupport.finiteTorIntegralInclusion l
              (Coefficient l (PadicAlgCl l) E) X).obj K)) ⟶ M₁)
      (a₁ : M₁ ⟶ M₂) (a₂ : M₂ ⟶ M₃) (a₃ : M₃ ⟶ M₄) (a₄ : M₄ ⟶ M₅)
      (a₅ : M₅ ⟶ (sections l Y).mapDerivedCategory.obj
        ((sfRationalConstructibleLocalization l
          (Coefficient l (PadicAlgCl l) E) X ⋙
          finiteTargetAux l c source E).obj
            ((PurCompactSupport.finiteTorIntegralInclusion l
              (Coefficient l (PadicAlgCl l) E) X).obj K))),
      HEq a₀ ((sections l Y).mapDerivedCategory.map
        (target.J.map ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := Y) E).map r))) ∧
      HEq a₁ ((target.integral E).hom.app
          ((sfCompactSupportFiniteIntegralFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c
            (Coefficient l (PadicAlgCl l) E)).obj
              ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₂ ((pbcDerivedExtend ((target.coefficient E).integralMap l Y)).map
          ((sfQcqsCompactSupportRealization l (Coefficient l (PadicAlgCl l) E)
            D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c).inv.app
              ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₃ ((PurCompactSupport.comparison (change E) c).app K.obj) ∧
      HEq a₄ ((PurCompactSupport.image (nativeCoefficients l) c).map
          ((source.integral E).inv.app
            ((PurCompactSupport.finiteTorIntegralInclusion l
              (Coefficient l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₅ ((operationTransport l c).inv.app (source.J.obj input)) ∧
      (sections l Y).mapDerivedCategory.map
          (tau.app ((PurCompactSupport.finiteTorIntegralInclusion l
            (Coefficient l (PadicAlgCl l) E) X).obj K)) =
        a₀ ≫ a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅ := by
  sorry

end WeilConjectures.LocallyFiniteAdicCompactSupport
