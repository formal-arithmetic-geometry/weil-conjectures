/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.Paper.PodCompletionTensorNormalization

/-! # Naturality part of strict tensor tower reindexing

Source: blueprint prop-pod-dual-tate-data-compatibility, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-reindexing-strict-tensor-towers).

The missing argument evaluates both naturality composites on pure tensor
summands. This component assumes the generator formula and concludes only the
naturality square, so it is strictly smaller than the full assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Naturality of a generator-compatible strict tower family.
Source: blueprint prop-pod-dual-tate-data-compatibility, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-reindexing-strict-tensor-towers).
The generator equation is an explicit hypothesis, and the conclusion is only
the naturality square for maps of good complexes.
-/
theorem podReindexingStrictTensorTowersNaturality
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) 
    (τ : ∀ P Q : (integralOperationsGoodComplex l E Y).FullSubcategory,
        (podReindexTower l E g).obj
            ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj,Q.obj)) ≅
          (integralOperationsTensorTowerFunctor l E X).obj
            (((podGoodReindex l E g D).obj P).obj,((podGoodReindex l E g D).obj Q).obj))
    (hgen : ∀ (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (n : ℕ) (p q : ℤ) (U : X.ProEt)
        (x : (((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj).X p).val.obj
          (op ((proEtaleIsoPostcompose g).obj U)))
        (y : (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X q).val.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        ((((τ P Q).hom.app (op n)).f (p + q)).val.app (op U))
            (integralOperationsTotalTensorSection l E Y n P.obj Q.obj p q
              (op ((proEtaleIsoPostcompose g).obj U)) x y) =
          integralOperationsTotalTensorSection l E X n
            (((podGoodReindex l E g D).obj P).obj) (((podGoodReindex l E g D).obj Q).obj)
            p q (op U) ((((D.quotient P.obj P.property n).hom.f p).val.app (op U)) x)
              ((((D.quotient Q.obj Q.property n).hom.f q).val.app (op U)) y)) :
      ∀ (P Q P' Q' : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (a : P ⟶ P') (b : Q ⟶ Q'),
        (podReindexTower l E g).map
            ((integralOperationsTensorTowerFunctor l E Y).map (Prod.mkHom a.hom b.hom)) ≫
            (τ P' Q').hom =
          (τ P Q).hom ≫ (integralOperationsTensorTowerFunctor l E X).map
            (Prod.mkHom ((podGoodReindex l E g D).map a).hom
              ((podGoodReindex l E g D).map b).hom) := by
  sorry

end WeilConjectures
