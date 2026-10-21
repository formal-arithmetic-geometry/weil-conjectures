/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.LisseRationalRealizationData
public import Sheaf.SixFunctors.ConstructibleTensorCompletion

/-! # Canonically normalized lisse realization

Source: Bhatt--Scholze, Lemma 6.8.2, Definition 6.8.3, Proposition 6.8.4(1),(4),(6),
Proposition 6.8.14(2), Remark 6.8.15, pp. 58--62
(blueprint: def-real-lisse-tensor-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme MonoidalCategory
open scoped TensorProduct MonoidalCategory
namespace WeilConjectures.LisseRealization
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
/-- Scalar extension to the normalized rational coefficient sheaf.
Source: BS 6.8.2 (blueprint: def-real-lisse-tensor-normalization). -/
abbrev scalar {X : Base D l hl} (a : At D l hl E X) :=
  a.completion.hom ≫ integralRationalCoefficientMap l E X.scheme

/-- Termwise ordinary scalar extension of an integral complex.
Source: BS 6.8.14(2) (blueprint: def-real-lisse-tensor-normalization). -/
abbrev rationalComplex {X : Base D l hl} (a : At D l hl E X)
    (P : CochainComplex (integralTowerModules l E X.scheme) ℤ) :=
  ((pbcExtend (scalar D l hl E a)).mapHomologicalComplex (.up ℤ)).obj P

/-- The existing signed total tensor over the rational sheaf, without completion.
Source: Stacks 06YN (blueprint: def-real-lisse-tensor-normalization). -/
abbrev ordinaryTotal {X : Base D l hl}
    (P Q : CochainComplex (Modules D l hl E X) ℤ) :=
  (coefficientTotalTensor.{u + 1} (ProEt.topology X.scheme)
    (rationalCoefficientSheaf l X.scheme E)).obj (P, Q)

/-- A cycle pairing is characterized by its values on local cocycles. The cycle z is
quantified with its actual injection, so this fixes the map through the two homology quotients.
Source: Stacks 06YN (blueprint: def-real-lisse-tensor-normalization). -/
structure HomologyTensor {X : Base D l hl}
    (P Q : CochainComplex (Modules D l hl E X) ℤ) where
  pairing : P.homology 0 ⊗ Q.homology 0 ⟶ (ordinaryTotal D l hl E P Q).homology 0
  sections : ∀ (U : X.scheme.ProEtᵒᵖ)
    (x : (P.cycles 0).val.obj U) (y : (Q.cycles 0).val.obj U)
    (z : ((ordinaryTotal D l hl E P Q).cycles 0).val.obj U),
    ((ordinaryTotal D l hl E P Q).iCycles 0).val.app U z =
      coefficientTensorGenerator.{u + 1} (ProEt.topology X.scheme)
        (rationalCoefficientSheaf l X.scheme E) P Q 0 0 0 (by omega) U
        ((P.iCycles 0).val.app U x) ((Q.iCycles 0).val.app U y) →
    pairing.val.app U
      (pure D l hl E (P.homology 0) (Q.homology 0) U
        ((P.homologyπ 0).val.app U x) ((Q.homologyπ 0).val.app U y)) =
      (((ordinaryTotal D l hl E P Q).homologyπ 0).val.app U z)

/-- The cohomology comparison on an integral representative is the universal derived counit,
not a chosen basis. This also fixes its value on every local free model.
Source: BS 6.8.14(2); Stacks 06YY (blueprint: def-real-lisse-tensor-normalization). -/
structure Model {X : Base D l hl} (a : At D l hl E X)
    (K : sfIntegralConstructibleCategory l E X.scheme)
    (P : CochainComplex (integralTowerModules l E X.scheme) ℤ)
    (e : DerivedCategory.Q.obj P ≅ K.obj) where
  comparison : (a.sheaf D l hl E).obj
      ((sfRationalConstructibleLocalization l E X.scheme).obj K) ≅
    (rationalComplex D l hl E a P).homology 0
  normalized : comparison.hom =
    (DerivedCategory.homologyFunctor _ 0).map
      (a.integral.hom.app K ≫ (pbcDerivedExtend (scalar D l hl E a)).map e.inv ≫
        pbcComplexCounit (scalar D l hl E a) P) ≫
      (DerivedCategory.homologyFunctorFactors _ 0).hom.app
        (rationalComplex D l hl E a P)

/-- Completion and scalar comparison on two good representatives. The finite quotient
coordinates and zero shifted component fix chi; the scalar map is fixed on pure tensors.
Source: BS 6.8.15; the specified completion map of
lem-fix-constructible-tensor-completion (blueprint: def-real-lisse-tensor-normalization). -/
structure TensorModel {X : Base D l hl} (a : At D l hl E X)
    (K L : sfIntegralConstructibleCategory l E X.scheme)
    (P Q : (integralOperationsGoodComplex l E X.scheme).FullSubcategory)
    (eP : DerivedCategory.Q.obj P.obj ≅ K.obj)
    (eQ : DerivedCategory.Q.obj Q.obj ≅ L.obj) where
  chi : (constructibleTensorTotal l E X.scheme).obj (P.obj, Q.obj) ⟶
    (integralOperationsTensorComplexFunctor l E X.scheme).obj (P.obj, Q.obj)
  quotients : ∀ (p q : ℤ) (n : ℕ) (U : X.scheme.ProEtᵒᵖ)
    (x : (P.obj.X p).val.obj U) (y : (Q.obj.X q).val.obj U),
    (((chi ≫ CochainComplex.mappingCocone.fst
      (constructibleTensorBoundary l E X.scheme P.obj Q.obj) ≫
      Pi.π (fun n ↦ (integralOperationsTensorLevel l E X.scheme n).obj (P.obj, Q.obj)) n).f
        (p + q)).val.app U)
      (constructibleTensorTotalSection l E X.scheme P.obj Q.obj p q U x y) =
    integralOperationsTotalTensorSection l E X.scheme n P.obj Q.obj p q U
      (unrestrictedIntegralTensorSection l E X.scheme n (P.obj.X p) U 1 x)
      (unrestrictedIntegralTensorSection l E X.scheme n (Q.obj.X q) U 1 y)
  shifted : ∀ (i j : ℤ) (h : i + -1 = j), chi.f i ≫
    (CochainComplex.mappingCocone.snd
      (constructibleTensorBoundary l E X.scheme P.obj Q.obj)).v i j h = 0
  completed : DerivedCategory.Q.obj
      ((constructibleTensorTotal l E X.scheme).obj (P.obj, Q.obj)) ≅
    (integralCompletedTensor l E X.scheme).obj (K.obj, L.obj)
  completed_normalized : completed.hom =
    DerivedCategory.Q.map chi ≫
      (integralCompletedTensorComparison l E X.scheme).inv.app (P, Q) ≫
      (integralCompletedTensor l E X.scheme).map (Prod.mkHom eP.hom eQ.hom)
  scalar : rationalComplex D l hl E a
      ((constructibleTensorTotal l E X.scheme).obj (P.obj, Q.obj)) ≅
    ordinaryTotal D l hl E (rationalComplex D l hl E a P.obj)
      (rationalComplex D l hl E a Q.obj)
  scalar_sections : ∀ (p q : ℤ) (U : X.scheme.ProEtᵒᵖ)
    (c : (rationalCoefficientSheaf l X.scheme E).obj.obj U)
    (x : (P.obj.X p).val.obj U) (y : (Q.obj.X q).val.obj U),
    (scalar.hom.f (p + q)).val.app U
      (pbcTensorSection (LisseRealization.scalar D l hl E a)
        (((constructibleTensorTotal l E X.scheme).obj (P.obj, Q.obj)).X (p + q)) U c
        (constructibleTensorTotalSection l E X.scheme P.obj Q.obj p q U x y)) =
    coefficientTensorGenerator.{u + 1} (ProEt.topology X.scheme)
      (rationalCoefficientSheaf l X.scheme E)
      (rationalComplex D l hl E a P.obj) (rationalComplex D l hl E a Q.obj)
      p q (p + q) rfl U
      (pbcTensorSection (LisseRealization.scalar D l hl E a) (P.obj.X p) U 1 x)
      (pbcTensorSection (LisseRealization.scalar D l hl E a) (Q.obj.X q) U c y)
  integral : a.J.obj ((tensor D l hl E X).obj
      ((sfRationalConstructibleLocalization l E X.scheme).obj K,
        (sfRationalConstructibleLocalization l E X.scheme).obj L)) ≅
    (pbcDerivedExtend (LisseRealization.scalar D l hl E a)).obj
      ((integralCompletedTensor l E X.scheme).obj (K.obj, L.obj))
  integral_normalized : HEq integral.hom
    (a.integral.hom.app ((constructibleIntegralTensor l E X.scheme).obj (K, L)))
  comparison : (a.sheaf D l hl E).obj ((tensor D l hl E X).obj
      ((sfRationalConstructibleLocalization l E X.scheme).obj K,
        (sfRationalConstructibleLocalization l E X.scheme).obj L)) ≅
    (ordinaryTotal D l hl E (rationalComplex D l hl E a P.obj)
      (rationalComplex D l hl E a Q.obj)).homology 0
  normalized : comparison.hom = (DerivedCategory.homologyFunctor _ 0).map
      (integral.hom ≫ (pbcDerivedExtend (LisseRealization.scalar D l hl E a)).map completed.inv ≫
        pbcComplexCounit (LisseRealization.scalar D l hl E a)
          ((constructibleTensorTotal l E X.scheme).obj (P.obj, Q.obj)) ≫
        DerivedCategory.Q.map scalar.hom) ≫
      (DerivedCategory.homologyFunctorFactors _ 0).hom.app
        (ordinaryTotal D l hl E (rationalComplex D l hl E a P.obj)
          (rationalComplex D l hl E a Q.obj))

/-- The tensor comparison is precisely the preceding derived scalar-extension map.
Source: BS 6.8.15 (blueprint: def-real-lisse-tensor-normalization). -/
structure TensorNormalized (X : Base D l hl) (a : At D l hl E X)
    (t : TensorAt D l hl E X a) where
  models : ∀ (K L : sfIntegralConstructibleCategory l E X.scheme)
    (hK : Lisse D l hl E X ((sfRationalConstructibleLocalization l E X.scheme).obj K))
    (hL : Lisse D l hl E X ((sfRationalConstructibleLocalization l E X.scheme).obj L))
    (P Q : (integralOperationsGoodComplex l E X.scheme).FullSubcategory)
    (eP : DerivedCategory.Q.obj P.obj ≅ K.obj) (eQ : DerivedCategory.Q.obj Q.obj ≅ L.obj),
    ∃ (mK : Model D l hl E a K P.obj eP) (mL : Model D l hl E a L Q.obj eQ)
      (mT : TensorModel D l hl E a K L P Q eP eQ)
      (h : HomologyTensor D l hl E (rationalComplex D l hl E a P.obj)
        (rationalComplex D l hl E a Q.obj)),
      (mK.comparison.hom ⊗ₘ mL.comparison.hom) ≫ h.pairing ≫ mT.comparison.inv =
        (t.tensor _ _ hK hL).inv


end WeilConjectures.LisseRealization
