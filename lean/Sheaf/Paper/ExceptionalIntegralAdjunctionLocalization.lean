/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M6
-/
module

public import Sheaf.Paper.ConstructibleExceptionalCoefficientConstructionData
import all Sheaf.Paper.SfRationalLocalizationOrthogonality

/-! # Raw localization of one integral linear adjunction

Source: Zheng, Construction 6.2, localization of the integral coefficient category.
The functors below are actual tensor extensions, with no choice of object or arrow maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] HasDerivedCategory.standard Padic
  WeilConjectures.sfIntegralConstructible WeilConjectures.sfRationalTriangulationDatum
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v w
open CategoryTheory AlgebraicGeometry TensorProduct
namespace WeilConjectures.ConstructibleExceptionalCoefficients
attribute [local instance] Operation.leftAdditive Operation.rightAdditive
  Operation.leftShift Operation.rightShift
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (E : FieldStage.{max u v} l) (X Y : Scheme.{max u v})

/-- Change only the membership proof of an integral representative.
Source: the full-subcategory step of Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
def integralRepresentative
    (h : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X) :
    sfIntegralConstructibleCategory l E.carrier X ⥤ C.{u, v} l Ω X (.integral E) where
  obj K := ⟨K.obj, h ▸ K.property⟩
  map f := ObjectProperty.homMk f.hom

/-- Extend the domain of an integral functor by the literal full inclusions.
Source: Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
def fullIntegralFunctor
    (F : C.{u, v} l Ω X (.integral E) ⥤ C.{u, v} l Ω Y (.integral E))
    (h : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X) :
    sfIntegralConstructibleCategory l E.carrier X ⥤ sfIntegralConstructibleCategory l E.carrier Y :=
  integralRepresentative l Ω E X h ⋙ F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y

/-- The proof-changing representative functor is additive.
Source: the tensor Hom construction in Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
instance integralRepresentativeAdditive (h) :
    (integralRepresentative l Ω E X h).Additive where
  map_add := by intros; rfl

/-- The proof-changing representative functor is integral-linear.
Source: the tensor Hom construction in Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
instance integralRepresentativeLinear (h) :
    (integralRepresentative l Ω E X h).Linear (Padic.coefficientExtensionIntegers l E.carrier) where
  map_smul := by intros; rfl

/-- The literal full integral inclusion is additive.
Source: the tensor Hom construction in Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
instance integralInclusionAdditive (l : ℕ) [Fact l.Prime]
    (E : FieldStage.{w} l) (X : Scheme.{w}) :
    (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).Additive where
  map_add := by intros; rfl

/-- The literal full integral inclusion is integral-linear.
Source: the tensor Hom construction in Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
instance integralInclusionLinear (l : ℕ) [Fact l.Prime]
    (E : FieldStage.{w} l) (X : Scheme.{w}) :
    (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).Linear
      (Padic.coefficientExtensionIntegers l E.carrier) where
  map_smul := by intros; rfl

/-- The full-domain functor is additive, since both inclusions are literal.
Source: Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
instance fullIntegralFunctorAdditive
    (F : C.{u, v} l Ω X (.integral E) ⥤ C.{u, v} l Ω Y (.integral E))
    [F.Additive] (h) : (fullIntegralFunctor l Ω E X Y F h).Additive := by
  dsimp only [fullIntegralFunctor]
  infer_instance

/-- The full-domain functor preserves integral scalar multiplication.
Source: Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
instance fullIntegralFunctorLinear
    (F : C.{u, v} l Ω X (.integral E) ⥤ C.{u, v} l Ω Y (.integral E))
    [F.Linear (Padic.coefficientExtensionIntegers l E.carrier)] (h) :
    (fullIntegralFunctor l Ω E X Y F h).Linear
      (Padic.coefficientExtensionIntegers l E.carrier) := by
  dsimp only [fullIntegralFunctor]
  infer_instance

/-- Tensor extension of a linear functor preserves identities and composition.
Source: the tensor Hom construction in Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
theorem rawTensorFunctorLaws
    {R : Type*} [CommRing R] {B C : Type*} [Category B] [Category C]
    [Preadditive B] [Preadditive C] [Linear R B] [Linear R C]
    (p : R) (F : B ⥤ C) [F.Additive] [F.Linear R] :
    (∀ K : B, (F.mapLinearMap R).baseChange (Localization.Away p)
      (1 ⊗ₜ[R] 𝟙 K) = 1 ⊗ₜ[R] 𝟙 (F.obj K)) ∧
    (∀ (K L M : B) (a : Localization.Away p ⊗[R] (K ⟶ L))
        (b : Localization.Away p ⊗[R] (L ⟶ M)),
      (F.mapLinearMap R).baseChange (Localization.Away p)
        (ScalarLocalization.composition R B p K L M b a) =
      ScalarLocalization.composition R C p (F.obj K) (F.obj L) (F.obj M)
        ((F.mapLinearMap R).baseChange (Localization.Away p) b)
        ((F.mapLinearMap R).baseChange (Localization.Away p) a)) := by
  constructor
  · intro K
    change (1 : Localization.Away p) ⊗ₜ[R] F.map (𝟙 K) = _
    rw [F.map_id]
  · intro K L M a b
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul b g =>
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul a h =>
        rw [ScalarLocalization.composition_tmul]
        change (b * a) ⊗ₜ[R] F.map (h ≫ g) =
          ScalarLocalization.composition R C p (F.obj K) (F.obj L) (F.obj M)
            (b ⊗ₜ[R] F.map g) (a ⊗ₜ[R] F.map h)
        rw [ScalarLocalization.composition_tmul, F.map_comp]
      | add a a' ha ha' => simp [map_add, ha, ha']
    | add b b' hb hb' => simp [map_add, hb, hb']

/-- The rational functor sends each tensor to the tensor of the integral image.
Source: Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
def rawRationalFunctor
    (F : C.{u, v} l Ω X (.integral E) ⥤ C.{u, v} l Ω Y (.integral E))
    [F.Additive] [F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    (h : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X) :
    C.{u, v} l Ω X (.rational E) ⥤ C.{u, v} l Ω Y (.rational E) where
  obj K := ⟨(fullIntegralFunctor l Ω E X Y F h).obj K.obj⟩
  map f := ((fullIntegralFunctor l Ω E X Y F h).mapLinearMap
    (Padic.coefficientExtensionIntegers l E.carrier)).baseChange
      (Localization.Away (Padic.coefficientExtensionUniformizer l E.carrier)) f
  map_id K := (rawTensorFunctorLaws _ (fullIntegralFunctor l Ω E X Y F h)).1 K.obj
  map_comp f g := (rawTensorFunctorLaws _ (fullIntegralFunctor l Ω E X Y F h)).2 _ _ _ f g

/-- Canonical endpoint shift on raw rationalization, chosen without an operation.
Source: the inherited shifts of the two full coefficient subcategories
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
@[instance_reducible]
def integralRationalizationShift : (rationalization.{u, v} l Ω E X).CommShift ℤ := by
  letI : (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).CommShift ℤ :=
    Functor.CommShift.ofComp
      (show PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        (sfIntegralConstructible l E.carrier X).ι ≅
          (finiteTorConstructibleIntegral l E.carrier X).ι from Iso.refl _) ℤ
  infer_instance

/-- Only the adjunction and exact structures on the two explicitly constructed functors.
Source: Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
structure RawLocalizedAdjunction
    (A : Operation.{u, v} l Ω X Y (.integral E))
    [A.F.Additive] [A.G.Additive]
    [A.F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    [A.G.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    (hX : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X)
    (hY : sfIntegralConstructible l E.carrier Y =
      finiteTorConstructibleIntegral l E.carrier Y) where
  adjunction : rawRationalFunctor l Ω E X Y A.F hX ⊣ rawRationalFunctor l Ω E Y X A.G hY
  [leftShift : (rawRationalFunctor l Ω E X Y A.F hX).CommShift ℤ]
  [rightShift : (rawRationalFunctor l Ω E Y X A.G hY).CommShift ℤ]
  leftExact : (rawRationalFunctor l Ω E X Y A.F hX).IsTriangulated
  rightExact : (rawRationalFunctor l Ω E Y X A.G hY).IsTriangulated
  unitShift : adjunction.unit.CommShift ℤ
  counitShift : adjunction.counit.CommShift ℤ

variable {X Y}

/-- Package the exact structures; both functor data are the explicit tensor extensions.
Source: Zheng, Construction 6.2
(blueprint: lem-sf-integral-adjunction-raw-localization). -/
def RawLocalizedAdjunction.operation
    {A : Operation.{u, v} l Ω X Y (.integral E)}
    [A.F.Additive] [A.G.Additive]
    [A.F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    [A.G.Linear (Padic.coefficientExtensionIntegers l E.carrier)] {hX hY}
    (R : RawLocalizedAdjunction l Ω E X Y A hX hY) :
    Operation.{u, v} l Ω X Y (.rational E) where
  F := rawRationalFunctor l Ω E X Y A.F hX
  G := rawRationalFunctor l Ω E Y X A.G hY
  adjunction := R.adjunction
  leftAdditive := ⟨by intros; exact map_add _ _ _⟩
  rightAdditive := ⟨by intros; exact map_add _ _ _⟩
  leftShift := R.leftShift
  rightShift := R.rightShift
  leftExact := R.leftExact
  rightExact := R.rightExact
  unitShift := R.unitShift
  counitShift := R.counitShift

private def integralRepresentativeEquivalence (T : Scheme.{max u v})
    (h : sfIntegralConstructible l E.carrier T = finiteTorConstructibleIntegral l E.carrier T) :
    sfIntegralConstructibleCategory l E.carrier T ≌ C.{u, v} l Ω T (.integral E) where
  functor := integralRepresentative l Ω E T h
  inverse := PurCompactSupport.finiteTorIntegralInclusion l E.carrier T
  unitIso := NatIso.ofComponents
    (fun _ ↦ ObjectProperty.isoMk _ (Iso.refl _)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents
    (fun _ ↦ ObjectProperty.isoMk _ (Iso.refl _)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  functor_unitIso_comp K := by
    apply ObjectProperty.hom_ext
    change 𝟙 K.obj ≫ 𝟙 K.obj = 𝟙 K.obj
    exact Category.id_comp _

private def fullIntegralAdjunction
    (A : Operation.{u, v} l Ω X Y (.integral E))
    (hX : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X)
    (hY : sfIntegralConstructible l E.carrier Y = finiteTorConstructibleIntegral l E.carrier Y) :
    fullIntegralFunctor l Ω E X Y A.F hX ⊣ fullIntegralFunctor l Ω E Y X A.G hY :=
  ((integralRepresentativeEquivalence l Ω E X hX).toAdjunction.comp A.adjunction).comp
    (integralRepresentativeEquivalence l Ω E Y hY).symm.toAdjunction

private theorem rawRationalFactor
    (F : C.{u, v} l Ω X (.integral E) ⥤ C.{u, v} l Ω Y (.integral E))
    [F.Additive] [F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    (hX : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X) :
    sfRationalConstructibleLocalization l E.carrier X ⋙ rawRationalFunctor l Ω E X Y F hX =
      fullIntegralFunctor l Ω E X Y F hX ⋙ sfRationalConstructibleLocalization l E.carrier Y := by
  exact sfLocalization_factor l E.carrier (fullIntegralFunctor l Ω E X Y F hX)
    (rawRationalFunctor l Ω E X Y F hX) (fun _ ↦ rfl)
    (by intros; exact heq_of_eq rfl)

private theorem fullIntegralExact
    (F : C.{u, v} l Ω X (.integral E) ⥤ C.{u, v} l Ω Y (.integral E))
    [F.CommShift ℤ] [F.IsTriangulated]
    (hX : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X) :
    ∃ cs : (fullIntegralFunctor l Ω E X Y F hX).CommShift ℤ,
      (letI := cs; (fullIntegralFunctor l Ω E X Y F hX).IsTriangulated) := by
  let IX := (sfIntegralConstructible l E.carrier X).ι
  let JX := (finiteTorConstructibleIntegral l E.carrier X).ι
  let IY := (sfIntegralConstructible l E.carrier Y).ι
  let JY := (finiteTorConstructibleIntegral l E.carrier Y).ι
  let r := integralRepresentative l Ω E X hX
  let j := PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y
  let er : r ⋙ JX ≅ IX := Iso.refl _
  let ej : j ⋙ IY ≅ JY := Iso.refl _
  let : r.CommShift ℤ := Functor.CommShift.ofComp er ℤ
  let : j.CommShift ℤ := Functor.CommShift.ofComp ej ℤ
  have : NatTrans.CommShift er.hom ℤ := Functor.CommShift.ofComp_compatibility er ℤ
  have : NatTrans.CommShift ej.hom ℤ := Functor.CommShift.ofComp_compatibility ej ℤ
  have : r.IsTriangulated := (Functor.isTriangulated_iff_comp_right er).2 inferInstance
  have : j.IsTriangulated := (Functor.isTriangulated_iff_comp_right ej).2 inferInstance
  exact ⟨(inferInstance : (r ⋙ F ⋙ j).CommShift ℤ),
    (inferInstance : (r ⋙ F ⋙ j).IsTriangulated)⟩

set_option linter.unusedVariables false in
/-- The localized raw functors carry the transported adjunction and exact structures.
Source: Zheng, Construction 6.2, adjunction and exactness before normalization
(blueprint: lem-sf-integral-adjunction-raw-localization-core). -/
theorem exists_raw_localized_adjunction_core
    (A : Operation.{u, v} l Ω X Y (.integral E))
    [A.F.Additive] [A.G.Additive]
    [A.F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    [A.G.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    (hX : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X)
    (hY : sfIntegralConstructible l E.carrier Y = finiteTorConstructibleIntegral l E.carrier Y) :
    ∃ (R : RawLocalizedAdjunction l Ω E X Y A hX hY), True := by
  let F := fullIntegralFunctor l Ω E X Y A.F hX
  let G := fullIntegralFunctor l Ω E Y X A.G hY
  have : F.Additive := fullIntegralFunctorAdditive l Ω E X Y A.F hX
  have : F.Linear (Padic.coefficientExtensionIntegers l E.carrier) :=
    fullIntegralFunctorLinear l Ω E X Y A.F hX
  let Fq := rawRationalFunctor l Ω E X Y A.F hX
  let Gq := rawRationalFunctor l Ω E Y X A.G hY
  let : A.F.CommShift ℤ := A.leftShift
  have : A.F.IsTriangulated := A.leftExact
  obtain ⟨cs, ht⟩ := fullIntegralExact l Ω E A.F hX
  let : F.CommShift ℤ := cs
  have : F.IsTriangulated := ht
  have : Fq.Additive := ⟨by intros; exact map_add _ _ _⟩
  obtain ⟨P⟩ := sfRationalizedExact l E.carrier F Fq
    (fun _ ↦ rfl) (by intros; exact heq_of_eq rfl)
  let : Fq.CommShift ℤ := P.rationalShift
  have : Fq.IsTriangulated := P.rationalExact
  obtain ⟨adj, _, _⟩ := sfLocalizedAdjunction l E.carrier F G Fq Gq
    (fullIntegralAdjunction l Ω E A hX hY)
    (rawRationalFactor l Ω E A.F hX) (rawRationalFactor l Ω E A.G hY)
  let : Gq.CommShift ℤ := adj.rightAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  exact ⟨{
    adjunction := adj
    leftExact := P.rationalExact
    rightExact := adj.isTriangulated_rightAdjoint
    unitShift := inferInstance
    counitShift := inferInstance }, trivial⟩

/-- The localized adjunction admits the identity normalized coefficient comparison.
Source: Zheng, Construction 6.2, normalization after scalar localization
(blueprint: lem-sf-integral-adjunction-raw-localization-identity).
STATEMENT-DISPUTED: an arbitrary RawLocalizedAdjunction has no normalization against
A's counit or shifts. Rescaling its unit and counit by -1 preserves its axioms but
contradicts identity comparison components on a nonzero characteristic-zero category.
The comparison must concern the particular normalized construction, or assume that
normalization explicitly. -/
theorem exists_raw_localized_identity_comparison
    (A : Operation.{u, v} l Ω X Y (.integral E))
    [A.F.Additive] [A.G.Additive]
    [A.F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    [A.G.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    (hX : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X)
    (hY : sfIntegralConstructible l E.carrier Y = finiteTorConstructibleIntegral l E.carrier Y)
    (R : RawLocalizedAdjunction l Ω E X Y A hX hY) :
    ∃ (q : CounitFieldComparison.{u, v} l Ω A (R.operation l Ω E)
        (rationalization.{u, v} l Ω E X) (rationalization.{u, v} l Ω E Y)),
      (∀ K, HEq (q.q.hom.app K)
        (𝟙 ((rationalization.{u, v} l Ω E Y).obj (A.F.obj K)))) ∧
      (∀ M, HEq (q.b.hom.app M)
        (𝟙 ((rationalization.{u, v} l Ω E X).obj (A.G.obj M)))) ∧
      q.shiftX = integralRationalizationShift l Ω E X ∧
      q.shiftY = integralRationalizationShift l Ω E Y := by sorry

/-- A single integral linear adjunction localizes on its literal tensor Hom maps.
There is no compactification, compact-support realization, or change of coefficient field.
Source: Zheng, Construction 6.2, and scalar localization of adjunctions
(blueprint: lem-sf-integral-adjunction-raw-localization).
-/
theorem exists_integral_adjunction_raw_localization
    (A : Operation.{u, v} l Ω X Y (.integral E))
    [A.F.Additive] [A.G.Additive]
    [A.F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    [A.G.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    (hX : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X)
    (hY : sfIntegralConstructible l E.carrier Y = finiteTorConstructibleIntegral l E.carrier Y) :
    ∃ (R : RawLocalizedAdjunction l Ω E X Y A hX hY)
      (q : CounitFieldComparison.{u, v} l Ω A (R.operation l Ω E)
        (rationalization.{u, v} l Ω E X) (rationalization.{u, v} l Ω E Y)),
      (∀ K, HEq (q.q.hom.app K)
        (𝟙 ((rationalization.{u, v} l Ω E Y).obj (A.F.obj K)))) ∧
      (∀ M, HEq (q.b.hom.app M)
        (𝟙 ((rationalization.{u, v} l Ω E X).obj (A.G.obj M)))) ∧
      q.shiftX = integralRationalizationShift l Ω E X ∧
      q.shiftY = integralRationalizationShift l Ω E Y := by
  obtain ⟨R⟩ := exists_raw_localized_adjunction_core l Ω E A hX hY
  obtain ⟨q, hq, hb, hx, hy⟩ :=
    exists_raw_localized_identity_comparison l Ω E A hX hY R
  exact ⟨R, q, hq, hb, hx, hy⟩

end WeilConjectures.ConstructibleExceptionalCoefficients
