/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.PointFibreDerivedTensorScalar

/-! # Canonical point tensor comparison interfaces

Source: Stacks 07A4 and the recorded coefficient constructions.
(blueprint: def-sf-point-fibre-tensor-rational-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v c e d hc he hd w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures

/-- The canonical coefficient/carrier lift carries tensor through localization.
Its comparison is fixed by up(x tensor y) mapping to up(x) tensor up(y).
Source: recorded point-coefficient size lift, blueprint order 1509
(blueprint: def-sf-point-fibre-tensor-rational-compatibility). -/
structure PointFibreLiftTensorData (E : Type u) [Field E] where
  /-- Strong monoidality of the specified fully faithful derived lift. -/
  strong : (pointFibreModuleLift E).mapDerivedCategory.Monoidal
  /-- The pure-tensor representative normalization. -/
  model : ∀ P Q : CochainComplex (ModuleCat.{u} E) ℤ,
    ∃ e : ((pointFibreModuleLift E).mapHomologicalComplex (ComplexShape.up ℤ)).obj (P ⊗ Q) ≅
      ((pointFibreModuleLift E).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⊗
        ((pointFibreModuleLift E).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q,
      (∀ (p q k : ℤ) (h : p + q = k) (x : P.X p) (y : Q.X q),
        (e.hom.f k) (ULift.up ((HomologicalComplex.ιTensorObj P Q p q k h) (x ⊗ₜ[E] y))) =
          (HomologicalComplex.ιTensorObj
            (((pointFibreModuleLift E).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            (((pointFibreModuleLift E).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
            p q k h) (ULift.up x ⊗ₜ[ULift.{u + 1, u} E] ULift.up y)) ∧
      (pointFibreModuleLift E).mapDerivedCategory.map
          (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        (pointFibreModuleLift E).mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
        DerivedCategory.Q.map e.hom =
      (@Functor.OplaxMonoidal.δ _ _ _ _ _ _ _ strong.toOplaxMonoidal
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)) ≫
        (MonoidalCategory.tensor _).map
          (Prod.mkHom ((pointFibreModuleLift E).mapDerivedCategoryFactors.hom.app P)
            ((pointFibreModuleLift E).mapDerivedCategoryFactors.hom.app Q)) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          (((pointFibreModuleLift E).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (((pointFibreModuleLift E).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)

/-- Rational fibre normalization before the recorded coefficient universe is lowered.
It is made from the specified localization object identity and size-equivalence counit.
Source: blueprint order 1509 (blueprint: def-sf-point-fibre-tensor-rational-compatibility). -/
def pointRationalLargeNormalization
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (K : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (pointFibreModuleLift E).mapDerivedCategory.obj ((pointRationalFibre D l hl E).obj K).obj ≅
      (pointFibreRationalAmbient D l E).obj K.obj.obj :=
  letI := pointFibreSizeLift_equivalence E
  (pointFibreModuleLift E).mapDerivedCategory.mapIso
      ((DerivedCategory.pointFiniteDimensional E).ι.mapIso
        (pointRationalFibreObjIso D l hl E K)) ≪≫
    (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)).ι.mapIso
      ((pointFibreSizeLift E).asEquivalence.counitIso.app
        (pointFibreRationalLarge D l hl E K.obj))

/-- The specified integral tensor object underlying rational tensor, with no chosen
isomorphism: this is the object equality in the recorded rational tensor definition.
Source: blueprint rationalization clause
(blueprint: def-sf-point-fibre-tensor-rational-compatibility). -/
def pointRationalTensorObjectIso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (M N : sfRationalConstructibleCategory l E (Spec (.of D.k))) :=
  letI : ∀ w : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField w) :=
    Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  eqToIso ((rationalDerivedTensor_existsUnique l E (Spec (.of D.k))).exists.choose_spec.1 (M, N))

/-- The rational comparison is precisely the integral comparison after rationalization,
conjugated by the recorded size normalization. Faithfulness of the lift pins the
small comparison, rather than merely asserting that some small isomorphism exists.
Source: node proof step 6 (blueprint: def-sf-point-fibre-tensor-rational-compatibility). -/
def PointRationalTensorCanonical
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (I : PointIntegralTensorData D l hl E)
    (R : PointRationalTensorData D l hl E I) (U : PointFibreLiftTensorData E)
    (B : PointModuleScalarTensorData (pointIntegralToField l E)
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)).mapDerivedCategory) : Prop :=
  ∀ M N : sfRationalConstructibleCategory l E (Spec (.of D.k)),
    ∃ (hM : finiteTorConstructibleIntegral l E (Spec (.of D.k)) M.obj.obj)
      (hN : finiteTorConstructibleIntegral l E (Spec (.of D.k)) N.obj.obj),
      (pointFibreModuleLift E).mapDerivedCategory.map (R.tensorIso M N).hom ≫
        (@Functor.OplaxMonoidal.δ _ _ _ _ _ _ _ U.strong.toOplaxMonoidal
          ((pointRationalFibre D l hl E).obj M).obj
          ((pointRationalFibre D l hl E).obj N).obj) ≫
        (MonoidalCategory.tensor _).map
          (Prod.mkHom (pointRationalLargeNormalization D l hl E M).hom
            (pointRationalLargeNormalization D l hl E N).hom) =
      (pointFibreModuleLift E).mapDerivedCategory.map
          ((pointRationalFibre D l hl E ⋙ (DerivedCategory.pointFiniteDimensional E).ι).map
            (pointRationalTensorObjectIso D l hl E M N).hom) ≫
        (pointRationalLargeNormalization D l hl E _).hom ≫
        (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (pointIntegralToField l E)).mapDerivedCategory.map
          (I.tensorIso ⟨M.obj.obj, hM⟩ ⟨N.obj.obj, hN⟩).hom ≫
        (@Functor.OplaxMonoidal.δ _ _ _ _ _ _ _ B.strong.toOplaxMonoidal
          ((pointFibreIntegralAmbient D l E).obj M.obj.obj)
          ((pointFibreIntegralAmbient D l E).obj N.obj.obj))

/-- The rational scalar comparison in the actual ambient module categories.
Its defining dependency uses `pointFibreTensorLiftIso` and the normalized sections
comparison, so both coefficient and carrier transports are retained.
Source: blueprint order 1509 (blueprint: def-sf-point-fibre-tensor-rational-compatibility). -/
def pointRationalTensorScalarFibreIso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) :=
  Functor.isoWhiskerRight (pointRationalFibreScalarIso D l hl E L ι)
    (DerivedCategory.pointFiniteDimensional L).ι

/-- The actual field-extension square through `rationalTensorScalarComparison` and
`pointRationalFibreScalarIso`, including its specified tensor/lift transport.
Source: node proof steps 6 and 9 (blueprint: def-sf-point-fibre-tensor-rational-compatibility). -/
def PointRationalTensorScalarSquare
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (I₁ : PointIntegralTensorData D l hl E) (I₂ : PointIntegralTensorData D l hl L)
    (R₁ : PointRationalTensorData D l hl E I₁) (R₂ : PointRationalTensorData D l hl L I₂)
    (B : PointModuleScalarTensorData ι.toRingHom
      (DerivedCategory.fieldDerivedScalarExtension ι.toRingHom)) : Prop :=
  letI : ∀ w : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField w) :=
    Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  ∀ M N : sfRationalConstructibleCategory l E (Spec (.of D.k)),
    HEq
      ((pointRationalFibre D l hl L ⋙ (DerivedCategory.pointFiniteDimensional L).ι).map
        ((rationalTensorScalarComparison l E L ι (Spec (.of D.k))).hom.app (M, N)) ≫
        (R₂.tensorIso
          ((sfRationalScalarExtension l E (Spec (.of D.k)) 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)
          ((sfRationalScalarExtension l E (Spec (.of D.k)) 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj N)).hom ≫
        (MonoidalCategory.tensor _).map
          (Prod.mkHom ((pointRationalTensorScalarFibreIso D l hl E L ι).hom.app M)
            ((pointRationalTensorScalarFibreIso D l hl E L ι).hom.app N)))
      ((pointRationalTensorScalarFibreIso D l hl E L ι).hom.app
          ((rationalPointFibreTensorBifunctor D l hl E).obj (M, N)) ≫
        (DerivedCategory.fieldDerivedScalarExtension ι.toRingHom).map (R₁.tensorIso M N).hom ≫
        (@Functor.OplaxMonoidal.δ _ _ _ _ _ _ _ B.strong.toOplaxMonoidal
          ((pointRationalFibre D l hl E).obj M).obj ((pointRationalFibre D l hl E).obj N).obj))


/-- The rational coefficient unit is the localization of the normalized integral unit.
Both coefficient and carrier transports are the same as in the tensor square.
Source: rationalization clause (blueprint: def-sf-point-fibre-tensor-rational-compatibility). -/
def PointRationalTensorUnitCanonical
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (I : PointIntegralTensorData D l hl E)
    (R : PointRationalTensorData D l hl E I) (U : PointFibreLiftTensorData E)
    (B : PointModuleScalarTensorData (pointIntegralToField l E)
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)).mapDerivedCategory) : Prop :=
  (pointFibreModuleLift E).mapDerivedCategory.map R.unitIso.hom ≫
      (@Functor.Monoidal.εIso _ _ _ _ _ _ _ U.strong).inv =
    (pointRationalLargeNormalization D l hl E (pointRationalTensorUnit D l hl E I)).hom ≫
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (pointIntegralToField l E)).mapDerivedCategory.map
        ((pointFibreIntegralAmbient D l E).map (eqToHom I.unit_eq)) ≫
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)).mapDerivedCategory.map I.unitIso.hom ≫
      (@Functor.Monoidal.εIso _ _ _ _ _ _ _ B.strong).inv

end WeilConjectures
