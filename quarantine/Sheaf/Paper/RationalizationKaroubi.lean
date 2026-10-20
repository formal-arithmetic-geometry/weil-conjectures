/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.IntegralScalarExtensionConstructible
public import Sheaf.CategoryTheory.ScalarLocalization
public import Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Sheaf.CategoryTheory.ScalarLocalizationTriangulated

public import Mathlib.CategoryTheory.Triangulated.Triangulated
/-! # Rationalized constructible integral categories and coefficient extension

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1460 (blueprint: def-weil-rationalization-karoubi).

This is raw Hom scalar localization, with the same integral objects. The canonical
localization isomorphism identifies its Hom modules with Hom tensor E. No retracts
are adjoined. The coefficient functor is fixed uniquely on objects and pure tensors.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe d u

open CategoryTheory TensorProduct

namespace WeilConjectures

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- The raw rationalized category, without idempotent completion.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable abbrev rationalConstructibleCategory :=
  ScalarLocalization (Padic.coefficientExtensionIntegers l E)
    (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y)
    (Padic.coefficientExtensionUniformizer l E)

set_option linter.defProp false in
/-- The recorded raw scalar-localization theorem supplies precisely the induced shift
and image triangles, with exact localization and no new objects.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable def rationalTriangulationDatum :=
  letI := integralConstructibleShift_linear l E Y D hl (1 : ℤ)
  ScalarLocalization.exists_triangulated_scalarLocalization
    (Padic.coefficientExtensionIntegers l E)
    (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y)
    (Padic.coefficientExtensionUniformizer l E)

/-- The zero object in raw rationalization.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance rationalConstructibleZero :
    CategoryTheory.Limits.HasZeroObject (rationalConstructibleCategory D l hl E Y) :=
  (rationalTriangulationDatum D l hl E Y).choose

/-- The induced shift, with the tensor-Hom shift specified by the triangulation datum.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance rationalConstructibleShift :
    HasShift (rationalConstructibleCategory D l hl E Y) ℤ :=
  (rationalTriangulationDatum D l hl E Y).choose_spec.choose

/-- Additivity of every induced rational shift.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance rationalConstructibleShiftAdditive (n : ℤ) :
    (shiftFunctor (rationalConstructibleCategory D l hl E Y) n).Additive :=
  (rationalTriangulationDatum D l hl E Y).choose_spec.choose_spec.2.choose n

/-- The canonical integral-to-rational functor is the identity on objects and tensors
morphisms with one. Source: blueprint order 1460
(blueprint: def-weil-rationalization-karoubi). -/
noncomputable def rationalConstructibleLocalization :
    boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y ⥤
      rationalConstructibleCategory D l hl E Y :=
  ScalarLocalization.localization (Padic.coefficientExtensionIntegers l E)
    (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y)
    (Padic.coefficientExtensionUniformizer l E)

/-- The canonical shift comparison for localization.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance rationalLocalizationCommShift :
    (rationalConstructibleLocalization D l hl E Y).CommShift ℤ :=
  (rationalTriangulationDatum D l hl E Y).choose_spec.choose_spec.2.choose_spec.choose

/-- The image-triangle pretriangulation of the raw localized category.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance rationalConstructiblePretriangulated :
    Pretriangulated (rationalConstructibleCategory D l hl E Y) :=
  (rationalTriangulationDatum D l hl E Y).choose_spec.choose_spec.2.choose_spec.choose_spec.2.choose

/-- Triangulation for exactly the image triangles.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance rationalConstructibleTriangulated :
    IsTriangulated (rationalConstructibleCategory D l hl E Y) :=
  (rationalTriangulationDatum D l hl E Y).choose_spec.choose_spec.2.choose_spec.choose_spec.2
    |>.choose_spec.1

/-- Exactness of the integral-to-rational functor for the specified image triangles.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance rationalLocalizationTriangulated :
    (rationalConstructibleLocalization D l hl E Y).IsTriangulated :=
  (rationalTriangulationDatum D l hl E Y).choose_spec.choose_spec.2.choose_spec.choose_spec.2
    |>.choose_spec.2.1

/-- The canonical localized coefficient field identification, fixed on fractions.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable def rationalCoefficientEquiv :
    Localization.Away (Padic.coefficientExtensionUniformizer l E) ≃ₐ[
      Padic.coefficientExtensionIntegers l E] E :=
  (Padic.coefficientExtension_localization_uniformizer.{u, u} l E).2.choose

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- Rational scalar extension is uniquely specified by integral extension and the
field inclusion on scalar factors. This is the well-definedness needed by its definition.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi).
Proof: integral scalar extension is additive and linear for the integer inclusion.
Transport localized scalars through rationalCoefficientEquiv, the inclusion ι and
its target inverse. The tensor universal property therefore gives the stated map
on each Hom group. The integral functor laws and the multiplication law for scalar
factors show that it preserves identities and composition, first on pure tensors
and then on finite sums. Pure tensors generate every Hom module, proving uniqueness.
The object map is the actual restricted completed extension. -/
theorem rationalScalarExtension_existsUnique :
    ∃! F : rationalConstructibleCategory D l hl E Y ⥤
        rationalConstructibleCategory D l hl L Y,
      F.Additive ∧
      (∀ K : rationalConstructibleCategory D l hl E Y,
        F.obj K = ⟨(constructibleIntegralScalarExtension D l hl E L ι Y).obj K.obj⟩) ∧
      (∀ (K K' : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y)
        (f : K ⟶ K') (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
        HEq (F.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
          (rationalConstructibleLocalization D l hl E Y).obj K ⟶
            (rationalConstructibleLocalization D l hl E Y).obj K'))
          ((rationalCoefficientEquiv l L).symm (ι (rationalCoefficientEquiv l E a))
            ⊗ₜ[Padic.coefficientExtensionIntegers l L]
              (constructibleIntegralScalarExtension D l hl E L ι Y).map f :
                (rationalConstructibleLocalization D l hl L Y).obj
                  ((constructibleIntegralScalarExtension D l hl E L ι Y).obj K) ⟶
                (rationalConstructibleLocalization D l hl L Y).obj
                  ((constructibleIntegralScalarExtension D l hl E L ι Y).obj K'))) := by
  sorry

/-- The specified scalar-extension functor on the raw rationalized categories.
Its defining theorem uniquely determines the whole functor, rather than merely
asserting existence of an unspecified comparison.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable def rationalScalarExtension :
    rationalConstructibleCategory D l hl E Y ⥤ rationalConstructibleCategory D l hl L Y :=
  (rationalScalarExtension_existsUnique D l hl E Y L ι).exists.choose

/-- Rational coefficient extension is additive, as specified in its defining property.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance rationalScalarExtension_additive :
    (rationalScalarExtension D l hl E Y L ι).Additive :=
  (rationalScalarExtension_existsUnique D l hl E Y L ι).exists.choose_spec.1

end WeilConjectures


namespace WeilConjectures

open CategoryTheory TensorProduct

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- The displayed Hom tensor E formula in canonical additive coordinates.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi).
Proof: commute the two tensor factors, then apply the canonical uniformizer-localization
algebra equivalence to the scalar factor. The tensor universal property gives the map
and its inverse. Pure tensors generate, proving the stated uniqueness. -/
theorem rationalConstructibleHomCoordinates_existsUnique
    (K M : rationalConstructibleCategory D l hl E Y) :
    ∃! e : (K ⟶ M) ≃+
        ((K.obj ⟶ M.obj) ⊗[Padic.coefficientExtensionIntegers l E] E),
      ∀ (a : Localization.Away (Padic.coefficientExtensionUniformizer l E))
        (f : K.obj ⟶ M.obj), e (a ⊗ₜ f) = f ⊗ₜ rationalCoefficientEquiv l E a := by
  sorry

/-- The canonical coordinates identifying the actual Hom group with Hom tensor E.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable def rationalConstructibleHomCoordinates
    (K M : rationalConstructibleCategory D l hl E Y) :=
  (rationalConstructibleHomCoordinates_existsUnique D l hl E Y K M).exists.choose

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- The induced map on localized scalar rings, through their canonical field coordinates.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable def rationalCoefficientMap :
    Localization.Away (Padic.coefficientExtensionUniformizer l E) →+*
      Localization.Away (Padic.coefficientExtensionUniformizer l L) :=
  (rationalCoefficientEquiv l L).symm.toRingHom.comp
    (ι.toRingHom.comp (rationalCoefficientEquiv l E).toRingHom)

/-- The unique additive map induced by scalar extension on the tensor Hom module.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi).
Proof: ordinary sheaf tensor is additive, and its balanced relations respect the
constant-section action through the completed coefficient inclusion. The fraction-field
coordinate maps respect the
integer inclusion. Thus the stated formula is additive and balanced over O_E. The tensor
universal property gives the map; pure tensors generate, proving uniqueness. -/
theorem rationalScalarHom_existsUnique
    (K M : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :
    ∃! f : (Localization.Away (Padic.coefficientExtensionUniformizer l E) ⊗[
        Padic.coefficientExtensionIntegers l E] (K ⟶ M)) →+
      (Localization.Away (Padic.coefficientExtensionUniformizer l L) ⊗[
        Padic.coefficientExtensionIntegers l L]
        ((integralConstructibleScalarExtension D l hl E L ι Y).obj K ⟶
          (integralConstructibleScalarExtension D l hl E L ι Y).obj M)),
      ∀ (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)) (g : K ⟶ M),
        f (a ⊗ₜ g) = rationalCoefficientMap l E L ι a ⊗ₜ
          (integralConstructibleScalarExtension D l hl E L ι Y).map g := by
  sorry

/-- The actual tensor Hom map, selected from its uniquely determining formula.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable def rationalScalarHom
    (K M : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :=
  (rationalScalarHom_existsUnique D l hl E Y L ι K M).exists.choose

/-- The tensor Hom maps respect identities and composition.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi).
Proof: on pure tensors, the formulas for the uniquely specified Hom map and for
ScalarLocalization.composition reduce this to functoriality of integral scalar extension
and multiplicativity of rationalCoefficientMap. Bilinearity extends the identities to
all tensor morphisms. -/
theorem rationalScalarHom_laws :
    (∀ K : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y,
      rationalScalarHom D l hl E Y L ι K K (1 ⊗ₜ 𝟙 K) =
        1 ⊗ₜ 𝟙 ((integralConstructibleScalarExtension D l hl E L ι Y).obj K)) ∧
    (∀ (K M N : rationalConstructibleCategory D l hl E Y) (f : K ⟶ M) (g : M ⟶ N),
      rationalScalarHom D l hl E Y L ι K.obj N.obj (f ≫ g) =
        ScalarLocalization.composition (Padic.coefficientExtensionIntegers l L)
          (boundedConstructibleDerivedCompleteIntegralCategory D l hl L Y)
          (Padic.coefficientExtensionUniformizer l L) _ _ _
          (rationalScalarHom D l hl E Y L ι M.obj N.obj g)
          (rationalScalarHom D l hl E Y L ι K.obj M.obj f)) := by
  sorry

/-- Scalar extension on raw rational stages: integral scalar extension on objects,
and the specified tensor map on morphisms.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable def rationalOrdinaryScalarExtension :
    rationalConstructibleCategory D l hl E Y ⥤ rationalConstructibleCategory D l hl L Y where
  obj K := ⟨(integralConstructibleScalarExtension D l hl E L ι Y).obj K.obj⟩
  map {K M} f := rationalScalarHom D l hl E Y L ι K.obj M.obj f
  map_id K := (rationalScalarHom_laws D l hl E Y L ι).1 K.obj
  map_comp {K M N} f g := (rationalScalarHom_laws D l hl E Y L ι).2 K M N f g

/-- The ordinary-model functor identifies with the published completed scalar extension
by tensoring the normalized quotient completion comparison with one.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi).
Proof: use integralConstructibleScalarComparison on every integral object. The published
rationalScalarExtension has the specified integral object map and balanced tensor map.
Integral comparison naturality therefore gives naturality on pure rational tensors and
then on sums. Rationalizing its inverse gives the inverse; the displayed components
uniquely fix the natural isomorphism, including all newly localized morphisms. -/
theorem rationalOrdinaryComparison_existsUnique :
    ∃! c : rationalOrdinaryScalarExtension D l hl E Y L ι ≅
        rationalScalarExtension D l hl E Y L ι,
      ∀ K : rationalConstructibleCategory D l hl E Y,
        HEq (c.hom.app K)
          ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l L)) ⊗ₜ[
            Padic.coefficientExtensionIntegers l L]
              (integralConstructibleScalarComparison D l hl E L ι Y).hom.app K.obj) := by
  sorry

/-- The normalized comparison to the existing completed rational scalar functor.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable def rationalOrdinaryComparison :=
  (rationalOrdinaryComparison_existsUnique D l hl E Y L ι).exists.choose

end WeilConjectures
