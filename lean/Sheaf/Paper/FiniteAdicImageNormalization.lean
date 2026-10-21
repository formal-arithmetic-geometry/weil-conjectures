/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.FiniteAdicSectionRealizationCore

/-! # Finite adic compactification and section comparison data

Source: Bhatt--Scholze 6.8.14--6.8.15; Milne 18.1, 18.3(b)
(blueprint: def-a1-finite-adic-image-normalization).

This module records one component of the canonical finite section diagrams.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

namespace AdicCompactificationSections

open scoped ChangeOfRings

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Integral image transport, retaining the precise Roos comparison before localization.
Source: BS 6.7.2, 6.8.15
(blueprint: def-a1-finite-adic-image-normalization). -/
def normalizedIntegralImageArrow (W : Geometry D)
    (K : sfIntegralConstructibleCategory l E W.scheme) (M : ImageModel D l hl E W K) :
    (integralDetailedTransport (Spec (.of D.k)) l E).obj
        (integralImage D l hl E W.scheme K).obj ⟶
      (pbcActualDerivedPush (W.scheme ↘ Spec (.of D.k)) (pbcIntegralDatum l E)).obj
        ((integralDetailedTransport W.scheme l E).obj K.obj) :=
  (integralDetailedTransport (Spec (.of D.k)) l E).map
      ((imageObjectIso D l hl E W K).hom ≫ M.roos.hom) ≫
    M.transport.derived.hom.app K.obj

/-- A component of the normalized ordinary-image comparison.
Source: BS 6.7.2, 6.8.15
(blueprint: def-a1-finite-adic-image-normalization). -/
def imageIntegralSource (R : ContinuousRational.Family.{u} l) (W : Geometry D)
    (A : FiniteAtCore D l hl E R W)
    (F : sfRationalConstructibleCategory l E W.scheme) :=
  A.point.integral.hom.app (integralImage D l hl E W.scheme F.obj)

/-- A component of the normalized ordinary-image comparison.
Source: BS 6.7.2, 6.8.15
(blueprint: def-a1-finite-adic-image-normalization). -/
def imageIntegralTransport (R : ContinuousRational.Family.{u} l) (W : Geometry D)
    (A : FiniteAtCore D l hl E R W)
    (F : sfRationalConstructibleCategory l E W.scheme) :=
  (pbcDerivedExtend
    ((R.realization E (realizationBase D l hl ⟨Spec (.of D.k)⟩)).integralIso.hom ≫
      (R.realization E (realizationBase D l hl ⟨Spec (.of D.k)⟩)).inclusion)).map
    (normalizedIntegralImageArrow D l hl E W F.obj (A.image_model F))

/-- A component of the normalized ordinary-image comparison.
Source: BS 6.7.2, 6.8.15
(blueprint: def-a1-finite-adic-image-normalization). -/
def imageLocalizationProjection (R : ContinuousRational.Family.{u} l) (W : Geometry D)
    (A : FiniteAtCore D l hl E R W)
    (F : sfRationalConstructibleCategory l E W.scheme) :=
  ContinuousRational.DirectImage.projection l E
    (X := realizationBase D l hl W)
    (Y := realizationBase D l hl ⟨Spec (.of D.k)⟩) (W.scheme ↘ Spec (.of D.k))
    (R.realization E (realizationBase D l hl W))
    (R.realization E (realizationBase D l hl ⟨Spec (.of D.k)⟩))
    (R.along E (X := realizationBase D l hl W)
      (Y := realizationBase D l hl ⟨Spec (.of D.k)⟩) (W.scheme ↘ Spec (.of D.k)))
    (A.direct_image (X := realizationBase D l hl W)
      (Y := realizationBase D l hl ⟨Spec (.of D.k)⟩) (W.scheme ↘ Spec (.of D.k)))
    ((integralDetailedTransport W.scheme l E).obj F.obj.obj)

/-- A component of the normalized ordinary-image comparison.
Source: BS 6.7.2, 6.8.15
(blueprint: def-a1-finite-adic-image-normalization). -/
def imageRealizationTarget (R : ContinuousRational.Family.{u} l) (W : Geometry D)
    (A : FiniteAtCore D l hl E R W)
    (F : sfRationalConstructibleCategory l E W.scheme) :=
  (ContinuousRational.DirectImage.derivedPush (W.scheme ↘ Spec (.of D.k))
    (R.along E (X := realizationBase D l hl W)
      (Y := realizationBase D l hl ⟨Spec (.of D.k)⟩) (W.scheme ↘ Spec (.of D.k))).coefficient).map
    (A.integral.inv.app F.obj)

/-- The ordinary image is the composite of the four specified arrows. Equality in
`Arrow` pins both endpoints and each map, while the final equation composes only
abstract intermediate objects. This equivalent factorization avoids repeated kernel
conversion through the large coefficient-transport expressions.
Source: BS 6.7.2, 6.8.15
(blueprint: def-a1-finite-adic-image-normalization). -/
def ImageNormalization (R : ContinuousRational.Family.{u} l) (W : Geometry D)
    (A : FiniteAtCore D l hl E R W)
    (F : sfRationalConstructibleCategory l E W.scheme) : Prop :=
  ∃ (P Q S : DerivedCategory (pbcModules (Spec (.of D.k))
      (rationalCoefficientSheaf l (Spec (.of D.k)) E)))
    (f : A.point.J.obj (rationalImage D l hl E W.scheme F) ⟶ P)
    (g : P ⟶ Q) (h : Q ⟶ S)
    (i : S ⟶ (ContinuousRational.DirectImage.derivedPush (W.scheme ↘ Spec (.of D.k))
      (R.along E (X := realizationBase D l hl W)
        (Y := realizationBase D l hl ⟨Spec (.of D.k)⟩)
          (W.scheme ↘ Spec (.of D.k))).coefficient).obj (A.J.obj F)),
    Arrow.mk f = Arrow.mk (imageIntegralSource D l hl E R W A F) ∧
    Arrow.mk g = Arrow.mk (imageIntegralTransport D l hl E R W A F) ∧
    Arrow.mk h = Arrow.mk (imageLocalizationProjection D l hl E R W A F) ∧
    Arrow.mk i = Arrow.mk (imageRealizationTarget D l hl E R W A F) ∧
    (A.image F).hom = f ≫ g ≫ h ≫ i

end AdicCompactificationSections
end WeilConjectures
