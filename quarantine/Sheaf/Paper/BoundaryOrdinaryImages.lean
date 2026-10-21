/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Paper.IntrinsicQbarCategory
public import Sheaf.Paper.QbarCurveOrdinaryImage
public import Sheaf.Paper.WeilIndSheafCategory
public import Sheaf.Paper.CommonStageLisse
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Ordinary boundary images and their induced Frobenius pairs

Source: blueprint main-20261015, rem-dl-a1-conventions, final paragraph,
and lem-dl-a1-boundary-hom-vanishing, ordinary closed-image and Weil-pair conventions
(blueprint: def-dl-a1-boundary-ordinary-images).

The closed image is the right adjoint of the recorded geometric inverse image on
constructible hearts. Frobenius is its adjunction mate, with the specified counit.
The open image uses the already recorded ordinary curve adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Closed ordinary direct image exists on the actual constructible heart.
Source: blueprint boundary-image convention; Bhatt--Scholze §6.7--6.8
(blueprint: def-dl-a1-boundary-ordinary-images).
Proof: ordinary closed direct image is sectionwise evaluation on the base change
of a test object. It is right adjoint to exact inverse image, is exact, and extends
a finite constructible stratification by the zero sheaf on the complement. Thus
it preserves the rational constructible heart. Its finite scalar comparisons are
sectionwise identities, so the adjunction descends to the common-stage heart.
The right-adjoint universal property fixes the functor up to compatible isomorphism. -/
theorem boundaryClosedRestriction_isLeftAdjoint
    {Z₀ C₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]
    (i₀ : Z₀ ⟶ C₀) [IsClosedImmersion i₀.left] :
    (zlHeartPull D l hl Ω i₀).IsLeftAdjoint := by
  sorry

/-- Ordinary closed image, determined by its sheaf adjunction, in the common-stage heart.
Source: blueprint boundary-image convention
(blueprint: def-dl-a1-boundary-ordinary-images). -/
def boundaryClosedPushforward
    {Z₀ C₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]
    (i₀ : Z₀ ⟶ C₀) [IsClosedImmersion i₀.left] :=
  @Functor.rightAdjoint _ _ _ _ (zlHeartPull D l hl Ω i₀)
    (boundaryClosedRestriction_isLeftAdjoint D l hl Ω i₀)

/-- The ordinary closed adjunction, including the unit and counit normalization.
Source: blueprint boundary-image convention
(blueprint: def-dl-a1-boundary-ordinary-images). -/
def boundaryClosedAdjunction
    {Z₀ C₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]
    (i₀ : Z₀ ⟶ C₀) [IsClosedImmersion i₀.left] :
    zlHeartPull D l hl Ω i₀ ⊣ boundaryClosedPushforward D l hl Ω i₀ :=
  @Adjunction.ofIsLeftAdjoint _ _ _ _ (zlHeartPull D l hl Ω i₀)
    (boundaryClosedRestriction_isLeftAdjoint D l hl Ω i₀)

variable {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (f₀ : X₀ ⟶ Y₀)
  (R : sfCommonStageHeart l (D.geometricFiber X₀).left Ω ⥤
    sfCommonStageHeart l (D.geometricFiber Y₀).left Ω)
  (a : zlHeartPull D l hl Ω f₀ ⊣ R)
  (K : sfCommonStageWeilSheaf D l hl X₀ Ω)

/-- The induced Frobenius arrow is the adjoint of inverse-image comparison,
Frobenius of the ordinary counit, and the given Frobenius arrow, in that order.
Source: blueprint induced Weil structures
(blueprint: def-dl-a1-boundary-ordinary-images). -/
def boundaryImageFrobeniusMap :
    (zlHeartFrobenius D l hl Ω Y₀).obj (R.obj ⟨K.obj.carrier, K.property⟩) ⟶
      R.obj ⟨K.obj.carrier, K.property⟩ :=
  (a.homEquiv _ _)
    ((zlHeartSquare D l hl Ω f₀).inv.app (R.obj ⟨K.obj.carrier, K.property⟩) ≫
      (zlHeartFrobenius D l hl Ω X₀).map (a.counit.app ⟨K.obj.carrier, K.property⟩) ≫
      ObjectProperty.homMk K.obj.str.hom)

/-- The normalized adjunction mate is invertible.
Source: blueprint induced Weil structures
(blueprint: def-dl-a1-boundary-ordinary-images).
Proof: geometric Frobenius is an automorphism. Its inverse square supplies the
inverse mate. The two pasted squares are identity squares, by the inverse-image
composition normalization. Taking adjunction mates preserves pasting and identities;
the triangle identities therefore make the two composites identities. Composing
with the given Weil isomorphism preserves invertibility. -/
theorem boundaryImageFrobeniusMap_isIso :
    IsIso (boundaryImageFrobeniusMap D l hl Ω f₀ R a K) := by
  sorry

/-- The actual induced fixed pair on an ordinary direct image. Its carrier is
literally the right-adjoint image, and its structure is the prescribed mate.
Source: blueprint induced Weil structures
(blueprint: def-dl-a1-boundary-ordinary-images). -/
def boundaryOrdinaryWeilImage : sfCommonStageWeilComplex D l hl Y₀ Ω :=
  letI := boundaryImageFrobeniusMap_isIso D l hl Ω f₀ R a K
  IsoAlgebra.mk (R.obj ⟨K.obj.carrier, K.property⟩).obj
    ((sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Ω).ι.mapIso
      (asIso (boundaryImageFrobeniusMap D l hl Ω f₀ R a K)))

/-- Shift a fixed pair using the cohomological pullback/shift comparison.
The carrier is K[1], and the structure is Φ(K[1]) ≅ Φ(K)[1] ≅ K[1].
Source: blueprint cohomological shift and Weil-pair conventions
(blueprint: def-dl-a1-boundary-ordinary-images). -/
def boundaryWeilShift (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (s : (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).CommShift ℤ)
    (K : sfCommonStageWeilComplex D l hl Y₀ Ω) :
    sfCommonStageWeilComplex D l hl Y₀ Ω :=
  IsoAlgebra.mk (K.carrier⟦(1 : ℤ)⟧)
    ((Functor.commShiftIso (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω)
        (self := s) (1 : ℤ)).app K.carrier ≪≫
      (shiftFunctor _ (1 : ℤ)).mapIso K.str)

end WeilConjectures
