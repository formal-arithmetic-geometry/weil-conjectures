/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.FiniteAdicProperSectionData

/-! # Finite adic compactification and section comparison data

Source: Bhatt--Scholze 6.8.14--6.8.15; Milne 18.1, 18.3(b)
(blueprint: def-a1-finite-adic-compactification-section-data).

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

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]

/-- Finite scalar extension on hearts and sections. The underlying functor is the
recorded completed scalar extension. All section maps are the actual tensor-unit maps.
Source: BS 6.8.2(1), 6.8.14; Milne 18.3(b)
(blueprint: def-a1-finite-adic-compactification-section-data). -/
structure FiniteScalar (ι : E →ₐ[ℚ_[l]] L) (R : ContinuousRational.Family.{u} l)
    {W : Geometry D} (AE : FiniteAt D l hl E R W) (AL : FiniteAt D l hl L R W) where
  heart : sfRationalHeart l E W.scheme ⥤ sfRationalHeart l L W.scheme
  underlying : heart ⋙ (sfRationalHeartProperty l L W.scheme).ι ≅
    (sfRationalHeartProperty l E W.scheme).ι ⋙ sfRationalScalarExtension l E W.scheme
      0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  sheaf : AE.sheaf ⋙ pbcExtend
      (R.fieldChange E L ι (realizationBase D l hl W)).coefficient ≅ heart ⋙ AL.sheaf
  unit : heart.obj AE.unit ≅ AL.unit
  unit_one : ∀ V : W.scheme.ProEtᵒᵖ,
    (AL.sheaf.map unit.hom).val.app V
      ((sheaf.hom.app AE.unit).val.app V
        (pbcTensorSection (X := W.scheme)
          (R.fieldChange E L ι (realizationBase D l hl W)).coefficient
          (AE.sheaf.obj AE.unit) V 1 (unitSection D l hl E AE V))) =
      unitSection D l hl L AL V
  ordinary : AE.ordinary ⋙ ModuleCat.extendScalars ι.toRingHom ≅ heart ⋙ AL.ordinary
  hom : ∀ (F : sfRationalHeart l E W.scheme) (x : AE.ordinary.obj F),
    AL.ordinary_hom (heart.obj F)
        (ordinary.hom.app F (scalarUnit ι.toRingHom x)) =
      unit.inv ≫ heart.map (AE.ordinary_hom F x)
  sections : ∀ (F : sfRationalHeart l E W.scheme) (x : AE.ordinary.obj F),
    AL.ordinary_sections (heart.obj F)
        (ordinary.hom.app F (scalarUnit ι.toRingHom x)) =
      (sheaf.hom.app F).val.app
        (Opposite.op (ProEt.mk (S := W.scheme) (X := W.scheme) (𝟙 W.scheme)))
        (pbcTensorSection (X := W.scheme)
          (R.fieldChange E L ι (realizationBase D l hl W)).coefficient
          (AE.sheaf.obj F) (Opposite.op (ProEt.mk (S := W.scheme) (X := W.scheme) (𝟙 W.scheme))) 1
          (AE.ordinary_sections F x))

/-- Scalar extension commutes with open extension and restriction, with the
specified adjunction unit. These are comparisons of functors, hence include arrows.
Source: BS 6.8.14--6.8.15; Stacks 0GL1
(blueprint: def-a1-finite-adic-compactification-section-data). -/
structure FiniteScalarOpen (ι : E →ₐ[ℚ_[l]] L) {R : ContinuousRational.Family.{u} l}
    {U T : Geometry D} {AEU : FiniteAt D l hl E R U} {AET : FiniteAt D l hl E R T}
    {ALU : FiniteAt D l hl L R U} {ALT : FiniteAt D l hl L R T}
    {j : U.scheme ⟶ T.scheme} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))]
    (OE : FiniteOpen D l hl E R AEU AET j) (OL : FiniteOpen D l hl L R ALU ALT j)
    (SU : FiniteScalar D l hl E L ι R AEU ALU)
    (ST : FiniteScalar D l hl E L ι R AET ALT) where
  extension : OE.shriek ⋙ ST.heart ≅ SU.heart ⋙ OL.shriek
  restriction : OE.restriction ⋙ SU.heart ≅ ST.heart ⋙ OL.restriction
  open_unit : ∀ F : sfRationalHeart l E U.scheme,
    SU.heart.map (OE.adjunction.unit.app F) ≫
        restriction.hom.app (OE.shriek.obj F) ≫
        OL.restriction.map (extension.hom.app F) = OL.adjunction.unit.app (SU.heart.obj F)
  coefficient_unit : SU.heart.map OE.unit.hom ≫ SU.unit.hom =
    restriction.hom.app AET.unit ≫ OL.restriction.map ST.unit.hom ≫ OL.unit.hom
  ordinary_restriction : ∀ (F : sfRationalHeart l E T.scheme) (x : AET.ordinary.obj F),
    SU.ordinary.hom.app (OE.restriction.obj F)
        (scalarUnit ι.toRingHom (OE.ordinary_restriction.app F x)) =
      ALU.ordinary.map (restriction.inv.app F)
        (OL.ordinary_restriction.app (ST.heart.obj F)
          (ST.ordinary.hom.app F (scalarUnit ι.toRingHom x)))

/-- The compact Hom and compact-to-ordinary maps commute with finite coefficient
extension. The equations on pure tensors determine the linear comparison entirely.
Source: BS 6.8.2(1), 6.8.14; Milne 18.3(b)
(blueprint: def-a1-finite-adic-compactification-section-data). -/
structure FiniteScalarProper (ι : E →ₐ[ℚ_[l]] L) {R : ContinuousRational.Family.{u} l}
    {U T : Geometry D} {AEU : FiniteAt D l hl E R U} {AET : FiniteAt D l hl E R T}
    {ALU : FiniteAt D l hl L R U} {ALT : FiniteAt D l hl L R T}
    {j : U.scheme ⟶ T.scheme} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] [IsProper (T.scheme ↘ Spec (.of D.k))]
    {OE : FiniteOpen D l hl E R AEU AET j} {OL : FiniteOpen D l hl L R ALU ALT j}
    {SU : FiniteScalar D l hl E L ι R AEU ALU}
    {ST : FiniteScalar D l hl E L ι R AET ALT}
    (B : FiniteScalarOpen D l hl E L ι OE OL SU ST)
    (PE : FiniteProper D l hl E OE) (PL : FiniteProper D l hl L OL) where
  compact : PE.compact ⋙ ModuleCat.extendScalars ι.toRingHom ≅ SU.heart ⋙ PL.compact
  hom : ∀ (F : sfRationalHeart l E U.scheme) (x : PE.compact.obj F),
    PL.hom (SU.heart.obj F)
        (compact.hom.app F (scalarUnit ι.toRingHom x)) =
      ST.unit.inv ≫ ST.heart.map (PE.hom F x) ≫ B.extension.hom.app F
  comparison : ∀ (F : sfRationalHeart l E U.scheme) (x : PE.compact.obj F),
    PL.comparison.app (SU.heart.obj F)
        (compact.hom.app F (scalarUnit ι.toRingHom x)) =
      SU.ordinary.hom.app F
        (scalarUnit ι.toRingHom (PE.comparison.app F x))
  compactification : ∀ (F : sfRationalHeart l E U.scheme) (x : PE.compact.obj F),
    PL.compactification.hom.app (SU.heart.obj F)
        (compact.hom.app F (scalarUnit ι.toRingHom x)) =
      ALT.ordinary.map (B.extension.hom.app F)
        (ST.ordinary.hom.app (OE.shriek.obj F)
          (scalarUnit ι.toRingHom (PE.compactification.hom.app F x)))


/-- One simultaneous finite-stage construction, including all open restrictions and
all coefficient embeddings (also identity embeddings and ramified extensions).
Source: BS 6.8.14--6.8.15; Milne 18.1, 18.3(b)
(blueprint: def-a1-finite-adic-compactification-section-data). -/
structure FiniteFamily where
  realization : ContinuousRational.Family.{u} l
  atScheme : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (W : Geometry D), FiniteAt D l hl A realization W
  openImage : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {U T : Geometry D} (j : U.scheme ⟶ T.scheme) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))],
    FiniteOpen D l hl A realization (atScheme A U) (atScheme A T) j
  proper : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {U T : Geometry D} (j : U.scheme ⟶ T.scheme) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] [IsProper (T.scheme ↘ Spec (.of D.k))],
    FiniteProper D l hl A (openImage A j)
  scalar : ∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (ι : A →ₐ[ℚ_[l]] B) (W : Geometry D),
    FiniteScalar D l hl A B ι realization (atScheme A W) (atScheme B W)
  scalarOpen : ∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (ι : A →ₐ[ℚ_[l]] B) {U T : Geometry D} (j : U.scheme ⟶ T.scheme)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of D.k))],
    FiniteScalarOpen D l hl A B ι (openImage A j) (openImage B j)
      (scalar A B ι U) (scalar A B ι T)
  scalarProper : ∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (ι : A →ₐ[ℚ_[l]] B) {U T : Geometry D} (j : U.scheme ⟶ T.scheme)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of D.k))]
    [IsProper (T.scheme ↘ Spec (.of D.k))],
    FiniteScalarProper D l hl A B ι (scalarOpen A B ι j) (proper A j) (proper B j)


end AdicCompactificationSections
end WeilConjectures
