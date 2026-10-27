/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.FiniteAdicOpenSectionData

/-! # Finite adic compactification and section comparison data

Source: Bhatt--Scholze 6.8.14--6.8.15; Milne 18.1, 18.3(b)
(blueprint: def-a1-finite-adic-proper-section-data).

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

/-- The restriction map on coefficient-unit morphisms, using the specified inverse
open unit. This is a construction from functoriality and the adjunction, not a map
chosen from an existence assertion.
Source: Milne 18.3(b) (blueprint: def-a1-finite-adic-proper-section-data). -/
def restrictionHom {R : ContinuousRational.Family.{u} l} {U T : Geometry D}
    {AU : FiniteAt D l hl E R U} {AT : FiniteAt D l hl E R T}
    {j : U.scheme ⟶ T.scheme} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] (O : FiniteOpen D l hl E R AU AT j)
    (F : sfRationalHeart l E U.scheme) (t : AT.unit ⟶ O.shriek.obj F) : AU.unit ⟶ F :=
  O.unit.inv ≫ O.restriction.map t ≫ (asIso (O.adjunction.unit.app F)).inv

/-- Realization of the inverse open unit. This is obtained from the actual
continuous pullback counit and the sheaf comparison of the open adjunction.
Source: BS 6.8.15; Milne 18.3(b)
(blueprint: def-a1-finite-adic-proper-section-data). -/
def realizedOpenInverseUnit {R : ContinuousRational.Family.{u} l} {U T : Geometry D}
    {AU : FiniteAt D l hl E R U} {AT : FiniteAt D l hl E R T}
    {j : U.scheme ⟶ T.scheme} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] (O : FiniteOpen D l hl E R AU AT j)
    (F : sfRationalHeart l E U.scheme) :
    (ContinuousRational.derivedPull j
      (R.along E (X := realizationBase D l hl U)
        (Y := realizationBase D l hl T) j).coefficient).obj
          (AT.J.obj (O.shriek.obj F).obj) ⟶ AU.J.obj F.obj :=
  (ContinuousRational.derivedPull j
    (R.along E (X := realizationBase D l hl U)
      (Y := realizationBase D l hl T) j).coefficient).map
        (AT.heart.hom.app (O.shriek.obj F)) ≫
    (R.along E (X := realizationBase D l hl U)
      (Y := realizationBase D l hl T) j).counit.app
        ((CochainComplex.singleFunctor _ 0).obj (AT.sheaf.obj (O.shriek.obj F))) ≫
    DerivedCategory.Q.map
      ((familyPullSingle l E R (X := realizationBase D l hl U)
        (Y := realizationBase D l hl T) j).hom.app _) ≫
    (DerivedCategory.singleFunctor _ 0).map
      (O.ordinary_pull.inv.app (AT.sheaf.obj (O.shriek.obj F)) ≫
        O.inverse_image.inv.app (O.shriek.obj F) ≫
        AU.sheaf.map (asIso (O.adjunction.unit.app F)).inv) ≫ AU.heart.inv.app F

/-- The canonical derived compact-to-ordinary arrow, including the actual
structure-morphism equation after the direct-image compositor. Neither H0/Hom
maps nor the restriction formula occur in its definition.
Source: Milne 18.1, 18.3(b); BS 6.8.15
(blueprint: def-a1-finite-adic-proper-section-data). -/
def compactOrdinaryArrow {R : ContinuousRational.Family.{u} l} {U T : Geometry D}
    {AU : FiniteAt D l hl E R U} {AT : FiniteAt D l hl E R T}
    {j : U.scheme ⟶ T.scheme} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] (O : FiniteOpen D l hl E R AU AT j)
    (F : sfRationalHeart l E U.scheme) :
    (ContinuousRational.DirectImage.derivedPush (T.scheme ↘ Spec (.of D.k))
      (R.along E (X := realizationBase D l hl T)
        (Y := realizationBase D l hl ⟨Spec (.of D.k)⟩)
          (T.scheme ↘ Spec (.of D.k))).coefficient).obj
            (AT.J.obj (O.shriek.obj F).obj) ⟶
    (ContinuousRational.DirectImage.derivedPush (U.scheme ↘ Spec (.of D.k))
      (R.along E (X := realizationBase D l hl U)
        (Y := realizationBase D l hl ⟨Spec (.of D.k)⟩)
          (U.scheme ↘ Spec (.of D.k))).coefficient).obj (AU.J.obj F.obj) :=
  derivedCompactOrdinaryArrow l E R AT.direct_image
    (X := realizationBase D l hl T) (Y := realizationBase D l hl ⟨Spec (.of D.k)⟩)
    (Z := realizationBase D l hl U) (T.scheme ↘ Spec (.of D.k)) j
    (AT.J.obj (O.shriek.obj F).obj) (AU.J.obj F.obj)
    (realizedOpenInverseUnit D l hl E O F) ≫
      eqToHom (congrArg
        (fun f : U.scheme ⟶ Spec (.of D.k) ↦
          (ContinuousRational.DirectImage.derivedPush f
            (R.along E (X := realizationBase D l hl U)
              (Y := realizationBase D l hl ⟨Spec (.of D.k)⟩) f).coefficient).obj
                (AU.J.obj F.obj))
        (CategoryTheory.HomIsOver.comp_over (f := j) (S := Spec (.of D.k))))

/-- Equality of the actual finite compactification projection adjuncts.
Source: BS 6.7.6, 6.8.15; Milne 18.1
(blueprint: def-a1-finite-adic-proper-section-data). -/
def CompactificationProjectionNormalized {U T : Geometry D} (j : U.scheme ⟶ T.scheme)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of D.k))]
    [IsProper (T.scheme ↘ Spec (.of D.k))]
    (K : sfIntegralConstructibleCategory l E U.scheme)
    (identity : ∀ n : ℕ, FiniteIdentityImage l E T.scheme n)
    (integral : sfIntegralCompactSupportValue l E D.k (finiteFieldDatumPrimeUnit D l hl)
      (compactification D j) K ≅
    integralImage D l hl E T.scheme
      ((sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        (Compactification.ofIsOpenImmersion j) E).obj K)) : Prop :=
  letI := imageProduct D l hl E T
    ((sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
      (Compactification.ofIsOpenImmersion j) E).obj K)
  ∀ n : ℕ,
  (scalarReductionDerivedExtension l E (Spec (.of D.k)) n).map
      (integral.hom.hom ≫ (imageObjectIso D l hl E T
        ((sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
          (Compactification.ofIsOpenImmersion j) E).obj K)).hom) ≫
    sfDirectImageReductionComparison l E (T.scheme ↘ Spec (.of D.k))
      (chosenImage D l hl E T
        ((sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
          (Compactification.ofIsOpenImmersion j) E).obj K)) n ≫
    (proEtaleConstantDerivedDirectImage (T.scheme ↘ Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1))).map
        ((sfCompactSupportFiniteReductionIso l D.k (finiteFieldDatumPrimeUnit D l hl)
          (Compactification.ofIsOpenImmersion j) E K n).hom ≫
            (identity n).derived.hom.app _) =
    sfCompactSupportChosenReduction l D.k (finiteFieldDatumPrimeUnit D l hl)
      (compactification D j) E K n

/-- The normalized integral compactification comparison, with its identity image
and the exact finite projection equations. Sigma and subtype store these data
without generating large dependent-record recursors.
Source: BS 6.7.6, 6.8.15; Milne 18.1
(blueprint: def-a1-finite-adic-proper-section-data). -/
def CompactificationModel {U T : Geometry D} (j : U.scheme ⟶ T.scheme)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of D.k))]
    [IsProper (T.scheme ↘ Spec (.of D.k))]
    (K : sfIntegralConstructibleCategory l E U.scheme) :=
  Σ identity : ∀ n : ℕ, FiniteIdentityImage l E T.scheme n,
    { integral : sfIntegralCompactSupportValue l E D.k (finiteFieldDatumPrimeUnit D l hl)
      (compactification D j) K ≅
    integralImage D l hl E T.scheme
      ((sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        (Compactification.ofIsOpenImmersion j) E).obj K) //
      CompactificationProjectionNormalized D l hl E j K identity integral }

/-- The specified finite identity-image models.
Source: BS 6.7.6 (blueprint: def-a1-finite-adic-proper-section-data). -/
def CompactificationModel.identity {U T : Geometry D} {j : U.scheme ⟶ T.scheme}
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of D.k))]
    [IsProper (T.scheme ↘ Spec (.of D.k))]
    {K : sfIntegralConstructibleCategory l E U.scheme}
    (M : CompactificationModel D l hl E j K) :
    ∀ n : ℕ, FiniteIdentityImage l E T.scheme n := M.1

/-- The integral compactification comparison with the actual ordinary image.
Source: BS 6.7.6, 6.8.15 (blueprint: def-a1-finite-adic-proper-section-data). -/
def CompactificationModel.integral {U T : Geometry D} {j : U.scheme ⟶ T.scheme}
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of D.k))]
    [IsProper (T.scheme ↘ Spec (.of D.k))]
    {K : sfIntegralConstructibleCategory l E U.scheme}
    (M : CompactificationModel D l hl E j K) :
    sfIntegralCompactSupportValue l E D.k (finiteFieldDatumPrimeUnit D l hl)
      (compactification D j) K ≅
    integralImage D l hl E T.scheme
      ((sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        (Compactification.ofIsOpenImmersion j) E).obj K) := M.2.val

/-- The retained equality of every finite projection adjunct.
Source: BS 6.7.6 (blueprint: def-a1-finite-adic-proper-section-data). -/
abbrev CompactificationModel.projections {U T : Geometry D} (j : U.scheme ⟶ T.scheme)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of D.k))]
    [IsProper (T.scheme ↘ Spec (.of D.k))]
    (K : sfIntegralConstructibleCategory l E U.scheme)
    (M : CompactificationModel D l hl E j K) :
    CompactificationProjectionNormalized D l hl E j K
      M.1 M.2.val := M.2.property

/-- A specified component of the realized compactification comparison.
Source: BS 6.7.6, 6.8.15; Milne 18.1
(blueprint: def-a1-finite-adic-proper-section-data). -/
def compactRealizationSource {R : ContinuousRational.Family.{u} l} {U T : Geometry D}
    {j : U.scheme ⟶ T.scheme} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] [IsProper (T.scheme ↘ Spec (.of D.k))] (AT : FiniteAt D l hl E R T)
    (F : sfRationalHeart l E U.scheme) :=
  AT.point.integral.hom.app
    (sfIntegralCompactSupportValue l E D.k (finiteFieldDatumPrimeUnit D l hl)
      (compactification D j) F.obj.obj)

/-- A specified component of the realized compactification comparison.
Source: BS 6.7.6, 6.8.15; Milne 18.1
(blueprint: def-a1-finite-adic-proper-section-data). -/
def compactIntegralTransport {R : ContinuousRational.Family.{u} l} {U T : Geometry D}
    {j : U.scheme ⟶ T.scheme} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] [IsProper (T.scheme ↘ Spec (.of D.k))]
    (F : sfRationalHeart l E U.scheme) (M : CompactificationModel D l hl E j F.obj.obj) :=
  (pbcDerivedExtend
    ((R.realization E (realizationBase D l hl ⟨Spec (.of D.k)⟩)).integralIso.hom ≫
      (R.realization E (realizationBase D l hl ⟨Spec (.of D.k)⟩)).inclusion)).map
    ((integralDetailedTransport (Spec (.of D.k)) l E).map M.integral.hom.hom)

/-- A specified component of the realized compactification comparison.
Source: BS 6.7.6, 6.8.15; Milne 18.1
(blueprint: def-a1-finite-adic-proper-section-data). -/
def compactImageUnrealization {R : ContinuousRational.Family.{u} l} {U T : Geometry D}
    {j : U.scheme ⟶ T.scheme} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] [IsProper (T.scheme ↘ Spec (.of D.k))] (AT : FiniteAt D l hl E R T)
    (F : sfRationalHeart l E U.scheme) :=
  AT.point.integral.inv.app (integralImage D l hl E T.scheme
    ((sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
      (Compactification.ofIsOpenImmersion j) E).obj F.obj.obj))

/-- A specified component of the realized compactification comparison.
Source: BS 6.7.6, 6.8.15; Milne 18.1
(blueprint: def-a1-finite-adic-proper-section-data). -/
def compactImageComparison {R : ContinuousRational.Family.{u} l} {U T : Geometry D}
    {j : U.scheme ⟶ T.scheme} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] [IsProper (T.scheme ↘ Spec (.of D.k))] (AT : FiniteAt D l hl E R T)
    (F : sfRationalHeart l E U.scheme) :=
  (AT.image ((sfRationalConstructibleLocalization l E T.scheme).obj
    ((sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
      (Compactification.ofIsOpenImmersion j) E).obj F.obj.obj))).hom

/-- A specified component of the realized compactification comparison.
Source: BS 6.7.6, 6.8.15; Milne 18.1
(blueprint: def-a1-finite-adic-proper-section-data). -/
def compactOpenTransport {R : ContinuousRational.Family.{u} l} {U T : Geometry D}
    {AU : FiniteAt D l hl E R U} {AT : FiniteAt D l hl E R T}
    {j : U.scheme ⟶ T.scheme} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] (O : FiniteOpen D l hl E R AU AT j)
    (F : sfRationalHeart l E U.scheme) :=
  (ContinuousRational.DirectImage.derivedPush (T.scheme ↘ Spec (.of D.k))
    (R.along E (X := realizationBase D l hl T)
      (Y := realizationBase D l hl ⟨Spec (.of D.k)⟩)
        (T.scheme ↘ Spec (.of D.k))).coefficient).map
    (AT.J.map (O.tower.inv.app F))

/-- The realized compactification comparison is the composite of the five
specified arrows. Equality in the arrow category fixes endpoints as well as maps.
This is the integral-transport normalization, expressed without repeated conversion
through the large coefficient-transport objects.
Source: BS 6.7.6, 6.8.15; Milne 18.1
(blueprint: def-a1-finite-adic-proper-section-data). -/
def CompactPointNormalized {R : ContinuousRational.Family.{u} l} {U T : Geometry D}
    {AU : FiniteAt D l hl E R U} {AT : FiniteAt D l hl E R T}
    {j : U.scheme ⟶ T.scheme} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] (O : FiniteOpen D l hl E R AU AT j)
    [IsProper (T.scheme ↘ Spec (.of D.k))]
    (F : sfRationalHeart l E U.scheme) (M : CompactificationModel D l hl E j F.obj.obj)
    (c : sfRationalCompactSupportValue l E D.k (finiteFieldDatumPrimeUnit D l hl)
      (compactification D j) F.obj.obj ≅
        rationalImage D l hl E T.scheme (O.shriek.obj F).obj) : Prop :=
  ∃ (P Q S V : DerivedCategory (pbcModules (Spec (.of D.k))
      (rationalCoefficientSheaf l (Spec (.of D.k)) E)))
    (f : AT.point.J.obj (sfRationalCompactSupportValue l E D.k
      (finiteFieldDatumPrimeUnit D l hl) (compactification D j) F.obj.obj) ⟶ P)
    (g : P ⟶ Q) (h : Q ⟶ S) (i : S ⟶ V)
    (t : V ⟶ (ContinuousRational.DirectImage.derivedPush (T.scheme ↘ Spec (.of D.k))
      (R.along E (X := realizationBase D l hl T)
        (Y := realizationBase D l hl ⟨Spec (.of D.k)⟩)
          (T.scheme ↘ Spec (.of D.k))).coefficient).obj (AT.J.obj (O.shriek.obj F).obj)),
    Arrow.mk f = Arrow.mk (compactRealizationSource D l hl E (j := j) AT F) ∧
    Arrow.mk g = Arrow.mk (compactIntegralTransport D l hl E (R := R) F M) ∧
    Arrow.mk h = Arrow.mk (compactImageUnrealization D l hl E (j := j) AT F) ∧
    Arrow.mk i = Arrow.mk (compactImageComparison D l hl E (j := j) AT F) ∧
    Arrow.mk t = Arrow.mk (compactOpenTransport D l hl E O F) ∧
    AT.point.J.map c.hom ≫ (AT.image (O.shriek.obj F).obj).hom = f ≫ g ≫ h ≫ i ≫ t

set_option maxHeartbeats 800000 in
-- Elaborating the normalization diagrams unfolds several derived coefficient transports.
/-- Proper-compactification H⁰, as a natural linear Hom identification, and the
specified compact-to-ordinary map. The two map normalizations retain the actual
open-unit restriction, including its further ordinary open restrictions.
Source: Milne 18.1, 18.3(b); BS 6.8.15
(blueprint: def-a1-finite-adic-proper-section-data). -/
structure FiniteProper {R : ContinuousRational.Family.{u} l} {U T : Geometry D}
    {AU : FiniteAt D l hl E R U} {AT : FiniteAt D l hl E R T}
    {j : U.scheme ⟶ T.scheme} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] (O : FiniteOpen D l hl E R AU AT j)
    [IsProper (T.scheme ↘ Spec (.of D.k))] where
  compact : sfRationalHeart l E U.scheme ⥤ ModuleCat.{u} E
  compact_obj : ∀ F, compact.obj F =
    rationalCompactCohomology D l hl E U.scheme (compactification D j) F.obj 0
  hom : ∀ F, (compact.obj F : Type u) ≃ₗ[E] (AT.unit ⟶ O.shriek.obj F)
  natural : ∀ (F G : sfRationalHeart l E U.scheme) (f : F ⟶ G) (x : compact.obj F),
    hom G (compact.map f x) = hom F x ≫ O.shriek.map f
  comparison : compact ⟶ AU.ordinary
  /-- A derived comparison from the actual compact coefficient complex at
  (T,j,b), so the compact H0 comparison is its cohomology map. -/
  compact_point : ∀ F : sfRationalHeart l E U.scheme,
    sfRationalCompactSupportValue l E D.k (finiteFieldDatumPrimeUnit D l hl)
      (compactification D j) F.obj.obj ≅
        rationalImage D l hl E T.scheme (O.shriek.obj F).obj
  compact_model : ∀ F : sfRationalHeart l E U.scheme,
    CompactificationModel D l hl E j F.obj.obj
  compact_point_normalized : ∀ F : sfRationalHeart l E U.scheme,
    CompactPointNormalized D l hl E O F (compact_model F) (compact_point F)
  /-- The comparison is pinned to Rb_*(adjunct(open-unit inverse)) and the
  compositor. The restriction equation below is a separate obligation. -/
  comparison_derived_map : ∀ (F : sfRationalHeart l E U.scheme) (x : compact.obj F),
    AU.point.J.map (AU.point.hom (rationalImage D l hl E U.scheme F.obj)
      ((eqToIso (AU.ordinary_obj F)).hom (comparison.app F x))) ≫ (AU.image F.obj).hom =
    eqToHom (congrArg (fun P : PointSection D l hl E R ↦
      P.J.obj (pointCoefficient D l hl E)) O.point) ≫
      AT.point.J.map (AT.point.hom
        (sfRationalCompactSupportValue l E D.k (finiteFieldDatumPrimeUnit D l hl)
          (compactification D j) F.obj.obj)
        ((eqToIso (compact_obj F)).hom x)) ≫
      AT.point.J.map (compact_point F).hom ≫ (AT.image (O.shriek.obj F).obj).hom ≫
        compactOrdinaryArrow D l hl E O F
  comparison_canonical : ∀ (F : sfRationalHeart l E U.scheme) (x : compact.obj F),
    AU.ordinary_hom F (comparison.app F x) = restrictionHom D l hl E O F (hom F x)
  compactification : compact ≅ O.shriek ⋙ AT.ordinary
  /-- Cohomology of the point-fibre image of the displayed compactification
  map, on exactly rationalCompactSections at compactification D j. -/
  compactification_h0 : ∀ (F : sfRationalHeart l E U.scheme) (x : compact.obj F),
    (eqToIso (AT.ordinary_obj (O.shriek.obj F))).hom (compactification.hom.app F x) =
      (DerivedCategory.coefficientFdCohomology E 0).map
        ((pointRationalFibre D l hl E).map (compact_point F).hom)
          ((eqToIso (compact_obj F)).hom x)
  compactification_hom : ∀ (F : sfRationalHeart l E U.scheme) (x : compact.obj F),
    AT.ordinary_hom (O.shriek.obj F) (compactification.hom.app F x) = hom F x


end AdicCompactificationSections
end WeilConjectures
