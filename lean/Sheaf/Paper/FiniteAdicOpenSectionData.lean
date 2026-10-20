/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.FiniteAdicOrdinarySectionData

/-! # Finite adic compactification and section comparison data

Source: Bhatt--Scholze 6.8.14--6.8.15; Milne 18.1, 18.3(b)
(blueprint: def-a1-finite-adic-open-section-data).

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

/-- The actual completed pullback, in the intrinsic rational presentation.
Source: BS 6.8.15 (blueprint: def-a1-finite-adic-open-section-data). -/
def pull {U T : Geometry D} (j : U.scheme ⟶ T.scheme) :=
  letI := smoothQbarResidueInvertible D l hl U.scheme
  letI := smoothQbarResidueInvertible D l hl T.scheme
  rationalDerivedPullback l E j

/-- The compactification with the given proper ambient scheme and the given open map.
Its factorization is exactly the structure-morphism equation, with no Nagata choice.
Source: Milne 18.1 (blueprint: def-a1-finite-adic-open-section-data). -/
def compactification {U T : Geometry D} (j : U.scheme ⟶ T.scheme)
    [IsOpenImmersion j] [j.IsOver (Spec (.of D.k))]
    [IsProper (T.scheme ↘ Spec (.of D.k))] :
    Compactification (U.scheme ↘ Spec (.of D.k)) where
  Z := T.scheme
  g := T.scheme ↘ Spec (.of D.k)
  i := j
  comm := (CategoryTheory.HomIsOver.comp_over (f := j) (S := Spec (.of D.k))).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- Continuity in the literal open presentation; its source scheme is definitionally U.
Source: Stacks 098K
(blueprint: def-a1-finite-adic-open-section-data). -/
instance continuousSliceContinuous {U T : Scheme.{u}} (j : U ⟶ T)
    [hj : IsOpenImmersion j] :
    (cbcSliceFunctor T (cbcOpenObject j hj)).IsContinuous
      ((ProEt.topology T).over (cbcOpenObject j hj)) (ProEt.topology U) :=
  cbcSliceFunctor_continuous T (cbcOpenObject j hj)

/-- The concrete continuous module transport to the open slice, retaining the same
sections and actions through the specified coefficient map.
Source: Stacks 098K, 03DI; BS 6.8.14
(blueprint: def-a1-finite-adic-open-section-data). -/
def continuousModuleToSlice {U T : Geometry D} (j : U.scheme ⟶ T.scheme)
    [hj : IsOpenImmersion j]
    (c : (rationalCoefficientSheaf l T.scheme E).over (cbcOpenObject j hj) ⟶
      ((cbcSliceFunctor T.scheme (cbcOpenObject j hj)).sheafPushforwardContinuous
        CommRingCat.{u + 1} ((ProEt.topology T.scheme).over (cbcOpenObject j hj))
          (ProEt.topology U.scheme)).obj (rationalCoefficientSheaf l U.scheme E)) :=
  @SheafOfModules.pushforward.{u + 1}
    (Over (cbcOpenObject j hj)) _ U.scheme.ProEt _
    ((ProEt.topology T.scheme).over (cbcOpenObject j hj)) (ProEt.topology U.scheme)
    (cbcSliceFunctor T.scheme (cbcOpenObject j hj))
    ((proEtaleModuleCoefficients (rationalCoefficientSheaf l T.scheme E)).over
      (cbcOpenObject j hj))
    (proEtaleModuleCoefficients (rationalCoefficientSheaf l U.scheme E))
    (cbcSliceFunctor_continuous T.scheme (cbcOpenObject j hj))
    ((sheafCompose ((ProEt.topology T.scheme).over (cbcOpenObject j hj))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c)

/-- The finite-stage open extension with its actual tower-functor normalization,
continuous module realization, open adjunction and adic geometric fibres.
Source: BS 6.8.14--6.8.15; Stacks 03DI, 03DJ
(blueprint: def-a1-finite-adic-open-section-data). -/
structure FiniteOpen (R : ContinuousRational.Family.{u} l)
    {U T : Geometry D} (AU : FiniteAt D l hl E R U) (AT : FiniteAt D l hl E R T)
    (j : U.scheme ⟶ T.scheme) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] where
  point : AU.point = AT.point
  shriek : sfRationalHeart l E U.scheme ⥤ sfRationalHeart l E T.scheme
  [additive : shriek.Additive]
  [linear : shriek.Linear E]
  [limits : PreservesFiniteLimits shriek]
  [colimits : PreservesFiniteColimits shriek]
  tower : shriek ⋙ (sfRationalHeartProperty l E T.scheme).ι ≅
    (sfRationalHeartProperty l E U.scheme).ι ⋙
      sfCompactSupportFiniteFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        (Compactification.ofIsOpenImmersion j) E
  restriction : sfRationalHeart l E T.scheme ⥤ sfRationalHeart l E U.scheme
  pullback : restriction ⋙ (sfRationalHeartProperty l E U.scheme).ι ≅
    (sfRationalHeartProperty l E T.scheme).ι ⋙ pull D l hl E j
  adjunction : shriek ⊣ restriction
  [open_unit : IsIso adjunction.unit]
  coefficient : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj
    (rationalCoefficientSheaf l T.scheme E) ≅ rationalCoefficientSheaf l U.scheme E
  coefficient_normalized : rationalCoefficientRestrictionNormalized l E j coefficient.hom
  extension : shriek ⋙ AT.sheaf ≅ AU.sheaf ⋙
    proEtaleRingOpenExtension j (rationalCoefficientSheaf l T.scheme E)
      (rationalCoefficientSheaf l U.scheme E) coefficient
  slice_coefficient :
    (rationalCoefficientSheaf l T.scheme E).over (cbcOpenObject j inferInstance) ⟶
      ((cbcSliceFunctor T.scheme (cbcOpenObject j inferInstance)).sheafPushforwardContinuous
        CommRingCat.{u + 1} ((ProEt.topology T.scheme).over (cbcOpenObject j inferInstance))
          (ProEt.topology U.scheme)).obj (rationalCoefficientSheaf l U.scheme E)
  slice_normalized : ∀ (V : Over (cbcOpenObject j inferInstance))
    (s : (rationalCoefficientSheaf l T.scheme E).obj.obj (Opposite.op V.left))
    (x : V.left.left),
    rationalCoefficientValue l E U.scheme
        (Opposite.op ((cbcSliceFunctor T.scheme (cbcOpenObject j inferInstance)).obj V))
          (slice_coefficient.hom.app (Opposite.op V) s) x =
      rationalCoefficientValue l E T.scheme (Opposite.op V.left) s x
  sheafification : shriek ⋙ AT.sheaf ≅
    AU.sheaf ⋙ continuousModuleToSlice D l E j slice_coefficient ⋙
      proEtaleRingedExtensionByZero (cbcOpenObject j inferInstance)
        (rationalCoefficientSheaf l T.scheme E)
  inverse_image : restriction ⋙ AU.sheaf ≅ AT.sheaf ⋙
    proEtaleRingModulePullback j (rationalCoefficientSheaf l T.scheme E)
      (rationalCoefficientSheaf l U.scheme E) coefficient
  unit : restriction.obj AT.unit ≅ AU.unit
  adjunction_unit : ∀ F : sfRationalHeart l E U.scheme,
    AU.sheaf.map (adjunction.unit.app F) ≫
        inverse_image.hom.app (shriek.obj F) ≫
        (proEtaleRingModulePullback j (rationalCoefficientSheaf l T.scheme E)
          (rationalCoefficientSheaf l U.scheme E) coefficient).map
            (extension.hom.app F) =
      (Adjunction.ofIsRightAdjoint (proEtaleRingModulePullback j
        (rationalCoefficientSheaf l T.scheme E)
          (rationalCoefficientSheaf l U.scheme E) coefficient)).unit.app (AU.sheaf.obj F)
  ordinary_pull : proEtaleRingModulePullback j (rationalCoefficientSheaf l T.scheme E)
    (rationalCoefficientSheaf l U.scheme E) coefficient ≅
      ContinuousRational.modulePull j
        (R.along E (X := realizationBase D l hl U)
          (Y := realizationBase D l hl T) j).coefficient
  unit_one : ∀ V : T.scheme.ProEt,
    (AU.sheaf.map unit.hom).val.app (Opposite.op ((proEtaleBaseChange j).obj V))
      ((inverse_image.inv.app AT.unit).val.app
        (Opposite.op ((proEtaleBaseChange j).obj V))
        ((ordinary_pull.inv.app (AT.sheaf.obj AT.unit)).val.app
          (Opposite.op ((proEtaleBaseChange j).obj V))
          (ContinuousRational.moduleUnit j
            (R.along E (X := realizationBase D l hl U)
              (Y := realizationBase D l hl T) j).coefficient
            (AT.sheaf.obj AT.unit) V (unitSection D l hl E AT (Opposite.op V))))) =
      unitSection D l hl E AU (Opposite.op ((proEtaleBaseChange j).obj V))
  ordinary_restriction : AT.ordinary ⟶ restriction ⋙ AU.ordinary
  ordinary_restriction_hom : ∀ (F : sfRationalHeart l E T.scheme) (x : AT.ordinary.obj F),
    AU.ordinary_hom (restriction.obj F) (ordinary_restriction.app F x) =
      unit.inv ≫ restriction.map (AT.ordinary_hom F x)
  inside : ∀ (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ U.scheme),
    Nonempty (shriek ⋙ (sfRationalHeartProperty l E T.scheme).ι ⋙
      sfAdicRationalFiber l E T.scheme (x ≫ j) ≅
        (sfRationalHeartProperty l E U.scheme).ι ⋙ sfAdicRationalFiber l E U.scheme x)
  outside : ∀ (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ T.scheme),
    Set.range x.base ⊆ (Set.range j.base)ᶜ →
      ∀ F : sfRationalHeart l E U.scheme,
        IsZero ((sfAdicRationalFiber l E T.scheme x).obj (shriek.obj F).obj)

attribute [instance] FiniteOpen.additive FiniteOpen.linear FiniteOpen.limits FiniteOpen.colimits
  FiniteOpen.open_unit


end AdicCompactificationSections
end WeilConjectures
