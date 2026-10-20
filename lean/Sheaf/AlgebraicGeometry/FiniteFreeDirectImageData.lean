/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-!
# Normalized coefficient models for finite-free direct image

Source: Stacks Project, Tags 0B56 and 0944
(blueprint: def-sp-finite-free-direct-image-data).

All module and derived categories are the existing ones. The auxiliary records bundle
coefficient squares and normalized presentations of the existing scalar functors.
Balancing is the conjugate of the canonical restriction/direct-image comparison, and
its right mate is the specified counit-tensor map. No arbitrary comparison is bound.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

-- These are the same exactness instances formerly reexported through FourCorners.
attribute [instance] proEtaleRingRestrictScalars_preservesFiniteLimits
  proEtaleRingRestrictScalars_preservesFiniteColimits

/-- A presentation of the existing derived scalar extension on the actual small site.
Source: Stacks Tag 06YY (blueprint: def-sp-finite-free-direct-image-data). -/
abbrev Presentation (X : Scheme.{u}) {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) :=
  SheafOfModules.SuccessiveDerivedQuotient.Presentation.{u + 1, u, u + 1, u + 2}
    (C := X.ProEt) (J := ProEt.topology X) (R := R) (S := S)
    (hD := fun T ↦ proEtaleRingModules_hasDerivedCategory X T) a

set_option genSizeOf false in
/-- A normalized family of the existing scalar functors, with its multiplication unit.
`presentation` fixes ordinary objects and maps and the universal derived counit;
`normalization` fixes the balanced associators and tensor units. The additional
adjunction is normalized against exact scalar restriction, and the multiplication
isomorphism is fixed by its ordinary pure-tensor formula and the universal counit.
Source: Stacks Tags 03EK, 06YY and 07A6
(blueprint: def-sp-finite-free-direct-image-data). -/
structure ScalarModel (X : Scheme.{u}) where
  /-- Existing universal scalar-extension pairs, without a second tensor definition. -/
  presentation : ∀ {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}},
    (a : R ⟶ S) → Presentation X a
  /-- The recorded balanced associator and its K-flat normalization. -/
  normalization :
    SheafOfModules.SuccessiveDerivedQuotient.Normalization.{u + 1, u, u + 1, u + 2}
      (C := X.ProEt) (J := ProEt.topology X)
      (hD := fun T ↦ proEtaleRingModules_hasDerivedCategory X T) presentation
  /-- Scalar adjunction to the actual exact restriction, rather than an unrelated functor. -/
  adjunction : ∀ {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S),
    (presentation a).derived ⊣ (proEtaleRingRestrictScalars a).mapDerivedCategory
  /-- Normalization of the derived scalar unit at every flat-term K-flat complex. -/
  adjunction_unit : ∀ {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (P : CochainComplex (proEtaleRingModules X R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := R) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology X) (R := R) (P.X n)) →
    (adjunction a).unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
      (proEtaleRingRestrictScalars a).mapDerivedCategory.map
        ((presentation a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      (proEtaleRingRestrictScalars a).mapDerivedCategoryFactorsh.hom.app
        (((presentation a).ordinary.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P)) =
    DerivedCategory.Qh.map
      (((normalization.ordinaryAdjunction a).mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ _).obj P))
  /-- Multiplication `r ⊗ x ↦ r x` before localization. -/
  ordinaryUnit : ∀ R : Sheaf (ProEt.topology X) CommRingCat.{u + 1},
    (presentation (𝟙 R)).ordinary ≅ 𝟭 (proEtaleRingModules X R)
  /-- The pure-tensor normalization determines the ordinary unit uniquely. -/
  ordinaryUnit_pure : ∀ (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : proEtaleRingModules X R) (U : X.ProEtᵒᵖ) (r : R.obj.obj U) (x : M.val.obj U),
    ((ordinaryUnit R).hom.app M).val.app U
      (SheafOfModules.SuccessiveDerivedQuotient.sectionTensor
        (presentation (𝟙 R)) M U r x) = r • x
  /-- Multiplication after the universal derived scalar extension. -/
  unit : ∀ R : Sheaf (ProEt.topology X) CommRingCat.{u + 1},
    (presentation (𝟙 R)).derived ≅ 𝟭 (DerivedCategory (proEtaleRingModules X R))
  /-- The derived multiplication is determined by its universal counit. -/
  unit_normalization : ∀ (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (H : HomotopyCategory (proEtaleRingModules X R) (.up ℤ)),
    (unit R).hom.app (DerivedCategory.Qh.obj H) =
      (presentation (𝟙 R)).counit.app H ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory (ordinaryUnit R).hom (.up ℤ)).app H) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryIdIso (proEtaleRingModules X R) (.up ℤ)).hom.app H)

/-- The canonical scalar shift is the adjoint of the termwise restriction shift.
Source: Stacks Tag 07A6 (blueprint: def-sp-finite-free-direct-image-data). -/
instance scalarCommShift {X : Scheme.{u}} (s : ScalarModel X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    (s.presentation a).derived.CommShift ℤ :=
  (s.adjunction a).leftAdjointCommShift ℤ

/-- The coefficient ring at both ends, with the specified inverse-image identification.
Source: Stacks Tag 0B56 (blueprint: def-sp-finite-free-direct-image-data). -/
structure Coefficients {Z W : Scheme.{u}} (q : Z ⟶ W) where
  /-- Ring sheaf on the target. -/
  target : Sheaf (ProEt.topology W) CommRingCat.{u + 1}
  /-- Ring sheaf on the source. -/
  source : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}
  /-- The specified identification of inverse-image coefficients. -/
  identification : (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj target ≅ source

/-- Compatible coefficient maps on the two sites; the only condition is the ring square.
Source: Stacks Tag 0B56 (blueprint: def-sp-finite-free-direct-image-data). -/
structure CoefficientMap {Z W : Scheme.{u}} {q : Z ⟶ W} (R S : Coefficients q) where
  /-- Coefficient map on the target. -/
  target : R.target ⟶ S.target
  /-- Coefficient map on the source. -/
  source : R.source ⟶ S.source
  /-- The inverse-image identifications commute with coefficient change. -/
  comm : R.identification.hom ≫ source =
    (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map target ≫ S.identification.hom

/-- Identity coefficient map, keeping the given geometric identification.
Source: Stacks Tag 0B56 (blueprint: def-sp-finite-free-direct-image-data). -/
def CoefficientMap.id {Z W : Scheme.{u}} {q : Z ⟶ W} (R : Coefficients q) :
    CoefficientMap R R where
  target := 𝟙 _
  source := 𝟙 _
  comm := by simp

/-- Composition of compatible coefficient maps, using the same identifications.
Source: Stacks Tag 0D6D (blueprint: def-sp-finite-free-direct-image-data). -/
def CoefficientMap.comp {Z W : Scheme.{u}} {q : Z ⟶ W} {R S B : Coefficients q}
    (a : CoefficientMap R S) (b : CoefficientMap S B) : CoefficientMap R B where
  target := a.target ≫ b.target
  source := a.source ≫ b.source
  comm := by
    rw [← Category.assoc, a.comm, Category.assoc, b.comm, Functor.map_comp,
      Category.assoc]

/-- Canonical balancing, obtained by conjugating the actual normalized right adjoints.
The right-adjoint comparison is the published one fixed by its derived units and its
identity section maps. Scalar adjunctions have the `x ↦ 1 ⊗ x` normalization, so this
conjugate is exactly the balanced scalar/pullback comparison, including on flat K-flat
representatives. Its definition does not use the finite-free theorem below.
Source: Stacks Tags 03EL, 0D6D and 07A6
(blueprint: def-sp-finite-free-direct-image-data). -/
def balancing {Z W : Scheme.{u}} {q : Z ⟶ W} (sW : ScalarModel W) (sZ : ScalarModel Z)
    {R S : Coefficients q} (a : CoefficientMap R S) :
    (sW.presentation a.target).derived ⋙
        proEtaleRingDerivedPullback q S.target S.source S.identification ≅
      proEtaleRingDerivedPullback q R.target R.source R.identification ⋙
        (sZ.presentation a.source).derived :=
  ((conjugateIsoEquiv
      ((sW.adjunction a.target).comp
        (proEtaleRingDerivedAdjunction q S.target S.source S.identification))
      ((proEtaleRingDerivedAdjunction q R.target R.source R.identification).comp
        (sZ.adjunction a.source))).symm
    (proEtaleRingRestrictionDerivedDirectImage q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm)).symm

/-- The actual counit-tensor comparison in the larger coefficient derived category.
By the mate formula its component is the `Lq_S* ⊣ Rq_S*` adjunct of
`balancing.hom ≫ C_Z(ε_R)`. No scalar-forgetting functor is used to define the arrow.
Source: Stacks Tag 0B56 (blueprint: def-sp-finite-free-direct-image-data). -/
def comparison {Z W : Scheme.{u}} {q : Z ⟶ W} (sW : ScalarModel W) (sZ : ScalarModel Z)
    {R S : Coefficients q} (a : CoefficientMap R S) :
    proEtaleRingDerivedDirectImage q R.target R.source R.identification ⋙
        (sW.presentation a.target).derived ⟶
      (sZ.presentation a.source).derived ⋙
        proEtaleRingDerivedDirectImage q S.target S.source S.identification :=
  (mateEquiv
    (proEtaleRingDerivedAdjunction q R.target R.source R.identification)
    (proEtaleRingDerivedAdjunction q S.target S.source S.identification)
    (TwoSquare.mk _ _ _ _ (balancing sW sZ a).hom)).natTrans

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
