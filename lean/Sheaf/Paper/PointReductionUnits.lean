/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.Paper.PointSectionsDerivedReduction
public import Sheaf.Paper.PointSectionsFiniteReduction
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.Paper.AdicCoefficientDatum

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Canonical coefficient-reduction units at a geometric point

Source: Stacks Project, sites-cohomology.tex Tag 07A6 and derived.tex Tags 0FND and 09T5
(blueprint: def-trf-point-reduction-units).

## Main definitions

* `pointUnitIntegralModuleUnit`, `pointUnitIntegralSheafUnit`: the integral quotient units.
* `pointUnitFiniteModuleUnit`, `pointUnitFiniteSheafUnit`: the finite quotient units.
* `pointUnitIntegralDerivedSectionsRestrictionIso` and
  `pointUnitFiniteDerivedSectionsRestrictionIso`: the exact restriction/sections identity.

The named existence theorems fix each unit on actual tensor representatives, so their
choices determine the units uniquely. The section comparisons are the identity on elements.
The integral index n denotes exponent n+1; finite indices denote exponents.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary restriction along the integral quotient, in the existing coefficient lift.
Source: Stacks 07A6 (blueprint: def-trf-point-reduction-units). -/
abbrev pointUnitIntegralRestriction (n : ℕ) :=
  ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (pointReductionQuotient l E n)

/-- The fixed derived restriction on integral section modules.
Source: Stacks 07A6 (blueprint: def-trf-point-reduction-units). -/
def pointUnitIntegralDerivedRestriction (n : ℕ) :=
  (pointUnitIntegralRestriction l E n).mapDerivedCategory.{u + 2, u + 2}

/-- The quotient coefficient complex used by the existing module tensor functor.
Source: Stacks 06Y6 (blueprint: def-trf-point-reduction-units). -/
abbrev pointUnitIntegralCoefficient (n : ℕ) :=
  (HomologicalComplex.single _ (.up ℤ) 0).obj
    (ModuleCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))

/-- The mixed total tensor computing the published integral quotient functor.
Source: Stacks 06Y6 (blueprint: def-trf-point-reduction-units). -/
def pointUnitIntegralComplexTensor (n : ℕ) :=
  (((ModuleCat.mixedTensor (pointReductionQuotient l E n)).flip
    ).map₂CochainComplex).flip.obj (pointUnitIntegralCoefficient l E n)

/-- The universal computation map, retaining the published derived tensor choice.
Source: Stacks 06Y6 (blueprint: def-trf-point-reduction-units). -/
def pointUnitIntegralModuleCounit (n : ℕ) :
    DerivedCategory.Q ⋙ pointReductionModuleTensor l E n ⟶
      pointUnitIntegralComplexTensor l E n ⋙ DerivedCategory.Q :=
  (DerivedCategory.exists_derivedTensor_second_factor_functor
    (pointReductionQuotient l E n)).2.choose_spec.choose (pointUnitIntegralCoefficient l E n)

/-- The element 1 tensor (1 tensor x) in the degree-a summand of the actual total tensor.
Source: Stacks 06Y6 (blueprint: def-trf-point-reduction-units). -/
def pointUnitIntegralTensorGenerator (n : ℕ)
    (C : CochainComplex (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ)
    (a : ℤ) (b c : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
    (x : C.X a) : ((pointUnitIntegralComplexTensor l E n).obj C).X a :=
  (HomologicalComplex.ιMapBifunctorOrZero C (pointUnitIntegralCoefficient l E n)
    (ModuleCat.mixedTensor (pointReductionQuotient l E n)).flip (.up ℤ) a 0 a)
      (b ⊗ₜ (c ⊗ₜ[_, pointReductionQuotient l E n] x))

/-- The scalar-extension adjunction on section modules has its actual tensor unit.
Source: Stacks 07A6, 0FND, 09T5 (blueprint: def-trf-point-reduction-units).
Proof: the mixed tensor with the regular coefficient module in degree zero is ordinary
extension of scalars. Derive its ordinary tensor/restriction adjunction, whose unit sends
x to 1 tensor x. Identify the left derived functor by its universal computation map and
exact restriction by its localization comparison. On every K-flat complex this gives
the displayed equation, which fixes the unit on all derived objects. -/
theorem pointUnitIntegralModuleAdjunction (n : ℕ) :
    ∃ b : pointReductionModuleTensor l E n ⊣ pointUnitIntegralDerivedRestriction l E n,
      ∀ C : CochainComplex (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ,
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C →
        ∃ g : C ⟶ ((pointUnitIntegralRestriction l E n).mapHomologicalComplex (.up ℤ)).obj
            ((pointUnitIntegralComplexTensor l E n).obj C),
          (∀ (a : ℤ) (x : C.X a), g.f a x = pointUnitIntegralTensorGenerator l E n C a 1 1 x) ∧
          b.unit.app (DerivedCategory.Q.obj C) ≫
              (pointUnitIntegralDerivedRestriction l E n).map
                ((pointUnitIntegralModuleCounit l E n).app C) ≫
              (pointUnitIntegralRestriction l E n).mapDerivedCategoryFactors.hom.app
                ((pointUnitIntegralComplexTensor l E n).obj C) = DerivedCategory.Q.map g := by
  sorry

/-- Sections and actual integral coefficient restriction agree by the identity on elements.
Source: Stacks 07A6 (blueprint: def-trf-point-reduction-units).
Proof: restriction changes only the scalar action. The constant-to-completion map followed
by the limit projection is the constant quotient map. Thus both actions agree; the identity
on each section module gives a natural linear isomorphism, uniquely fixed on elements. -/
theorem pointUnitIntegralSectionsRestriction (n : ℕ) :
    ∃! e : scalarReductionRestriction l E (Spec (.of D.k)) n ⋙ pointIntegralSections l E D.k ≅
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
          pointUnitIntegralRestriction l E n,
      ∀ (M : scalarReductionTarget l E (Spec (.of D.k)) n)
        (x : (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).obj M),
        e.hom.app M x = x := by
  sorry

/-- Canonical identity-on-sections comparison before deriving.
Source: Stacks 07A6 (blueprint: def-trf-point-reduction-units). -/
def pointUnitIntegralSectionsRestrictionIso (n : ℕ) :=
  (pointUnitIntegralSectionsRestriction D l E n).exists.choose

/-- The exact identity-on-sections comparison transported through localization.
Source: Stacks 07A6, 09T5 (blueprint: def-trf-point-reduction-units). -/
def pointUnitIntegralDerivedSectionsRestrictionIso (n : ℕ) :
    scalarReductionDerivedRestriction l E (Spec (.of D.k)) n ⋙
        (pointIntegralSections l E D.k).mapDerivedCategory ≅
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory ⋙
        pointUnitIntegralDerivedRestriction l E n :=
  letI : (pointUnitIntegralRestriction l E n).Additive :=
    inferInstanceAs ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (pointReductionQuotient l E n)).Additive)
  letI : (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).Additive :=
    pointFiniteSectionsAdditive _ _
  letI : (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
      pointUnitIntegralRestriction l E n).Additive := inferInstance
  letI : PreservesFiniteLimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        pointUnitIntegralRestriction l E n) := comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        pointUnitIntegralRestriction l E n) := comp_preservesFiniteColimits _ _
  letI : PreservesFiniteLimits
      (scalarReductionRestriction l E (Spec (.of D.k)) n ⋙ pointIntegralSections l E D.k) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (scalarReductionRestriction l E (Spec (.of D.k)) n ⋙ pointIntegralSections l E D.k) :=
    comp_preservesFiniteColimits _ _
  (Functor.mapDerivedCategoryCompIso
    (scalarReductionRestriction l E (Spec (.of D.k)) n)
    (pointIntegralSections l E D.k)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pointUnitIntegralSectionsRestrictionIso D l E n) ≪≫
    Functor.mapDerivedCategoryCompIso
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
      (pointUnitIntegralRestriction l E n)

/-- Actual sheaf restriction for a pair of finite quotients.
Source: Stacks 07A6 (blueprint: def-trf-point-reduction-units). -/
abbrev pointUnitFiniteRestriction (n j : ℕ) (h : j ≤ n) :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology (Spec (.of D.k)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (pointFiniteReductionSheafMap D.k l E n j h))

/-- Restriction keeps the same kernels.
Source: Stacks 03DA (blueprint: def-trf-point-reduction-units). -/
instance pointUnitFiniteRestrictionLimits (n j : ℕ) (h : j ≤ n) :
    PreservesFiniteLimits (pointUnitFiniteRestriction D l E n j h) :=
  (SheafOfModules.sheafRingDerivedCoefficientAdjunction
    (pointFiniteReductionSheafMap D.k l E n j h)).choose

/-- Restriction keeps the same cokernels.
Source: Stacks 03DA (blueprint: def-trf-point-reduction-units). -/
instance pointUnitFiniteRestrictionColimits (n j : ℕ) (h : j ≤ n) :
    PreservesFiniteColimits (pointUnitFiniteRestriction D l E n j h) :=
  (SheafOfModules.sheafRingDerivedCoefficientAdjunction
    (pointFiniteReductionSheafMap D.k l E n j h)).choose_spec.choose

/-- Derived restriction using the existing standard localization of module sheaves.
Source: Stacks 07A6 (blueprint: def-trf-point-reduction-units). -/
def pointUnitFiniteDerivedRestriction (n j : ℕ) (h : j ≤ n) :=
  (pointUnitFiniteRestriction D l E n j h).mapDerivedCategory.{u + 2, u + 2}

/-- Ordinary restriction of the actual finite quotient ring map.
Source: Stacks 07A6 (blueprint: def-trf-point-reduction-units). -/
abbrev pointUnitFiniteModuleRestriction (n j : ℕ) (h : j ≤ n) :=
  ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (pointFiniteReductionRingMap l E n j h)

/-- Derived module restriction with the small Grothendieck localization already used
by finite point sections, rather than the larger integral-module localization.
Source: Stacks 07A6 (blueprint: def-trf-point-reduction-units). -/
def pointUnitFiniteDerivedModuleRestriction (n j : ℕ) (h : j ≤ n) :=
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (pointFiniteReductionModules l E j)
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (pointFiniteReductionModules l E n)
  (pointUnitFiniteModuleRestriction l E n j h).mapDerivedCategory

/-- Localization of finite ordinary-module complexes with the published small Hom universe.
Source: Stacks 05RU (blueprint: def-trf-point-reduction-units). -/
def pointUnitFiniteQ (n : ℕ) :=
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (pointFiniteReductionModules l E n)
  DerivedCategory.Q (C := pointFiniteReductionModules l E n)

/-- The fixed exact-restriction factorization in that same localization.
Source: Stacks 09T5 (blueprint: def-trf-point-reduction-units). -/
def pointUnitFiniteModuleFactors (n j : ℕ) (h : j ≤ n) :=
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (pointFiniteReductionModules l E j)
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (pointFiniteReductionModules l E n)
  (pointUnitFiniteModuleRestriction l E n j h).mapDerivedCategoryFactors

/-- The ordinary-module quotient adjunction, with its canonical tensor unit.
Source: Stacks 07A6, 09T5 (blueprint: def-trf-point-reduction-units).
Proof: derive ordinary tensor/restriction along the actual quotient map, then identify
its left adjoint using the universal mixed-tensor computation with the regular module
in degree zero. Exact restriction descends termwise. The ordinary unit is 1 tensor x;
its derived representative is the displayed map. The normalization fixes the unit on
every K-flat representative and hence on every derived object. -/
theorem pointUnitFiniteModuleAdjunction (n j : ℕ) (h : j ≤ n) :
    ∃ b : pointFiniteReductionModuleTensor l E n j h ⊣
        pointUnitFiniteDerivedModuleRestriction l E n j h,
      ∀ C : CochainComplex (pointFiniteReductionModules l E n) ℤ,
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C →
        ∃ g : C ⟶ ((pointUnitFiniteModuleRestriction l E n j h
            ).mapHomologicalComplex (.up ℤ)).obj
              ((pointFiniteReductionComplexTensor l E n j h).obj C),
          (∀ (a : ℤ) (x : C.X a),
            g.f a x = pointFiniteReductionTensorGenerator l E n j h C a 1 1 x) ∧
          b.unit.app ((pointUnitFiniteQ l E n).obj C) ≫
              (pointUnitFiniteDerivedModuleRestriction l E n j h).map
                ((pointFiniteReductionModuleCounit l E n j h).app C) ≫
              (pointUnitFiniteModuleFactors l E n j h).hom.app
                ((pointFiniteReductionComplexTensor l E n j h).obj C) =
            (pointUnitFiniteQ l E n).map g := by
  sorry

/-- Finite sheaf reduction uses the actual normalized tensor/restriction adjunction.
Source: Stacks 07A6, 0FND, 09T5 (blueprint: def-trf-point-reduction-units).
Proof: apply the normalized ring-sheaf coefficient adjunction to the fixed ordinary
extension functor and its universal derived pair. Its ordinary unit is sheafification
of 1 tensor x at every object of the site. On a flat-term K-flat complex its derived
unit is the localization of that ordinary unit followed by the inverse universal
computation map and the inverse exact-restriction factorization. This determines it
independently of representatives, with no flatness assumption on the quotient map. -/
theorem pointUnitFiniteSheafAdjunction (n j : ℕ) (h : j ≤ n) :
    ∃ a₀ : pointFiniteReductionSheafExtension D.k l E n j h ⊣
        pointUnitFiniteRestriction D l E n j h,
      (∀ (M : pointFiniteReductionSheaves D.k l E n)
        (U : (Scheme.ProEt (Spec (.of D.k)))ᵒᵖ) (x : M.val.obj U),
        (eqToHom ((pointFiniteReductionSheafExistence D.k l E n j h
          ).choose_spec.choose M)).val.app U ((a₀.unit.app M).val.app U x) =
          (toSheafify (ProEt.topology (Spec (.of D.k)))
            (SheafOfModules.changeOfRingsPresheaf
              (pointFiniteReductionSheafMap D.k l E n j h) M).presheaf).app U
                ((1 : (pointFiniteReductionRingSheaf D.k l E j).obj.obj U)
                  ⊗ₜ[(pointFiniteReductionRingSheaf D.k l E n).obj.obj U,
                    ((pointFiniteReductionSheafMap D.k l E n j h).hom.app U).hom] x)) ∧
      ∃ a : pointFiniteReductionSheafTensor D.k l E n j h ⊣
          pointUnitFiniteDerivedRestriction D l E n j h,
        ∀ P : CochainComplex (pointFiniteReductionSheaves D.k l E n) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients
            (J := ProEt.topology (Spec (.of D.k)))
            (R := pointFiniteReductionRingSheaf D.k l E n) P →
          (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
            (R := pointFiniteReductionRingSheaf D.k l E n) (P.X i)) →
          a.unit.app (DerivedCategory.Q.obj P) ≫
              (pointUnitFiniteDerivedRestriction D l E n j h).map
                (pointFiniteReductionSheafCounit D.k l E n j h P) ≫
              (pointUnitFiniteRestriction D l E n j h).mapDerivedCategoryFactors.hom.app
                ((pointFiniteReductionSheafComplexTensor D.k l E n j h).obj P) =
            DerivedCategory.Q.map ((a₀.mapHomologicalComplex (.up ℤ)).unit.app P) := by
  sorry

/-- The unique identity-on-sections comparison for a finite quotient.
Source: Stacks 07A6 (blueprint: def-trf-point-reduction-units).
Proof: the quotient map of constant sheaves commutes with their constant section maps.
Thus sections with restricted scalar action are the identical ordinary modules on
both sides. The identity is linear and natural, and its value on each element makes
the natural isomorphism unique. -/
theorem pointUnitFiniteSectionsRestriction (n j : ℕ) (h : j ≤ n) :
    ∃! e : pointUnitFiniteRestriction D l E n j h ⋙
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E n) ≅
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E j) ⋙
          pointUnitFiniteModuleRestriction l E n j h,
      ∀ (M : pointFiniteReductionSheaves D.k l E j)
        (x : (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j)).obj M),
        e.hom.app M x = x := by
  sorry

/-- The unique ordinary finite restriction/sections identification.
Source: Stacks 07A6 (blueprint: def-trf-point-reduction-units). -/
def pointUnitFiniteSectionsRestrictionIso (n j : ℕ) (h : j ≤ n) :=
  (pointUnitFiniteSectionsRestriction D l E n j h).exists.choose

/-- The same identity-on-sections comparison, descended through the fixed localizations.
Source: Stacks 07A6, 09T5 (blueprint: def-trf-point-reduction-units). -/
def pointUnitFiniteDerivedSectionsRestrictionIso (n j : ℕ) (h : j ≤ n) :
    pointUnitFiniteDerivedRestriction D l E n j h ⋙
        pointFiniteReductionSections D.k l E n ≅
      pointFiniteReductionSections D.k l E j ⋙
        pointUnitFiniteDerivedModuleRestriction l E n j h :=
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (pointFiniteReductionModules l E j)
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (pointFiniteReductionModules l E n)
  letI : (pointUnitFiniteModuleRestriction l E n j h).Additive :=
    inferInstanceAs ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (pointFiniteReductionRingMap l E n j h)).Additive)
  letI : (pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)).Additive :=
    pointFiniteSectionsAdditive _ _
  letI : (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j)).Additive :=
    pointFiniteSectionsAdditive _ _
  letI : PreservesFiniteLimits
      (pointUnitFiniteRestriction D l E n j h ⋙
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (pointUnitFiniteRestriction D l E n j h ⋙
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) :=
    comp_preservesFiniteColimits _ _
  letI : PreservesFiniteLimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j) ⋙
        pointUnitFiniteModuleRestriction l E n j h) := comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j) ⋙
        pointUnitFiniteModuleRestriction l E n j h) := comp_preservesFiniteColimits _ _
  (Functor.mapDerivedCategoryCompIso (pointUnitFiniteRestriction D l E n j h)
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E n))).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pointUnitFiniteSectionsRestrictionIso D l E n j h) ≪≫
    Functor.mapDerivedCategoryCompIso
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j))
      (pointUnitFiniteModuleRestriction l E n j h)

/-- The actual integral module scalar-extension unit, fixed on tensor representatives.
Source: Stacks 07A6, 09T5 (blueprint: def-trf-point-reduction-units). -/
def pointUnitIntegralModuleUnit (n : ℕ) :
    𝟭 _ ⟶ pointReductionModuleTensor l E n ⋙ pointUnitIntegralDerivedRestriction l E n :=
  (pointUnitIntegralModuleAdjunction l E n).choose.unit

/-- The actual integral sheaf scalar-extension unit from the published adjunction.
Source: Stacks 07A6, 09T5 (blueprint: def-trf-point-reduction-units). -/
def pointUnitIntegralSheafUnit (n : ℕ) :
    𝟭 _ ⟶ scalarReductionDerivedExtension l E (Spec (.of D.k)) n ⋙
      scalarReductionDerivedRestriction l E (Spec (.of D.k)) n :=
  (derivedScalarExtensionRestrictionAdjunction l E (Spec (.of D.k)) n).choose.unit

/-- The actual finite module scalar-extension unit, fixed on tensor representatives.
Source: Stacks 07A6, 09T5 (blueprint: def-trf-point-reduction-units). -/
def pointUnitFiniteModuleUnit (n j : ℕ) (h : j ≤ n) :
    𝟭 _ ⟶ pointFiniteReductionModuleTensor l E n j h ⋙
      pointUnitFiniteDerivedModuleRestriction l E n j h :=
  (pointUnitFiniteModuleAdjunction l E n j h).choose.unit

/-- The actual finite sheaf scalar-extension unit, with ordinary and derived normalization.
Source: Stacks 07A6, 09T5 (blueprint: def-trf-point-reduction-units). -/
def pointUnitFiniteSheafUnit (n j : ℕ) (h : j ≤ n) :
    𝟭 _ ⟶ pointFiniteReductionSheafTensor D.k l E n j h ⋙
      pointUnitFiniteDerivedRestriction D l E n j h :=
  (pointUnitFiniteSheafAdjunction D l E n j h).choose_spec.2.choose.unit

end WeilConjectures
