/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionData
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedAdjointLift
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedComparisonData
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.CategoryTheory.Ringed.RingedHomCompositionModel
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Homology.HomTensorSectionNaturality
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedTensorLift
import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientFlatModel
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.FiniteSiteInternalHomComparison
import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.SixFunctors.Etale.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.SixFunctors.Finite.FiniteConstructibleHom
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonUnit
import WeilConjectures.AlgebraicGeometry.Abelian.AbelianSheavesGModules
import WeilConjectures.AlgebraicGeometry.EtaleGlobalSectionsGaloisInvariants
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSequenceGlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Internal Hom and punctual representation on the coefficient sequence site

Source: the retained ordinary-system argument for the second paragraph of
`prop-coef-integral-exceptional-adjoint`; Zheng, Construction 4.1 and Lemma 4.10;
Stacks Project, Tags 08J9, 0D6E, 04JQ and 04JM
(blueprint: lem-coef-system-internal-hom-representability).

## Main definitions and statements

- `ComparisonImage`, `ComparisonTensor`: canonical sequence-site comparison presentations.
- `representingObject`, `representingEquiv`: punctual internal Hom and its Hom bijection.
- `SectionsComparison`, `mappingComparison`: the normalized derived abelian-tower map.
- `Representability`, `systemInternalHomRepresentability`: all the asserted properties.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
  WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective

attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.coefficientTowerSections
  WeilConjectures.coefficientSequenceRestriction
  CategoryTheory.Functor.rightDerivedFunctor
  Padic
attribute [-instance] WeilConjectures.coefficientSequenceEssentiallySmall

universe u c v r a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ d₁ d₂ d₃ d₄

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections

namespace WeilConjectures.SystemInternalHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The recorded finite coefficient rings, indexed by positive exponent n+1.
Source: coefficient extension, clause 4
(blueprint: lem-coef-system-internal-hom-representability). -/
abbrev coefficient (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))

/-- The actual adjacent quotient, with the canonical universe lift.
Source: coefficient extension, clause 4
(blueprint: lem-coef-system-internal-hom-representability). -/
def quotient (n : ℕ) : coefficient l E (n + 1) ⟶ coefficient l E n :=
  CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((Padic.coefficientExtensionTransition l E (n + 1)).comp ULift.ringEquiv.toRingHom))

/-- The strict tower of actual coefficient rings.
Source: Zheng Construction 4.1
(blueprint: lem-coef-system-internal-hom-representability). -/
def coefficients : ℕᵒᵖ ⥤ CommRingCat.{u + 1} := Functor.ofOpSequence (quotient l E)

/-- The existing ordinary etale sequence-site derived category.
Source: Zheng Construction 4.1
(blueprint: lem-coef-system-internal-hom-representability). -/
abbrev Et (W : Scheme.{u}) := Etale.SystemProjection.Derived W (coefficients l E)

section Sections

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C) (U : C)

/-- Sections at every coefficient index, with all horizontal arrows retained.
This forgets only scalar actions; its values and maps are the actual underlying
abelian presheaf at (n,U).
Source: Stacks 0941 (blueprint: lem-coef-system-internal-hom-representability). -/
def sectionsTower (R : Sheaf (coefficientSequenceTopology J) CommRingCat.{r}) :
    SemilinearSections.Mod.{c, v, r} (coefficientSequenceTopology J) R ⥤
      (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) :=
  SheafOfModules.toSheaf (ring (coefficientSequenceTopology J) R) ⋙
    sheafToPresheaf (coefficientSequenceTopology J) AddCommGrpCat.{r} ⋙
      (Functor.whiskeringLeft ℕᵒᵖ (ℕ × C)ᵒᵖ AddCommGrpCat.{r}).obj
        (Prod.sectL ℕ U).op

end Sections

/-- The sequence-site inclusion underlying nu_W, retaining the coefficient index.
Source: Stacks 099R and 0941
(blueprint: lem-coef-system-internal-hom-representability). -/
abbrev comparisonSite (W : Scheme.{u}) := (𝟭 ℕ).prod (Scheme.toProEt W)

/-- The canonical constant coefficient section on the pro-etale site.
Source: Stacks 03D7 (blueprint: lem-coef-system-internal-hom-representability). -/
def proConstant (W : Scheme.{u}) (n : ℕ) (U : W.ProEtᵒᵖ) :
    coefficient l E n → (coefficientSequenceCommRingSheaf.{u, u} l E W).obj.obj
      (op (n, U.unop)) :=
  letI : HasSheafify (Scheme.ProEt.topology W) CommRingCat.{u + 1} :=
    integralCoefficientRingSheafify.{u, u} W
  (toSheafify (Scheme.ProEt.topology W)
    ((Functor.const W.ProEtᵒᵖ).obj (coefficient l E n))).app U

/-- The actual structural map for nu on sequence sites, normalized on constant
coefficient generators. This determines the ring map before deriving anything.
Source: Stacks 099R, 03D7 (blueprint: lem-coef-system-internal-hom-representability). -/
structure ComparisonRing (W : Scheme.{u}) where
  [continuous : (comparisonSite W).IsContinuous
    (coefficientSequenceTopology W.smallEtaleTopology)
    (coefficientSequenceTopology (Scheme.ProEt.topology W))]
  structural : Etale.SystemProjection.rings W (coefficients l E) ⟶
    ((comparisonSite W).sheafPushforwardContinuous CommRingCat.{u + 1}
      (coefficientSequenceTopology W.smallEtaleTopology)
      (coefficientSequenceTopology (Scheme.ProEt.topology W))).obj
        (coefficientSequenceCommRingSheaf.{u, u} l E W)
  constants : ∀ (n : ℕ) (U : W.Etaleᵒᵖ) (b : coefficient l E n),
    (structural.hom.app (op (n, U.unop)))
      ((toSheafify (D := CommRingCat.{u + 1}) W.smallEtaleTopology ((Functor.const W.Etaleᵒᵖ).obj
        (coefficient l E n))).app U b) =
      proConstant l E W n ((Scheme.toProEt W).op.obj U) b

/-- Direct image along the specified ring map is the actual module pushforward.
Source: Stacks 03D7 (blueprint: lem-coef-system-internal-hom-representability). -/
def ComparisonRing.push {W : Scheme.{u}} (d : ComparisonRing l E W) :
    coefficientSequenceModules.{u, u} l E W ⥤
      Etale.SystemProjection.Modules W (coefficients l E) :=
  letI := d.continuous
  SheafOfModules.pushforward (F := comparisonSite W)
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map d.structural)

/-- The inverse image is the left adjoint to this concrete direct image; its
exactness is part of the conclusion, not an assumption on M or N.
Source: Stacks 099R, 06YY (blueprint: lem-coef-system-internal-hom-representability). -/
structure ComparisonImage (W : Scheme.{u}) extends ComparisonRing l E W where
  inverse : Etale.SystemProjection.Modules W (coefficients l E) ⥤
    coefficientSequenceModules.{u, u} l E W
  adjunction : inverse ⊣ toComparisonRing.push
  [inverseAdditive : inverse.Additive]
  [inverseLimits : PreservesFiniteLimits inverse]
  [inverseColimits : PreservesFiniteColimits inverse]
  [pushAdditive : toComparisonRing.push.Additive]
  [kinjectives : Abelian.HasKInjectiveResolutions (coefficientSequenceModules.{u, u} l E W)]

attribute [instance] ComparisonImage.inverseAdditive ComparisonImage.inverseLimits
  ComparisonImage.inverseColimits ComparisonImage.pushAdditive

/-- Exact localization of the actual sequence-site inverse image.
Source: Stacks 06YY (blueprint: lem-coef-system-internal-hom-representability). -/
def ComparisonImage.P {W : Scheme.{u}} (d : ComparisonImage l E W) :
    Et l E W ⥤ coefficientSequenceDerived.{u, u} l E W :=
  letI := d.inverseAdditive
  letI := d.inverseLimits
  letI := d.inverseColimits
  d.inverse.mapDerivedCategory

/-- Total unbounded derived pushforward on the sequence site itself.
Source: Stacks 079P (blueprint: lem-coef-system-internal-hom-representability). -/
def ComparisonImage.R {W : Scheme.{u}} (d : ComparisonImage l E W) :
    coefficientSequenceDerived.{u, u} l E W ⥤ Et l E W :=
  letI := d.pushAdditive
  letI := d.kinjectives
  d.toComparisonRing.push.rightDerivedFunctor

/-- Underlying abelian tower at the geometric point, by actual terminal sections.
Source: Stacks 04JQ, 04JM
(blueprint: lem-coef-system-internal-hom-representability). -/
abbrev pointSections (s : Scheme.{u}) :=
  sectionsTower s.smallEtaleTopology (⊤_ s.Etale)
    (Etale.SystemProjection.rings s (coefficients l E))

/-- Exactness of actual point sections; over Spec of an algebraically closed field
this follows from the abelian-sheaf/Galois-module equivalence. It is conclusion data.
Source: Stacks 04JQ, 04JM
(blueprint: lem-coef-system-internal-hom-representability). -/
structure PointSections (s : Scheme.{u}) where
  [limits : PreservesFiniteLimits (pointSections l E s)]
  [colimits : PreservesFiniteColimits (pointSections l E s)]



/-- Exact termwise localization of underlying point sections.
Source: Stacks 05RU (blueprint: lem-coef-system-internal-hom-representability). -/
def PointSections.derived {s : Scheme.{u}} (p : PointSections l E s) :
    Et l E s ⥤ DerivedCategory (ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  letI := p.limits
  letI := p.colimits
  (pointSections l E s).mapDerivedCategory

/-- Total termwise pro-etale sections, after exact restriction of coefficient actions.
This is the functor used in the dependency's definition of the mapping system.
Source: Stacks 0941, 0D6E
(blueprint: lem-coef-system-internal-hom-representability). -/
def proSections (W : Scheme.{u}) :
    coefficientSequenceDerived.{u, u} l E W ⥤
      DerivedCategory (ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  coefficientSequenceDerivedRestriction.{u, u} l E W ⋙
    (coefficientTowerSections.{u, u} l E W).rightDerivedFunctor

/-- The canonical full-complex unit for exact restriction followed by right derivation.
Source: Stacks 0D6E (blueprint: lem-coef-system-internal-hom-representability). -/
def exactThenRightUnit {A : Type a₁} {B : Type a₂} {C : Type a₃}
    [Category.{b₁} A] [Category.{b₂} B] [Category.{b₃} C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory.{d₁} A] [HasDerivedCategory.{d₂} B] [HasDerivedCategory.{d₃} C]
    [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : B ⥤ C) [G.Additive] (I : CochainComplex A ℤ) :
    DerivedCategory.Q.obj (((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj I) ⟶
      (F.mapDerivedCategory ⋙ G.rightDerivedFunctor).obj (DerivedCategory.Q.obj I) :=
  G.rightDerivedFunctorUnitQ ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
    G.rightDerivedFunctor.map (F.mapDerivedCategoryFactors.inv.app I)

/-- The canonical full-complex composition unit, ending with an exact functor.
Source: Stacks 0D6E (blueprint: lem-coef-system-internal-hom-representability). -/
def twoRightThenExactUnit {A : Type a₁} {B : Type a₂} {C : Type a₃} {D : Type a₄}
    [Category.{b₁} A] [Category.{b₂} B] [Category.{b₃} C] [Category.{b₄} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{d₁} A] [HasDerivedCategory.{d₂} B] [HasDerivedCategory.{d₃} C]
    [HasDerivedCategory.{d₄} D] [Abelian.HasKInjectiveResolutions A]
    [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]
    (H : C ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (I : CochainComplex A ℤ) :
    DerivedCategory.Q.obj (((F ⋙ G ⋙ H).mapHomologicalComplex (.up ℤ)).obj I) ⟶
      (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor ⋙ H.mapDerivedCategory).obj
        (DerivedCategory.Q.obj I) :=
  H.mapDerivedCategoryFactors.inv.app
      ((G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj I)) ≫
    H.mapDerivedCategory.map
      (G.rightDerivedFunctorUnitQ ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnitQ I))

/-- The actual derived unit for sections after exact coefficient restriction.
Source: Stacks 0D6E (blueprint: lem-coef-system-internal-hom-representability). -/
def proSectionsUnit (W : Scheme.{u})
    (I : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ) :
    DerivedCategory.Q.obj
      (((coefficientSequenceRestriction.{u, u} l E W ⋙
        coefficientTowerSections.{u, u} l E W).mapHomologicalComplex (.up ℤ)).obj I) ⟶
      (proSections l E W).obj (DerivedCategory.Q.obj I) :=
  letI := coefficientConstantTowersKInjectives.{u, u} l E W
  exactThenRightUnit (coefficientSequenceRestriction.{u, u} l E W)
    (coefficientTowerSections.{u, u} l E W) I

/-- Actual termwise composed sections of a whole system complex.
Source: Stacks 0D6E (blueprint: lem-coef-system-internal-hom-representability). -/
def composedSectionsComplex {W s : Scheme.{u}} {a : W ⟶ s}
    (c : ComparisonImage l E W) (d : Etale.SystemProjection.Image a (coefficients l E))
    (I : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ) :
    CochainComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℤ :=
  letI := c.pushAdditive
  letI := d.pushAdditive
  ((c.toComparisonRing.push ⋙ d.toDirectImage.push ⋙ pointSections l E s).mapHomologicalComplex
    (.up ℤ)).obj I

/-- The composed unit for actual nu-pushforward, structure-pushforward, and exact
point sections. This is formed on whole complexes, before coefficient evaluation.
Source: Stacks 0D6E (blueprint: lem-coef-system-internal-hom-representability). -/
def compositionUnit {W s : Scheme.{u}} {a : W ⟶ s}
    (c : ComparisonImage l E W) (d : Etale.SystemProjection.Image a (coefficients l E))
    (p : PointSections l E s)
    (I : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ) :
    DerivedCategory.Q.obj (composedSectionsComplex l E c d I) ⟶
      (c.R ⋙ d.R ⋙ p.derived).obj (DerivedCategory.Q.obj I) :=
  letI := c.pushAdditive
  letI := c.kinjectives
  letI := d.pushAdditive
  letI := d.kinjectives
  letI := p.limits
  letI := p.colimits
  twoRightThenExactUnit c.toComparisonRing.push d.toDirectImage.push (pointSections l E s) I

/-- Apply an ordinary sections comparison to a whole complex and localize.
Source: Stacks 0D6E (blueprint: lem-coef-system-internal-hom-representability). -/
def ordinarySectionsMap {W s : Scheme.{u}} {a : W ⟶ s}
    (c : ComparisonImage l E W) (d : Etale.SystemProjection.Image a (coefficients l E))
    (g : c.toComparisonRing.push ⋙ d.toDirectImage.push ⋙ pointSections l E s ≅
      coefficientSequenceRestriction.{u, u} l E W ⋙ coefficientTowerSections.{u, u} l E W)
    (I : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ) :
    DerivedCategory.Q.obj (composedSectionsComplex l E c d I) ⟶
      DerivedCategory.Q.obj
        (((coefficientSequenceRestriction.{u, u} l E W ⋙
          coefficientTowerSections.{u, u} l E W).mapHomologicalComplex (.up ℤ)).obj I) :=
  letI := c.pushAdditive
  letI := d.pushAdditive
  DerivedCategory.Q.map ((NatIso.mapHomologicalComplex g (.up ℤ)).hom.app I)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual base change of the terminal etale object, viewed on the pro-etale site.
Source: Stacks 03Q2 (blueprint: lem-coef-system-internal-hom-representability). -/
def structureSectionObject {W s : Scheme.{u}} (a : W ⟶ s) : W.ProEt :=
  (Scheme.toProEt W).obj
    ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ a).obj (⊤_ s.Etale))

/-- Evaluate the actual termwise module-Hom section on the coefficient unit.
Source: Stacks 0941 (blueprint: lem-coef-system-internal-hom-representability). -/
def towerSectionValue (W : Scheme.{u}) (N : coefficientSequenceModules.{u, u} l E W)
    (n : ℕ)
    (z : (((coefficientSequenceRestriction.{u, u} l E W ⋙
      coefficientTowerSections.{u, u} l E W).obj N).obj (op n))) (U : W.ProEtᵒᵖ) :=
  ((@id (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E W) ⟶
      ((coefficientSequenceRestriction.{u, u} l E W).obj N).obj (op n))
        (by unfold coefficientTowerSections at z; exact z)).val.app U)
    (1 : (completedIntegralCoefficientSheafUnrestricted.{u, u} l E W).obj.obj U)

/-- Normalize a derived sections comparison by its full-complex unit word.
Source: Stacks 0D6E (blueprint: lem-coef-system-internal-hom-representability). -/
def SectionsUnit {W s : Scheme.{u}} {a : W ⟶ s}
    (c : ComparisonImage l E W) (d : Etale.SystemProjection.Image a (coefficients l E))
    (p : PointSections l E s)
    (g : c.toComparisonRing.push ⋙ d.toDirectImage.push ⋙ pointSections l E s ≅
      coefficientSequenceRestriction.{u, u} l E W ⋙ coefficientTowerSections.{u, u} l E W)
    (γ : c.R ⋙ d.R ⋙ p.derived ≅ proSections l E W) : Prop :=
  ∀ I : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ,
    compositionUnit l E c d p I ≫ γ.hom.app (DerivedCategory.Q.obj I) =
      ordinarySectionsMap l E c d g I ≫ proSectionsUnit l E W I

/-- Canonical pushforward-composition and scalar-forgetting comparison. The ordinary
map is normalized by evaluating its resulting module homomorphism on 1; the derived
map is normalized by the full composed derived unit. Neither can be freely chosen.
Source: Stacks 0D6E, 0941 (blueprint: lem-coef-system-internal-hom-representability). -/
structure SectionsComparison {W s : Scheme.{u}} {a : W ⟶ s}
    (c : ComparisonImage l E W) (d : Etale.SystemProjection.Image a (coefficients l E))
    (p : PointSections l E s) where
  ordinary : c.toComparisonRing.push ⋙ d.toDirectImage.push ⋙ pointSections l E s ≅
    coefficientSequenceRestriction.{u, u} l E W ⋙ coefficientTowerSections.{u, u} l E W
  sections : ∀ (N : coefficientSequenceModules.{u, u} l E W) (n : ℕ)
    (x : ((pointSections l E s).obj (d.toDirectImage.push.obj
      (c.toComparisonRing.push.obj N))).obj (op n)),
    HEq (towerSectionValue l E W N n (((ordinary.hom.app N).app (op n)) x)
      (op (structureSectionObject a))) x
  derived : c.R ⋙ d.R ⋙ p.derived ≅ proSections l E W
  unit : SectionsUnit l E c d p ordinary derived

end WeilConjectures.SystemInternalHom
