module

public import Sheaf.Paper.EtaleSystemProjectionData
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.Paper.CoefficientSystemDerivedComparison
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Paper.RingedPullbackHomEvaluationComparison
import Sheaf.Paper.ConstructibleHomComparison
import Sheaf.Paper.FiniteConstructibleHom
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import WeilConjectures.AlgebraicGeometry.EtaleGlobalSectionsGaloisInvariants
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.CoefficientSequenceGlobalSections
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
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

/-- The unchanged pro-etale site is small in its natural object universe.
Source: Stacks 098K (blueprint: lem-coef-system-internal-hom-representability). -/
instance (priority := 4000) proSiteSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _

/-- The sequence index does not enlarge the natural site universe.
Source: Stacks 0941 (blueprint: lem-coef-system-internal-hom-representability). -/
instance (priority := 4000) sequenceSiteSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} (ℕ × W.ProEt) := essentiallySmallSelf.{0, u, u + 1} _

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

/-- The existing sequence-site internal Hom on the ordinary etale site.
Source: Stacks 08J9 (blueprint: lem-coef-system-internal-hom-representability). -/
abbrev etHom (W : Scheme.{u}) :=
  internalHom.{u + 1, u, u + 1} (coefficientSequenceTopology W.smallEtaleTopology)
    (Etale.SystemProjection.rings W (coefficients l E))

/-- The ordinary semilinear calculus, specialized to the actual etale coefficients.
Source: Zheng Lemma 4.10
(blueprint: lem-coef-system-internal-hom-representability). -/
abbrev EtData (W : Scheme.{u}) :=
  Data.{u + 1, u, u} W.smallEtaleTopology
    (Etale.SystemProjection.coefficients W (coefficients l E))
    (Etale.SystemProjection.transitions W (coefficients l E))

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

/-- Sections on towers preserve addition componentwise.
Source: Stacks 0941 (blueprint: lem-coef-system-internal-hom-representability). -/
instance sectionsTowerAdditive {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (U : C)
    (R : Sheaf (coefficientSequenceTopology J) CommRingCat.{r}) :
    (sectionsTower J U R).Additive := by
  unfold sectionsTower
  infer_instance

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

/-- The canonical localized adjunction, with its actual unit and counit.
Source: Stacks 06YY (blueprint: lem-coef-system-internal-hom-representability). -/
def ComparisonImage.derivedAdjunction {W : Scheme.{u}} (d : ComparisonImage l E W) :
    d.P ⊣ d.R :=
  letI := d.inverseAdditive
  letI := d.inverseLimits
  letI := d.inverseColimits
  letI := d.pushAdditive
  letI := d.kinjectives
  d.adjunction.mapDerivedCategoryRightDerivedAdjunction

/-- The canonical tensor comparison for nu: its ordinary adjunct sends a pure tensor
to the tensor of the two actual adjunction units, and its derived map is fixed on
K-flat total complexes. Thus a scalar-twisted tensor comparison is excluded.
Source: Stacks 03EL, 07A4 (blueprint: lem-coef-system-internal-hom-representability). -/
structure ComparisonTensor (W : Scheme.{u}) (A : EtData l E W)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W) (d : ComparisonImage l E W) where
  tensor : A.closed.tensor ⋙ d.P ≅ (d.P.prod d.P) ⋙ S.systemClosed.tensor
  model : TensorComparisonModel.{u + 1, u, u}
    (coefficientSequenceTopology W.smallEtaleTopology)
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (Etale.SystemProjection.rings W (coefficients l E))
    (coefficientSequenceCommRingSheaf.{u, u} l E W) d.inverse A.closed S.systemClosed
    A.tensorModels S.systemTensorModel tensor
  pure : ∀ (M N : Etale.SystemProjection.Modules W (coefficients l E))
    (n : ℕ) (U : W.Etaleᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) (y : N.val.obj (op (n, U.unop))),
    HEq ((((d.adjunction.homEquiv _ _) (model.ordinary M N).hom).val.app
      (op (n, U.unop)))
        (tensorSection.{u + 1, u, u} (coefficientSequenceTopology W.smallEtaleTopology)
          (Etale.SystemProjection.rings W (coefficients l E)) M N (op (n, U.unop)) x y))
      (tensorSection.{u + 1, u, u} (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf.{u, u} l E W) (d.inverse.obj M) (d.inverse.obj N)
        (op (n, (Scheme.toProEt W).obj U.unop))
        (((d.adjunction.unit.app M).val.app (op (n, U.unop))) x)
        (((d.adjunction.unit.app N).val.app (op (n, U.unop))) y))

/-- Pullback-Hom comparison: precisely the closed transpose of pulled-back evaluation.
Source: Stacks 08J9 (blueprint: lem-coef-system-internal-hom-representability). -/
def pullHom {W : Scheme.{u}} {A : EtData l E W}
    {S : CoefficientDerivedSystemCalculus.{u, u} l E W} {d : ComparisonImage l E W}
    (t : ComparisonTensor l E W A S d) (M N : Et l E W) :=
  coefficientBaseChangeHom A.closed S.systemClosed d.P t.tensor M N

/-- Punctual representing object, using the actual structure-morphism direct image.
Source: Stacks 08J9 (blueprint: lem-coef-system-internal-hom-representability). -/
def representingObject {W s : Scheme.{u}} {a : W ⟶ s}
    (d : Etale.SystemProjection.Image a (coefficients l E)) (M N : Et l E W) :=
  d.R.obj ((etHom l E W).obj (op M, N))

/-- The representing Hom bijection is the two adjunctions in the stated order.
There are no normalization, constructibility or boundedness assumptions.
Source: Stacks 08J9 (blueprint: lem-coef-system-internal-hom-representability). -/
def representingEquiv {W s : Scheme.{u}} {a : W ⟶ s}
    (d : Etale.SystemProjection.Image a (coefficients l E)) (A : EtData l E W)
    (M N : Et l E W) (P : Et l E s) :
    (P ⟶ representingObject l E d M N) ≃ (A.closed.tensor.obj (d.P.obj P, M) ⟶ N) :=
  ((d.derivedAdjunction.homEquiv P ((etHom l E W).obj (op M, N))).symm).trans
    (A.closed.transpose (d.P.obj P) M N).symm


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

/-- The canonical underlying-tower comparison: the system unit, followed by the
pushforward of the evaluation-defined Hom comparison, then canonical composition.
Source: retained ordinary-system proof, steps 4--6; Stacks 0D6E
(blueprint: lem-coef-system-internal-hom-representability). -/
def mappingComparison {W s : Scheme.{u}} {a : W ⟶ s}
    {A : EtData l E W} {S : CoefficientDerivedSystemCalculus.{u, u} l E W}
    {c : ComparisonImage l E W} (t : ComparisonTensor l E W A S c)
    (d : Etale.SystemProjection.Image a (coefficients l E)) (p : PointSections l E s)
    (g : SectionsComparison l E c d p) (M N : Et l E W) :
    p.derived.obj (representingObject l E d M N) ⟶
      (coefficientSequenceGlobalHom.{u, u} l E W).obj (op (c.P.obj M), c.P.obj N) :=
  p.derived.map (d.R.map
    (c.derivedAdjunction.unit.app ((etHom l E W).obj (op M, N)) ≫
      c.R.map (pullHom l E t M N))) ≫
    g.derived.hom.app
      ((coefficientSequenceInternalHom.{u, u} l E W).obj (op (c.P.obj M), c.P.obj N))

/-- Closed transpose of the existing fiberwise system's actual evaluation. The
fiberwise-system dependency already realizes I as sequence-site internal Hom.
Source: retained ordinary-system proof, step 1
(blueprint: lem-coef-system-internal-hom-representability). -/
def fiberComparison (W : Scheme.{u}) (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (M N : coefficientSequenceDerived.{u, u} l E W) :=
  S.systemClosed.transpose _ M N (S.systemClosed.evaluation M N)

/-- Normalization of an etale system by the actual transition adjuncts.
Source: Zheng Construction 4.1
(blueprint: lem-coef-system-internal-hom-representability). -/
abbrev EtNormalized {W : Scheme.{u}} (A : EtData l E W) (M : Et l E W) :=
  Normalized W.smallEtaleTopology
    (Etale.SystemProjection.coefficients W (coefficients l E))
    (Etale.SystemProjection.transitions W (coefficients l E)) A.scalar M

/-- Levelwise finite-Tor bounded constructibility, with separate bounds at each level.
Source: the finite-torsion and finite-Tor conventions
(blueprint: lem-coef-system-internal-hom-representability). -/
def EtFinite (W : Scheme.{u})
    (ev : ∀ n : ℕ, Etale.SystemProjection.Evaluation W (coefficients l E) n)
    (M : Et l E W) : Prop :=
  ∀ n : ℕ, finiteTorConstructibleEtale l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) W
    ((ev n).E.obj M)

/-- The claimed comparisons and representability, in the ordinary unbounded categories.
All comparison presentations here are conclusion data. The geometric functors use
actual sheaf pushforwards, and the maps are fixed by their units and evaluations.
Source: retained ordinary-system proof, steps 1--6; Zheng Lemma 4.10
(blueprint: lem-coef-system-internal-hom-representability). -/
structure Representability {W s : Scheme.{u}} (a : W ⟶ s) where
  etale : EtData l E W
  proetale : Data.{u + 1, u, u} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf.{u, u} l E W)
    (coefficientSequenceCommRingTransition.{u, u} l E W)
  system : CoefficientDerivedSystemCalculus.{u, u} l E W
  comparison : ComparisonImage l E W
  tensor : ComparisonTensor l E W etale system comparison
  structureImage : Etale.SystemProjection.Image a (coefficients l E)
  point : PointSections l E s
  sections : SectionsComparison l E comparison structureImage point
  levels : ∀ n : ℕ, Etale.SystemProjection.Evaluation W (coefficients l E) n
  pro_normalization : ∀ M : coefficientSequenceDerived.{u, u} l E W,
    Normalized (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf.{u, u} l E W)
      (coefficientSequenceCommRingTransition.{u, u} l E W) proetale.scalar M ↔
        IsNormalizedCoefficientSequence.{u, u} l E W M
  pull_normalized : ∀ M : Et l E W, EtNormalized l E etale M →
    IsNormalizedCoefficientSequence.{u, u} l E W (comparison.P.obj M)
  transpose : ∀ (T M N : Et l E W) (g : etale.closed.tensor.obj (T, M) ⟶ N),
    comparison.P.map (etale.closed.transpose T M N g) ≫ pullHom l E tensor M N =
      system.systemClosed.transpose (comparison.P.obj T) (comparison.P.obj M)
        (comparison.P.obj N) (tensor.tensor.inv.app (T, M) ≫ comparison.P.map g)
  fiber_iso : ∀ (M N : coefficientSequenceDerived.{u, u} l E W),
    IsNormalizedCoefficientSequence.{u, u} l E W M →
    IsNormalizedCoefficientSequence.{u, u} l E W N →
      IsIso (fiberComparison l E W system M N)
  /-- Under the fiber identification of I and the semilinear-sections identification
  of sequence-site internal Hom, the evaluated comparison is the identity. -/
  fiber_identity : ∀ (M N : coefficientSequenceDerived.{u, u} l E W)
    (hM : IsNormalizedCoefficientSequence.{u, u} l E W M)
    (hN : IsNormalizedCoefficientSequence.{u, u} l E W N) (n : ℕ),
    (system.fiberHom M N hM hN n).inv ≫
      (coefficientSequenceDerivedEvaluation.{u, u} l E W n).map
        (fiberComparison l E W system M N) ≫
          (proetale.homEvaluation M ((pro_normalization M).2 hM) n).hom.app N = 𝟙 _
  pull_iso : ∀ (M N : Et l E W),
    EtNormalized l E etale M → EtNormalized l E etale N →
    EtFinite l E W levels M → EtFinite l E W levels N →
      IsIso (pullHom l E tensor M N)
  mapping_iso : ∀ (M N : Et l E W),
    EtNormalized l E etale M → EtNormalized l E etale N →
    EtFinite l E W levels M → EtFinite l E W levels N →
      IsIso (mappingComparison l E tensor structureImage point sections M N)
  representing_evaluation : ∀ (M N : Et l E W) (P : Et l E s)
    (h : P ⟶ representingObject l E structureImage M N),
    representingEquiv l E structureImage etale M N P h =
      etale.closed.tensor.map (Prod.mkHom (structureImage.P.map h) (𝟙 M)) ≫
        etale.closed.tensor.map
          (Prod.mkHom (structureImage.derivedAdjunction.counit.app
            ((etHom l E W).obj (op M, N))) (𝟙 M)) ≫ etale.closed.evaluation M N
  representing_naturality : ∀ (M N : Et l E W) (P P' : Et l E s)
    (b : P' ⟶ P) (h : P ⟶ representingObject l E structureImage M N),
    representingEquiv l E structureImage etale M N P' (b ≫ h) =
      etale.closed.tensor.map (Prod.mkHom (structureImage.P.map b) (𝟙 M)) ≫
        representingEquiv l E structureImage etale M N P h

/-- Sequence-site internal Hom, its normalized evaluations, and its punctual
representing object for either W=X or W=Y, with the canonical abelian-tower comparison.
Source: the retained second paragraph of prop-coef-integral-exceptional-adjoint;
Zheng Construction 4.1 and Lemma 4.10; Stacks 08J9, 0D6E, 04JQ and 04JM
(blueprint: lem-coef-system-internal-hom-representability).

Proof: (1) apply semilinear derived sections on both sites. Transpose actual system
Hom evaluation; its finite fibers are identities, so conservativity proves invertibility.
(2) exact inverse image preserves normalized transitions. Evaluate its tensor-normalized
Hom comparison, and apply finite constructible Hom comparison at each separate level.
(3) compose the structure-morphism adjunction with closed tensor-Hom adjunction; their
counits give the displayed evaluation word, without conditions on either input.
(4) finite constructible Hom gives a bounded finite-Tor Hom at every separate level.
Bounded-below injective representatives are K-injective, so site-comparison full
faithfulness identifies the unbounded system unit levelwise; evaluation is conservative.
(5) over the algebraically closed point, actual terminal sections are the trivial-Galois
abelian-sheaf equivalence and are exact, also for systems with coefficient actions.
(6) apply structure pushforward and exact point sections to the system unit and Hom
comparison. Canonical derived composition, normalized by its full derived unit, identifies
this with total termwise pro-etale sections after exact scalar restriction. Evaluation
and all tensor-Hom transposes are preserved by the specified adjunction words.
The bounded-below argument is used separately at each level; no common bound is imposed. -/
theorem systemInternalHomRepresentability (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (X Y : Scheme.{u}) [X.Over (Spec (CommRingCat.of D.k))]
    [Y.Over (Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (_c : Compactification f) :
    Nonempty (Representability l E (X ↘ Spec (CommRingCat.of D.k))) ∧
      Nonempty (Representability l E (Y ↘ Spec (CommRingCat.of D.k))) := by
  sorry

end WeilConjectures.SystemInternalHom
