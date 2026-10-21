/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.PointSystemTransportDescent
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.StrictRoosComparison
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
public import Sheaf.Paper.ExactProductFunctorStrictLimit
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-!
# Normalized whole-Roos transport for point coefficient systems

Source: blueprint main-20261015, prop-trf-rational-frobenius-integral-model proof (3),
integral maps as derived limits, with the extracted whole-cone refinement; Stacks Tag 0941
(blueprint: lem-trf-point-system-roos-transport).

The existing strict system category and signed Roos functor are used throughout. The
structures below package the canonical product normalizations, their natural derived
comparisons, and the restriction identity on the entire cone, including its shifted part.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.pointReductionModuleDerived
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard

universe t u a b a' b'
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointSystemRoos

variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The ambient completed-module category; no completeness condition is imposed on objects.
Source: blueprint integral-model proof (3)
(blueprint: lem-trf-point-system-roos-transport). -/
abbrev Ambient := scalarReductionSource l E (Spec (.of D.k))

/-- The existing integral scalar ring, with the common lift required by the site size.
Source: blueprint coefficient conventions
(blueprint: lem-trf-point-system-roos-transport). -/
abbrev Scalars : Type (max u (t + 1)) := pointRestrictionScalars.{t, u} l E none

/-- Exact sections with the recorded constant-to-completion scalar action.
Source: Stacks 0946; blueprint integral-model proof (3)
(blueprint: lem-trf-point-system-roos-transport). -/
abbrev T := pointRestrictionSections l E D.k none

/-- Ambient inverse image by the actual rth geometric Frobenius power, with transported action.
Source: blueprint integral-model proof (3)
(blueprint: lem-trf-point-system-roos-transport). -/
abbrev F (r : ℕ) :=
  pointRestrictionInverseImage l E (PointSystemTransport.pointPower D r).hom none

/-- Additivity is inherited from the recorded inverse-image equivalence.
Source: Stacks 03D6 (blueprint: lem-trf-point-system-roos-transport). -/
instance fAdditive (r : ℕ) : (F D l E r).Additive :=
  (isoSectionwiseModuleInverseImage_exact (PointSystemTransport.pointPower D r).hom
    (pointRestrictionCoefficientMap l E (PointSystemTransport.pointPower D r).hom none)).1

/-- Left exactness is inherited from the recorded inverse-image equivalence.
Source: Stacks 03D6 (blueprint: lem-trf-point-system-roos-transport). -/
instance fLimits (r : ℕ) : PreservesFiniteLimits (F D l E r) :=
  (isoSectionwiseModuleInverseImage_exact (PointSystemTransport.pointPower D r).hom
    (pointRestrictionCoefficientMap l E (PointSystemTransport.pointPower D r).hom none)).2.1

/-- Right exactness is inherited from the recorded inverse-image equivalence.
Source: Stacks 03D6 (blueprint: lem-trf-point-system-roos-transport). -/
instance fColimits (r : ℕ) : PreservesFiniteColimits (F D l E r) :=
  (isoSectionwiseModuleInverseImage_exact (PointSystemTransport.pointPower D r).hom
    (pointRestrictionCoefficientMap l E (PointSystemTransport.pointPower D r).hom none)).2.2

/-- Exactness and canonical countable-product preservation for sections and inverse image.
Source: Stacks 0946, 0947; blueprint integral-model proof (3), steps 1--2
(blueprint: lem-trf-point-system-roos-transport).
Proof: sections are evaluation at the weakly contractible final object, followed by
restriction along the constant-to-completion map. The point-sections exactness lemma
applies in the common coefficient universe, independently of the field universe.
Products of sheaf modules are sectionwise, so evaluation preserves their projections;
restriction of scalars preserves their underlying products and exactness. Inverse image
is the site reindexing equivalence, with its scalar action transported through the
canonical coefficient isomorphism. Evaluate at each reindexed object to identify its
canonical product comparison with the identity on tuples. -/
theorem exact_products :
    PreservesFiniteLimits (T D l E) ∧ PreservesFiniteColimits (T D l E) ∧
    (∀ V : ℕ → Ambient D l E, IsIso (piComparison (T D l E) V)) ∧
    (∀ (r : ℕ) (V : ℕ → Ambient D l E), IsIso (piComparison (F D l E r) V)) := by
  sorry

/-- The exact-sections finite-limit instance, from the preceding named assertion.
Source: Stacks 0946 (blueprint: lem-trf-point-system-roos-transport). -/
instance tLimits : PreservesFiniteLimits (T D l E) := (exact_products D l E).1

/-- The exact-sections finite-colimit instance, from the preceding named assertion.
Source: Stacks 0946 (blueprint: lem-trf-point-system-roos-transport). -/
instance tColimits : PreservesFiniteColimits (T D l E) := (exact_products D l E).2.1

/-- The existing scalar restriction to genuine completed-module towers.
Source: Stacks 0941 (blueprint: lem-trf-point-system-roos-transport). -/
abbrev U := coefficientSequenceRestriction l E (Spec (.of D.k))

/-- The strict representative U(M), retaining the actual quotient transitions.
Source: Stacks 0941 (blueprint: lem-trf-point-system-roos-transport). -/
abbrev X := (U D l E).mapHomologicalComplex (.up ℤ)

/-- The recorded levelwise inverse image G_r on strict systems.
Source: blueprint integral-model proof (3)
(blueprint: lem-trf-point-system-roos-transport). -/
abbrev G (r : ℕ) := PointSystemTransport.pull D l E r

/-- The actual restricted inverse-image system complex U(G_r M).
Source: blueprint integral-model proof (3)
(blueprint: lem-trf-point-system-roos-transport). -/
abbrev Y (r : ℕ) := (G D l E r).mapHomologicalComplex (.up ℤ) ⋙ X D l E

/-- Sections of the whole original system complex.
Source: blueprint integral-model proof (3)
(blueprint: lem-trf-point-system-roos-transport). -/
abbrev Z := PointSystemTransport.complexSections D l E

/-- Sections of the whole transported system complex.
Source: blueprint integral-model proof (3)
(blueprint: lem-trf-point-system-roos-transport). -/
abbrev Z' (r : ℕ) := PointSystemTransport.transportedComplexSections D l E r

/-- Commutativity inherited from the existing integral coefficient ring.
Source: coefficient conventions (blueprint: lem-trf-point-system-roos-transport). -/
instance scalarCommutative : CommRing (Scalars.{t, u} l E) :=
  inferInstanceAs (CommRing (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))

set_option backward.isDefEq.respectTransparency false in
/-- Additivity of the ordinary scalar tower limit.
Source: Stacks Tag 0941 (blueprint: lem-trf-point-system-roos-transport). -/
instance scalarLimitAdditive :
    (lim : (ℕᵒᵖ ⥤ ModuleCat.{max u (t + 1)}
      (pointRestrictionScalars.{t, u} l E none)) ⥤
        ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E none)).Additive :=
  inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- The total derived inverse limit on R-module towers, from the recorded adjunction.
Source: Stacks 0941 (blueprint: lem-trf-point-system-roos-transport). -/
abbrev scalarLimit :=
  (lim : (ℕᵒᵖ ⥤ ModuleCat.{max u (t + 1)}
    (pointRestrictionScalars.{t, u} l E none)) ⥤
      ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E none)).rightDerivedFunctor

/-- The existing total derived inverse limit on completed-module towers.
Source: Stacks 0941 (blueprint: lem-trf-point-system-roos-transport). -/
abbrev ambientLimit := coefficientConstantTowerLimit l E (Spec (.of D.k))

/-- The existing system realization L_s = Rlim U_s.
Source: Stacks 0941 (blueprint: lem-trf-point-system-roos-transport). -/
abbrev L := coefficientSequenceLimit l E (Spec (.of D.k))

/-- The canonical constant-limit inclusion in termwise-limit coordinates. This predicate
fixes a chain map by BOTH of its Roos coordinates, including the zero shifted coordinate.
Source: Stacks 0941, strict augmentation normalization
(blueprint: lem-trf-point-system-roos-transport). -/
def InclusionCoordinates {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (ι : ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I ⟶ roosF.obj I) :
    Prop :=
  ∀ p : ℤ, ι.f (p + 1) ≫ (roosχ I p).hom =
    biprod.lift 0 ((Pi.lift (fun n : ℕ ↦
      (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I)).f (p + 1))

/-- Normalize a full-tower Roos comparison by the actual universal right-derived unit.
Naturality is part of the natural isomorphism, including all strict maps. The equation
on every K-injective tower fixes the comparison uniquely after localization.
Source: Stacks 0941 and lem-weil-strict-roos-comparison
(blueprint: lem-trf-point-system-roos-transport). -/
def Normalized {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory A]
    [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive]
    (θ : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor ≅
      roosF ⋙ DerivedCategory.Q) : Prop :=
  ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ), I.IsKInjective →
    ∀ (_hI : ∀ p : ℤ, Injective (I.X p)),
    ∃ ι : ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I ⟶ roosF.obj I,
      InclusionCoordinates I ι ∧ QuasiIso ι ∧
      (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ I ≫ θ.hom.app I =
        DerivedCategory.Q.map ι

/-- System realization in the fixed normalized full-tower Roos coordinates.
Source: blueprint integral-model proof (3), proof step 3
(blueprint: lem-trf-point-system-roos-transport). -/
def realization
    (θ : DerivedCategory.Q ⋙ ambientLimit D l E ≅ roosF ⋙ DerivedCategory.Q)
    (M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ) :
    (L D l E).obj (DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj (roosF.obj ((X D l E).obj M)) :=
  (ambientLimit D l E).mapIso ((U D l E).mapDerivedCategoryFactors.app M) ≪≫
    θ.app ((X D l E).obj M)

/-- A comparison is diagonal precisely when its two projections use the same product
comparison in their respective degrees. These equations prohibit off-diagonal terms.
Source: blueprint integral-model proof (3), steps 3--4
(blueprint: lem-trf-point-system-roos-transport). -/
def Diagonal {A : Type a} {B : Type a'} [Category.{b} A] [Category.{b'} B] [Abelian A] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    (P : A ⥤ B) [P.Additive]
    (V : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (W : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (ψ : (P.mapHomologicalComplex (.up ℤ)).obj (roosP V) ≅ roosP W)
    (κ : (P.mapHomologicalComplex (.up ℤ)).obj (roosF.obj V) ≅ roosF.obj W) : Prop :=
  ∀ p : ℤ,
    κ.hom.f (p + 1) ≫ (roosχ W p).hom ≫ biprod.fst =
      P.map ((roosχ V p).hom ≫ biprod.fst) ≫ ψ.hom.f p ∧
    κ.hom.f (p + 1) ≫ (roosχ W p).hom ≫ biprod.snd =
      P.map ((roosχ V p).hom ≫ biprod.snd) ≫ ψ.hom.f (p + 1)

attribute [local irreducible] roosF

set_option backward.isDefEq.respectTransparency false in
/-- The whole-tower point-system comparison, including its exact product normalizations.
Each field refers to the existing strict systems, actual transition maps, and the same
fixed normalized Roos identifications. The derived fields are natural transformations
on the entire ordinary unbounded derived category.
Source: blueprint integral-model proof (3); Stacks 0941
(blueprint: lem-trf-point-system-roos-transport). -/
structure Models where
  /-- Normalized Roos coordinates on ALL completed-module towers. -/
  thetaA : DerivedCategory.Q ⋙ ambientLimit D l E ≅ roosF ⋙ DerivedCategory.Q
  /-- Fix the zero shifted-coordinate augmentation and universal total-limit normalization. -/
  thetaA_normalized : Normalized thetaA
  /-- Normalized Roos coordinates on ALL R-module towers. -/
  thetaR : DerivedCategory.Q ⋙ scalarLimit.{t, u} l E ≅ roosF ⋙ DerivedCategory.Q
  /-- The same total-limit normalization over R. -/
  thetaR_normalized : Normalized thetaR

/-- The canonical products and both diagonal cone comparisons on strict representatives.
Source: blueprint integral-model proof (3), steps 1--4
(blueprint: lem-trf-point-system-roos-transport). -/
structure Products (r : ℕ) where
  /-- Canonical inverse-image product comparison, including the finite coefficient action. -/
  productF : ∀ M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ,
    ((F D l E r).mapHomologicalComplex (.up ℤ)).obj (roosP ((X D l E).obj M)) ≅
      roosP ((Y D l E r).obj M)
  /-- Canonical sections product comparison, before taking the cone. -/
  productT : ∀ M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ,
    ((T D l E).mapHomologicalComplex (.up ℤ)).obj (roosP ((X D l E).obj M)) ≅
      roosP ((Z D l E).obj M)
  /-- Inverse image applied to the ENTIRE Roos cone. -/
  kappaF : ∀ M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ,
    ((F D l E r).mapHomologicalComplex (.up ℤ)).obj (roosF.obj ((X D l E).obj M)) ≅
      roosF.obj ((Y D l E r).obj M)
  /-- Exact sections applied to the ENTIRE Roos cone. -/
  kappaT : ∀ M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ,
    ((T D l E).mapHomologicalComplex (.up ℤ)).obj (roosF.obj ((X D l E).obj M)) ≅
      roosF.obj ((Z D l E).obj M)

/-- Projection and diagonal normalization of the canonical product and cone maps.
Source: blueprint integral-model proof (3), steps 1--4
(blueprint: lem-trf-point-system-roos-transport). -/
def ProductLaws (r : ℕ) (products : Products D l E r) : Prop :=
  -- productF_projection
  (∀ (M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ)
        (i : ℤ) (n : ℕ) (V : (Spec (.of D.k)).ProEt)
        (x : (((F D l E r).mapHomologicalComplex (.up ℤ)).obj
          (roosP ((X D l E).obj M))).X i |>.val.obj (op V)),
        HEq (((products.productF M).hom ≫ Pi.π
          (fun n : ℕ ↦ ((Y D l E r).obj M).asFunctor.obj (op n)) n).f i |>.val.app (op V) x)
          (((Pi.π (fun n : ℕ ↦ ((X D l E).obj M).asFunctor.obj (op n)) n).f i).val.app
            (op ((proEtaleIsoPostcompose (PointSystemTransport.pointPower D r).hom).obj V)) x)) ∧
  -- productT_projection
  (∀ (M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ)
        (i : ℤ) (n : ℕ)
        (x : (((T D l E).mapHomologicalComplex (.up ℤ)).obj
          (roosP ((X D l E).obj M))).X i),
        HEq (((products.productT M).hom ≫ Pi.π
          (fun n : ℕ ↦ ((Z D l E).obj M).asFunctor.obj (op n)) n).f i x)
          (((Pi.π (fun n : ℕ ↦ ((X D l E).obj M).asFunctor.obj (op n)) n).f i).val.app
            (op (ProEt.mk (𝟙 (Spec (.of D.k))))) x)) ∧
  -- kappaF_diagonal
  (∀ M, Diagonal (F D l E r) ((X D l E).obj M)
      ((Y D l E r).obj M) (products.productF M) (products.kappaF M)) ∧
  -- kappaT_diagonal
  (∀ M, Diagonal (T D l E) ((X D l E).obj M)
      ((Z D l E).obj M) (products.productT M) (products.kappaT M))

/-- Natural derived comparisons, fixed by their whole-cone representative equations.
Source: blueprint integral-model proof (3), steps 4 and 6
(blueprint: lem-trf-point-system-roos-transport). -/
structure Comparisons (r : ℕ) where
  /-- a_r is a natural isomorphism on the unrestricted system derived category. -/
  a : L D l E ⋙ (F D l E r).mapDerivedCategory ≅
    (G D l E r).mapDerivedCategory ⋙ L D l E
  /-- zeta has the inverse-sections-comparison direction specified in the node. -/
  zeta : PointSystemTransport.derivedSections D l E ⋙ scalarLimit.{t, u} l E ≅
    L D l E ⋙ (T D l E).mapDerivedCategory
  /-- The restriction/insertion/sheafification recipe on ANY completed-module complex. -/
  sigma : (T D l E).mapHomologicalComplex (.up ℤ) ⟶
    (F D l E r).mapHomologicalComplex (.up ℤ) ⋙ (T D l E).mapHomologicalComplex (.up ℤ)
  /-- Its natural localization to all ambient completed-module derived objects. -/
  sigmaD : (T D l E).mapDerivedCategory ⟶
    (F D l E r).mapDerivedCategory ⋙ (T D l E).mapDerivedCategory

/-- Representative normalizations of the four natural comparisons, as proof data.
Source: blueprint integral-model proof (3), steps 4 and 6
(blueprint: lem-trf-point-system-roos-transport). -/
def ComparisonLaws (r : ℕ) (models : Models D l E) (products : Products D l E r)
    (comparisons : Comparisons D l E r) : Prop :=
  -- a_model
  (∀ M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ,
      comparisons.a.hom.app (DerivedCategory.Q.obj M) ≫
          (L D l E).map ((G D l E r).mapDerivedCategoryFactors.hom.app M) ≫
          (realization D l E models.thetaA
            (((G D l E r).mapHomologicalComplex (.up ℤ)).obj M)).hom =
        (F D l E r).mapDerivedCategory.map ((realization D l E models.thetaA M).hom) ≫
          (F D l E r).mapDerivedCategoryFactors.hom.app (roosF.obj ((X D l E).obj M)) ≫
          DerivedCategory.Q.map (products.kappaF M).hom) ∧
  -- zeta_model
  (∀ M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ,
      comparisons.zeta.hom.app (DerivedCategory.Q.obj M) ≫
          (T D l E).mapDerivedCategory.map ((realization D l E models.thetaA M).hom) ≫
          (T D l E).mapDerivedCategoryFactors.hom.app (roosF.obj ((X D l E).obj M)) ≫
          DerivedCategory.Q.map (products.kappaT M).hom =
        (scalarLimit.{t, u} l E).map
            ((PointSystemTransport.sections D l E).mapDerivedCategoryFactors.hom.app M) ≫
          models.thetaR.hom.app ((Z D l E).obj M)) ∧
  -- sigma_sections
  (∀ (K : CochainComplex (Ambient D l E) ℤ) (i : ℤ)
      (x : (K.X i).val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
      (comparisons.sigma.app K).f i x =
        pointRestrictionRaw l E (PointSystemTransport.pointPower D r).hom none (K.X i) x) ∧
  -- sigma_model
  (∀ K : CochainComplex (Ambient D l E) ℤ,
      comparisons.sigmaD.app (DerivedCategory.Q.obj K) ≫
          (T D l E).mapDerivedCategory.map ((F D l E r).mapDerivedCategoryFactors.hom.app K) ≫
          (T D l E).mapDerivedCategoryFactors.hom.app
            (((F D l E r).mapHomologicalComplex (.up ℤ)).obj K) =
        (T D l E).mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map (comparisons.sigma.app K))

/-- The normalized whole-tower transport identity and its actual strict chain model.
Source: blueprint integral-model proof (3), steps 5--8
(blueprint: lem-trf-point-system-roos-transport). -/
def TransportLaws (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r)
    (models : Models D l E) (products : Products D l E r)
    (comparisons : Comparisons D l E r) : Prop :=
  -- transport
  (∀ C : coefficientSequenceDerived l E (Spec (.of D.k)),
      (scalarLimit.{t, u} l E).map ((PointSystemTransport.derivedTransport D l E hl r hr).app C) ≫
          (scalarLimit.{t, u} l E).map
            ((Functor.mapDerivedCategoryCompIso (G D l E r)
              (PointSystemTransport.sections D l E)).hom.app C) ≫
          comparisons.zeta.hom.app ((G D l E r).mapDerivedCategory.obj C) =
        comparisons.zeta.hom.app C ≫ comparisons.sigmaD.app ((L D l E).obj C) ≫
          (T D l E).mapDerivedCategory.map (comparisons.a.hom.app C)) ∧
  -- transport_model
  (∀ M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ,
        (scalarLimit.{t, u} l E).map
            ((PointSystemTransport.sections D l E).mapDerivedCategoryFactors.inv.app M) ≫
          (scalarLimit.{t, u} l E).map
            ((PointSystemTransport.derivedTransport D l E hl r hr).app (DerivedCategory.Q.obj M)) ≫
          (scalarLimit.{t, u} l E).map
            ((G D l E r ⋙ PointSystemTransport.sections D l E).mapDerivedCategoryFactors.hom.app
                M) ≫
          models.thetaR.hom.app ((Z' D l E r).obj M) =
        models.thetaR.hom.app ((Z D l E).obj M) ≫
          DerivedCategory.Q.map (roosF.map
            ((PointSystemTransport.chainTransport D l E hl r hr).app M))) ∧
  -- transition_square
  (∀ M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ,
        roosU ((Z D l E).obj M) ≫
            roosPmap ((PointSystemTransport.chainTransport D l E hl r hr).app M) =
          roosPmap ((PointSystemTransport.chainTransport D l E hl r hr).app M) ≫
            roosU ((Z' D l E r).obj M)) ∧
  -- transport_diagonal
  (∀ (M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ) (p : ℤ),
        (roosF.map ((PointSystemTransport.chainTransport D l E hl r hr).app M)).f (p + 1) ≫
            (roosχ ((Z' D l E r).obj M) p).hom =
          (roosχ ((Z D l E).obj M) p).hom ≫
            biprod.map
              ((roosPmap ((PointSystemTransport.chainTransport D l E hl r hr).app M)).f p)
              ((roosPmap ((PointSystemTransport.chainTransport D l E hl r hr).app M)).f (p + 1))) ∧
  -- restriction_cone
  (∀ M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ,
        (products.kappaT M).inv ≫ comparisons.sigma.app (roosF.obj ((X D l E).obj M)) ≫
          ((T D l E).mapHomologicalComplex (.up ℤ)).map (products.kappaF M).hom ≫
          (products.kappaT (((G D l E r).mapHomologicalComplex (.up ℤ)).obj M)).hom =
        roosF.map ((PointSystemTransport.chainTransport D l E hl r hr).app M)) ∧
  -- restriction_products
  (∀ (M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ)
        (i : ℤ) (n : ℕ) (x : (roosP ((Z D l E).obj M)).X i),
        ∃ xₙ : (M.X i).val.obj (op (n, ProEt.mk (𝟙 (Spec (.of D.k))))),
          HEq (((Pi.π (fun n : ℕ ↦ ((Z D l E).obj M).asFunctor.obj (op n)) n).f i) x) xₙ ∧
          HEq (((roosPmap ((PointSystemTransport.chainTransport D l E hl r hr).app M) ≫
          Pi.π (fun n : ℕ ↦ ((Z' D l E r).obj M).asFunctor.obj (op n)) n).f i) x)
          ((M.X i).val.map
            (Prod.mkHom (𝟙 n)
              (pointRestrictionArrow (PointSystemTransport.pointPower D r).hom)).op
            xₙ))

/-- All canonical maps and their full normalization and transport laws.
Source: blueprint integral-model proof (3), steps 1--8
(blueprint: lem-trf-point-system-roos-transport). -/
structure Data (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r) where
  /-- Fixed normalized total-limit models. -/
  models : Models D l E
  /-- Canonical products and cone comparisons. -/
  products : Products D l E r
  /-- Their projection and both-coordinate normalizations. -/
  productLaws : ProductLaws D l E r products
  /-- Natural comparisons on unrestricted derived categories. -/
  comparisons : Comparisons D l E r
  /-- Their whole-cone representative normalizations. -/
  comparisonLaws : ComparisonLaws D l E r models products comparisons
  /-- The actual chain and derived transport identities. -/
  transportLaws : TransportLaws D l E hl r hr models products comparisons

/-- Whole-Roos normalization of point-system transport and sections, with no restrictions
on the realized ambient object. All comparisons and the transport equality concern whole
towers and are natural for every morphism in the ordinary unbounded derived category.

Source: literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-d-weil/
prop-trf-rational-frobenius-integral-model.proof.md, (3), integral maps as derived limits;
agent-formulated whole-cone refinement; Stacks Tag 0941
(blueprint: lem-trf-point-system-roos-transport).

Proof, following the eight steps of the node:
1. Restrict the actual quotient-linear systems along the completed projections. The
coefficient identity pi_n c_hat = c_n F(pi_n) identifies U(G M) with F(U M), including
all original transitions and the finite tensor insertions j from the descent lemma.
The site reindexing equivalence is additive, exact and preserves the canonical products.
2. Sections at the point are exact by lem-weil-point-proetale-sections-exact. Products
are sectionwise by lem-weil-proetale-countable-products-exact; scalar restriction keeps
those products and exactness. Products of R-modules are exact by coordinatewise choice.
3. Apply lem-weil-strict-roos-comparison and the total-limit model of
lem-weil-pbc-ringed-strict-tower-homotopy-limit to both module categories. Their universal
units fix thetaA and thetaR. The inclusion is (0, gamma). The signed permutation
(b,a) to (a,-b) identifies these coordinates with those in
lem-cbc-exact-product-functor-strict-limit without changing diagonal comparisons.
4. Apply that exact-product comparison to inverse image and sections. Its projection
formulas give productF and productT. Apply each on both cone coordinates to give
kappaF and kappaT, then conjugate by theta to get a and zeta in the displayed directions.
These are comparisons of the entire limit cones, independent of the tower resolutions.
5. The strict transformation of lem-trf-point-system-transport-descent has components u_n
commuting with the ORIGINAL transitions. Thus (1-s') product(u) = product(u) (1-s).
The actual cone map is (product(u),product(u)), with no off-diagonal component.
Naturality of thetaR identifies its localization with Rlim(I), as transport_model states.
6. On every ambient complex, restriction followed by insertion and sheafification is
actual restriction in the site-reindexing coordinates, by the point-transport recipe.
The completed coefficient identity makes it R-linear, and naturality with respect to
differentials makes a chain map. Exactness localizes this natural transformation.
7. Compare both coordinates after every product projection. Each is the actual
restriction x_n to x_n restricted along h^r; the coefficient identifications and finite j
identify them with u_n. Hence applying sections to kappaF after sigma equals the inverse
kappaT comparison after H(u), on the entire cone, including its shifted coordinate.
8. Substitute the conjugation formulas of step 4 and the localized cone-map equation of
step 5. Naturality of sigma with thetaA cancels the consecutive inverse comparisons and
gives transport. Natural chain comparisons localize along quasi-isomorphisms, giving
naturality for every derived system morphism, without assuming evaluation is faithful. -/
theorem point_system_roos_transport (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r) :
    Nonempty (Data D l E hl r hr) := by
  sorry

end WeilConjectures.PointSystemRoos
