/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.Paper.RationalLocallyFree
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.Paper.ContinuousRationalDerivedRealization
public import Sheaf.Paper.CompletedCoefficientPresentationTransport
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.PointAutomorphismTransportScalarExtension
public import Sheaf.Paper.CommonStageLocallyFree
public import Sheaf.CategoryTheory.StageSystemFunctorDescent
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCompletion
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientPullback
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

public import Mathlib.Algebra.CharP.CharAndCard
import Sheaf.Paper.InverseImagePullbackComparisonDerived
import Sheaf.SixFunctors.ConstructibleTensorCompletion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.CompletedOperationTowerSubstitution
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Targets.SliceRestrictionStrictDerivedLimit
import Sheaf.Paper.IntegralPullbackComparisonRealization
import Sheaf.Paper.OrdinaryCompletedIntegralPullback
import Sheaf.Paper.ConstantCoefficientScalarNormalization
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness
import Sheaf.Paper.LisseEConstructibleIntegralLattice
import Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal
import Sheaf.CategoryTheory.ScalarLocalizationDerivedHom
import Sheaf.Paper.PointFibreEquivalence
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

/-! # Normalized realization of the rational lisse heart

Source: Bhatt--Scholze, Lemma 6.8.2, Definition 6.8.3, Proposition 6.8.4(1),(4),(6),
Proposition 6.8.14(2), Remark 6.8.15, pp. 58--62
(blueprint: def-real-lisse-realization-data).

The continuous coefficient presentation below is identified with the specified completion
by every residue projection, and with its sheaf localization by the localization unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme MonoidalCategory
open scoped TensorProduct MonoidalCategory
namespace WeilConjectures.LisseRealization

/-- A finite-type geometric-base scheme, with no separation condition. Morphisms between
these bases will be arbitrary scheme morphisms. Source: BS 6.8.14 and Remark 6.8.15
(blueprint: def-real-lisse-realization-data). -/
structure Base (D : FiniteFieldDatum.{u}) (l : ℕ) (hl : l ≠ D.p) where
  scheme : Scheme.{u}
  [over : scheme.Over (Spec (.of D.k))]
  [finiteType : LocallyOfFiniteType (scheme ↘ Spec (.of D.k))]
  [quasiCompact : QuasiCompact (scheme ↘ Spec (.of D.k))]

attribute [instance] Base.over Base.finiteType Base.quasiCompact

/-- The coefficient prime is a unit in each residue field. This is inherited from the
finite-field base, so supplies no extra hypothesis. Source: BS 6.8.14
(blueprint: def-real-lisse-realization-data). -/
@[instance_reducible]
def baseInvertible (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (X : Base D l hl) (x : X.scheme) :
    Invertible (l : X.scheme.residueField x) := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (f := D.a)
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  have hunit : IsUnit (l : D.k₀) :=
    (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : l.Prime) hl.symm).isUnit
  let g := (X.scheme ↘ Spec (.of D.k)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  have h : IsUnit (l : X.scheme.residueField x) := by
    simpa only [map_natCast] using hunit.map
      ((Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv ≫ g.appTop ≫
        X.scheme.Γevaluation x).hom
  exact h.invertible

attribute [instance] baseInvertible

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The raw source category. Source: BS 6.8.14
(blueprint: def-real-lisse-realization-data). -/
abbrev Raw (X : Base D l hl) := sfRationalConstructibleCategory l E X.scheme

/-- The recorded lisse-heart predicate. Source: BS 6.8.3 and 6.8.14
(blueprint: def-real-lisse-realization-data). -/
abbrev Lisse (X : Base D l hl) := rationalLisseHeartProperty l E X.scheme

/-- The ordinary continuous/localized rational module category. Source: BS 6.8.2
(blueprint: def-real-lisse-realization-data). -/
abbrev Modules (X : Base D l hl) := pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E)

/-- The exact recorded completed rational tensor. Source: BS 6.8.15
(blueprint: def-real-lisse-realization-data). -/
abbrev tensor (X : Base D l hl) := rationalDerivedTensor l E X.scheme

/-- The recorded coefficient unit. Source: BS 6.8.15
(blueprint: def-real-lisse-realization-data). -/
abbrev unit (X : Base D l hl) := pullbackTensorRationalUnit l E X.scheme

/-- The recorded pullback, for arbitrary scheme maps. Source: BS 6.8.15
(blueprint: def-real-lisse-realization-data). -/
abbrev pull {X Y : Base D l hl} (f : X.scheme ⟶ Y.scheme) :=
  rationalDerivedPullback l E f

/-- The actual rational coefficient map, adjunct to precomposition of functions.
Source: BS 6.8.15 (blueprint: def-real-lisse-realization-data). -/
def coefficientPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (adicTowerInverseImage f).obj (rationalCoefficientSheaf l Y E) ⟶
      rationalCoefficientSheaf l X E := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientPullback (ULift.{u + 1, u} E) f

/-- Ordinary module inverse image, not completed inverse image. Source: BS 6.8.15
(blueprint: def-real-lisse-realization-data). -/
abbrev ordinaryPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ContinuousRational.modulePull f (coefficientPull l E f)

/-- Normalized derived realization and its restriction to the lisse heart. All comparison
data are part of the conclusion, never additional input. Source: BS 6.8.2 and 6.8.14
(blueprint: def-real-lisse-realization-data). -/
structure At (X : Base D l hl) where
  completion : completedIntegralCommRingSheafUnrestricted l E X.scheme ≅
    AlgebraicGeometry.Scheme.integralCoefficientSheaf l X.scheme E
  completion_residues : ∀ n : ℕ,
    completion.hom ≫ continuousCoefficientReduction l E X.scheme n =
      completedIntegralCommRingProjectionUnrestricted l E X.scheme n ≫
        (discreteContinuousCoefficientIso X.scheme).hom.app
          (AlgebraicGeometry.Scheme.finiteCoefficientRing l E n)
  localization : integralCoefficientLocalization l X.scheme E ≅
    rationalCoefficientSheaf l X.scheme E
  localization_unit : integralCoefficientLocalizationNormalized l E X.scheme localization.hom
  J : Raw D l hl E X ⥤ DerivedCategory (Modules D l hl E X)
  [additive : J.Additive]
  integral : sfRationalConstructibleLocalization l E X.scheme ⋙ J ≅
    (sfIntegralConstructible l E X.scheme).ι ⋙
      pbcDerivedExtend (completion.hom ≫ integralRationalCoefficientMap l E X.scheme)
  fractions : ∀ (K L : sfIntegralConstructibleCategory l E X.scheme)
      (f : K ⟶ L) (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
    J.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f) =
      sfRationalCoefficientEquiv l E a •
        J.map ((sfRationalConstructibleLocalization l E X.scheme).map f)
  degree_zero : ∀ (K : Raw D l hl E X), Lisse D l hl E X K →
    Nonempty (J.obj K ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((DerivedCategory.homologyFunctor _ 0).obj (J.obj K)))
  fully_faithful : ∀ (K L : Raw D l hl E X),
    Lisse D l hl E X K → Lisse D l hl E X L →
      Function.Bijective ((J ⋙ DerivedCategory.homologyFunctor _ 0).map :
        (K ⟶ L) → _)
  image : ∀ M : Modules D l hl E X, M.IsFiniteLocallyFree ↔
    ∃ K : Raw D l hl E X, Lisse D l hl E X K ∧
      Nonempty ((DerivedCategory.homologyFunctor _ 0).obj (J.obj K) ≅ M)

attribute [instance] At.additive

/-- The sheaf realization is the actual degree-zero cohomology of scalar extension.
Source: BS 6.8.14 (blueprint: def-real-lisse-realization-data). -/
def At.sheaf {X : Base D l hl} (a : At D l hl E X) :=
  a.J ⋙ DerivedCategory.homologyFunctor _ 0


/-- Tensor and unit comparisons on precisely the lisse objects, with explicit coherence
for the recorded completed operations. Source: BS 6.8.4(6), 6.8.15
(blueprint: def-real-lisse-realization-data). -/
structure TensorAt (X : Base D l hl) (a : At D l hl E X) where
  unit_mem : Lisse D l hl E X (unit D l hl E X)
  tensor_mem : ∀ (K L : Raw D l hl E X), Lisse D l hl E X K → Lisse D l hl E X L →
    Lisse D l hl E X ((tensor D l hl E X).obj (K, L))
  unit : (a.sheaf D l hl E).obj (LisseRealization.unit D l hl E X) ≅
    𝟙_ (Modules D l hl E X)
  tensor : ∀ (K L : Raw D l hl E X), Lisse D l hl E X K → Lisse D l hl E X L →
    ((a.sheaf D l hl E).obj ((LisseRealization.tensor D l hl E X).obj (K, L)) ≅
      ((a.sheaf D l hl E).obj K ⊗ (a.sheaf D l hl E).obj L))
  naturality : ∀ (K L K' L' : Raw D l hl E X)
    (hK : Lisse D l hl E X K) (hL : Lisse D l hl E X L)
    (hK' : Lisse D l hl E X K') (hL' : Lisse D l hl E X L')
    (f : K ⟶ K') (g : L ⟶ L'),
    (a.sheaf D l hl E).map ((LisseRealization.tensor D l hl E X).map (Prod.mkHom f g)) ≫
      (tensor K' L' hK' hL').hom =
    (tensor K L hK hL).hom ≫ ((a.sheaf D l hl E).map f ⊗ₘ (a.sheaf D l hl E).map g)
  associativity : ∀ (K L M : Raw D l hl E X)
    (hK : Lisse D l hl E X K) (hL : Lisse D l hl E X L)
    (hM : Lisse D l hl E X M),
    (a.sheaf D l hl E).map
        (pullbackTensorRationalAssociator l E X.scheme K L M).hom ≫
      (tensor K _ hK (tensor_mem L M hL hM)).hom ≫
      (𝟙 _ ⊗ₘ (tensor L M hL hM).hom) =
    (tensor _ M (tensor_mem K L hK hL) hM).hom ≫
      ((tensor K L hK hL).hom ⊗ₘ 𝟙 _) ≫
      (α_ ((a.sheaf D l hl E).obj K) ((a.sheaf D l hl E).obj L)
        ((a.sheaf D l hl E).obj M)).hom
  symmetry : ∀ (K L : Raw D l hl E X)
    (hK : Lisse D l hl E X K) (hL : Lisse D l hl E X L),
    (a.sheaf D l hl E).map (pullbackTensorRationalBraiding l E X.scheme K L).hom ≫
      (tensor L K hL hK).hom =
    (tensor K L hK hL).hom ≫ (β_ _ _).hom
  left_unit : ∀ (K : Raw D l hl E X) (hK : Lisse D l hl E X K),
    (a.sheaf D l hl E).map (pullbackTensorRationalLeftUnitor l E X.scheme K).hom =
      (tensor _ K unit_mem hK).hom ≫ (unit.hom ⊗ₘ 𝟙 _) ≫ (λ_ _).hom
  right_unit : ∀ (K : Raw D l hl E X) (hK : Lisse D l hl E X K),
    (a.sheaf D l hl E).map (pullbackTensorRationalRightUnitor l E X.scheme K).hom =
      (tensor K _ hK unit_mem).hom ≫ (𝟙 _ ⊗ₘ unit.hom) ≫ (ρ_ _).hom

/-- Pullback comparison to actual ordinary module inverse image, together with its
integral balanced-tensor normalization. Source: BS 6.8.15
(blueprint: def-real-lisse-realization-data). -/
structure Along {X Y : Base D l hl} (f : X.scheme ⟶ Y.scheme)
    (aX : At D l hl E X) (aY : At D l hl E Y) where
  preserves : ∀ K : Raw D l hl E Y, Lisse D l hl E Y K →
    Lisse D l hl E X ((pull D l hl E f).obj K)
  comparison : ∀ K : Raw D l hl E Y, Lisse D l hl E Y K →
    ((aX.sheaf D l hl E).obj ((pull D l hl E f).obj K) ≅
      (ordinaryPull l E f).obj ((aY.sheaf D l hl E).obj K))
  naturality : ∀ (K L : Raw D l hl E Y)
    (hK : Lisse D l hl E Y K) (hL : Lisse D l hl E Y L) (g : K ⟶ L),
    (aX.sheaf D l hl E).map ((pull D l hl E f).map g) ≫ (comparison L hL).hom =
      (comparison K hK).hom ≫ (ordinaryPull l E f).map ((aY.sheaf D l hl E).map g)
  balance : pbcExtend (aY.completion.hom ≫ integralRationalCoefficientMap l E Y.scheme) ⋙
      ordinaryPull l E f ≅
    ContinuousRational.modulePull f
      ((adicTowerInverseImage f).map (purCoefficientIso l E Y.scheme).inv ≫
        AlgebraicGeometry.Scheme.completedCoefficientMap f (pbcIntegralDatum l E) ≫
          (purCoefficientIso l E X.scheme).hom) ⋙
      pbcExtend (aX.completion.hom ≫ integralRationalCoefficientMap l E X.scheme)


/-- Composition comparison on the ordinary pullbacks, fixed by the images of tensor
unit sections. Source: BS 6.8.15 (blueprint: def-real-lisse-realization-data). -/
structure Composition {X Y Z : Base D l hl} (f : X.scheme ⟶ Y.scheme)
    (g : Z.scheme ⟶ X.scheme) (aX : At D l hl E X) (aY : At D l hl E Y)
    (aZ : At D l hl E Z) (af : Along D l hl E f aX aY) (ag : Along D l hl E g aZ aX)
    (ac : Along D l hl E (g ≫ f) aZ aY) where
  ordinary : ordinaryPull l E (g ≫ f) ≅ ordinaryPull l E f ⋙ ordinaryPull l E g
  sections : ∀ (M : Modules D l hl E Y) (U : Y.scheme.ProEt)
    (m : M.val.obj (op U)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange (g ≫ f)).obj U))
        (ContinuousRational.moduleUnit (g ≫ f) (coefficientPull l E (g ≫ f)) M U m) =
      (((ordinaryPull l E g).obj ((ordinaryPull l E f).obj M)).val.map
        ((MorphismProperty.Over.pullbackComp g f).hom.app U).op)
          (ContinuousRational.moduleUnit g (coefficientPull l E g)
            ((ordinaryPull l E f).obj M) ((proEtaleBaseChange f).obj U)
            (ContinuousRational.moduleUnit f (coefficientPull l E f) M U m))
  compatibility : ∀ (K : Raw D l hl E Y) (hK : Lisse D l hl E Y K),
    (ac.comparison K hK).hom ≫ ordinary.hom.app ((aY.sheaf D l hl E).obj K) =
      (aZ.sheaf D l hl E).map (pullbackTensorRationalComposition l E f g K).hom ≫
        (ag.comparison _ (af.preserves K hK)).hom ≫
          (ordinaryPull l E g).map (af.comparison K hK).hom

/-- Identity comparison, fixed by the identity base-change projection.
Source: BS 6.8.15 (blueprint: def-real-lisse-realization-data). -/
structure Identity (X : Base D l hl) (a : At D l hl E X)
    (ai : Along D l hl E (𝟙 X.scheme) a a) where
  ordinary : ordinaryPull l E (𝟙 X.scheme) ≅ 𝟭 _
  sections : ∀ (M : Modules D l hl E X) (U : X.scheme.ProEt) (m : M.val.obj (op U)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange (𝟙 X.scheme)).obj U))
      (ContinuousRational.moduleUnit (𝟙 X.scheme) (coefficientPull l E (𝟙 X.scheme)) M U m) =
        M.val.map ((MorphismProperty.Over.pullbackId _ _ X.scheme).hom.app U).op m
  raw : pull D l hl E (𝟙 X.scheme) ≅ 𝟭 _
  compatibility : ∀ (K : Raw D l hl E X) (hK : Lisse D l hl E X K),
    (ai.comparison K hK).hom ≫ ordinary.hom.app ((a.sheaf D l hl E).obj K) =
      (a.sheaf D l hl E).map (raw.hom.app K)

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]

/-- Finite scalar extension with the normalized balanced map, not an arbitrary equivalence.
Source: BS 6.8.14--6.8.15 (blueprint: def-real-lisse-realization-data). -/
structure FieldChange (i : E →ₐ[ℚ_[l]] F) (X : Base D l hl)
    (aE : At D l hl E X) (aF : At D l hl F X) where
  coefficient : rationalCoefficientSheaf l X.scheme E ⟶ rationalCoefficientSheaf l X.scheme F
  normalized : ∀ (U : X.scheme.ProEtᵒᵖ)
    (s : (rationalCoefficientSheaf l X.scheme E).obj.obj U) (x : U.unop.left),
    rationalCoefficientValue l F X.scheme U (coefficient.hom.app U s) x =
      i (rationalCoefficientValue l E X.scheme U s x)
  preserves : ∀ (K : Raw D l hl E X), Lisse D l hl E X K →
    Lisse D l hl F X ((sfRationalScalarExtension l E X.scheme D.p hl F i).obj K)
  comparison : ∀ (K : Raw D l hl E X), Lisse D l hl E X K →
    ((aF.sheaf D l hl F).obj
        ((sfRationalScalarExtension l E X.scheme D.p hl F i).obj K) ≅
      (pbcExtend coefficient).obj ((aE.sheaf D l hl E).obj K))
  naturality : ∀ (K L : Raw D l hl E X)
    (hK : Lisse D l hl E X K) (hL : Lisse D l hl E X L) (f : K ⟶ L),
    (aF.sheaf D l hl F).map
        ((sfRationalScalarExtension l E X.scheme D.p hl F i).map f) ≫
      (comparison L hL).hom = (comparison K hK).hom ≫
        (pbcExtend coefficient).map ((aE.sheaf D l hl E).map f)

/-- The rational point as a finite-type base, with its identity structure map.
Source: BS 6.8 and the blueprint geometric point convention
(blueprint: def-real-lisse-realization-data). -/
def point : Base D l hl := ⟨Spec (.of D.k)⟩

/-- Constants acting on ordinary sections at the geometric point. Source: BS 6.8.1
(blueprint: def-real-lisse-realization-data). -/
def pointConstants : E →+*
    (rationalCoefficientSheaf l (Spec (.of D.k)) E).obj.obj
      (op (ProEt.mk (𝟙 (Spec (.of D.k))))) :=
  { toFun := fun a ↦ (ContinuousRational.scalarSections l E (Spec (.of D.k)) a).val _
    map_one' := rfl
    map_mul' := fun _ _ ↦ rfl
    map_zero' := rfl
    map_add' := fun _ _ ↦ rfl }

/-- Ordinary sheaf sections, with coefficients restricted along constant rational functions.
Source: BS 6.8.1 (blueprint: def-real-lisse-realization-data). -/
def sections : Modules D l hl E (point D l hl) ⥤ ModuleCat.{u + 1} E :=
  AlgebraicGeometry.ProEtale.pointModuleSections D.k
    (rationalCoefficientSheaf l (Spec (.of D.k)) E) ⋙
      ModuleCat.restrictScalars (pointConstants D l E)

/-- The existing small derived localization of coefficient modules.
Source: blueprint point target convention (blueprint: def-real-lisse-realization-data). -/
instance fieldDerived (F : Type u) [Field F] :
    HasDerivedCategory.{u} (ModuleCat.{u} F) :=
  HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u} F)

/-- The actual recorded point fibre, lifted only in carrier size. Source: blueprint order 1509
(blueprint: def-real-lisse-realization-data). -/
def fibre : Raw D l hl E (point D l hl) ⥤ ModuleCat.{u + 1} E :=
  pointRationalFibre D l hl E ⋙ (DerivedCategory.pointFiniteDimensional E).ι ⋙
    DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) 0 ⋙ ModuleCat.uliftFunctor.{u + 1, u} E

/-- Point evaluation agrees naturally with the specified fibre and scalar-extension model.
Source: BS 6.8.2; blueprint point fibre convention
(blueprint: def-real-lisse-realization-data). -/
structure PointAt (a : At D l hl E (point D l hl)) where
  degree_zero : ∀ (K : Raw D l hl E (point D l hl)), Lisse D l hl E (point D l hl) K →
    Nonempty (((pointRationalFibre D l hl E).obj K).obj ≅
      (DerivedCategory.singleFunctor.{u} (ModuleCat.{u} E) 0).obj
        ((DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) 0).obj
          ((pointRationalFibre D l hl E).obj K).obj))
  comparison : (Lisse D l hl E (point D l hl)).ι ⋙ fibre D l hl E ≅
    (Lisse D l hl E (point D l hl)).ι ⋙ a.sheaf D l hl E ⋙ sections D l hl E

/-- The distinguished inverse-image coprojection at the point, in base-change coordinates.
Source: Stacks 00WX; blueprint restriction/coprojection formula
(blueprint: def-real-lisse-realization-data). -/
def pointCoprojection (h : (point D l hl).scheme ⟶ (point D l hl).scheme) :
    ProEt.mk (𝟙 (point D l hl).scheme) ⟶
      (proEtaleBaseChange h).obj (ProEt.mk (𝟙 (point D l hl).scheme)) :=
  MorphismProperty.Over.homMk
    (pullback.lift h (𝟙 _) (by
      change h ≫ 𝟙 _ = 𝟙 _ ≫ h
      simp only [Category.comp_id, Category.id_comp]))
    (pullback.lift_snd _ _ _) trivial

/-- Restriction and the inverse-image coprojection, followed by tensor with one.
This is a section function, before the assertion of its E-linearity.
Source: blueprint point-transport paragraph
(blueprint: def-real-lisse-realization-data). -/
def ordinaryPointTransport
    (h : (point D l hl).scheme ⟶ (point D l hl).scheme)
    (M : Modules D l hl E (point D l hl))
    (m : (sections D l hl E).obj M) :
    (sections D l hl E).obj ((ordinaryPull l E h).obj M) :=
  ((ordinaryPull l E h).obj M).val.map (pointCoprojection D l hl h).op
    (ContinuousRational.moduleUnit h (coefficientPull l E h) M (ProEt.mk (𝟙 _)) m)

/-- H0 of the large rational sections model, to retain the exact prescribed transport.
Source: blueprint point-fibre convention
(blueprint: def-real-lisse-realization-data). -/
def largeFibre (K : Raw D l hl E (point D l hl)) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} E) 0).obj
    ((pointModuleDerivedRationalization l E).obj
      ((pointCompletedDerivedSections D.k l E).obj K.obj.obj))

/-- Carrier lift of the recorded fibre, followed by its specified normalization.
Source: blueprint point-fibre convention
(blueprint: def-real-lisse-realization-data). -/
def fibreNormalization (K : Raw D l hl E (point D l hl)) :
    (fibre D l hl E).obj K ≅ largeFibre D l hl E K :=
  ((ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategoryHomologyFunctorIso 0).app
      ((pointRationalFibre D l hl E).obj K).obj ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} E) 0).mapIso
      (pointRationalNormalization D l hl E K)

/-- The recorded restriction-and-kappa arrow for every automorphism of the point.
The integral pullback target is kept explicit, with the raw object equality inserted later.
Source: blueprint point-transport paragraph
(blueprint: def-real-lisse-realization-data). -/
def transport (h : (point D l hl).scheme ⟶ (point D l hl).scheme) [IsIso h]
    (K : Raw D l hl E (point D l hl)) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} E) 0).map
    ((pointModuleDerivedRationalization l E).map (pointTransport D l hl E h K.obj.obj))

/-- The point square is fixed on every section, and hence also on every iterated transport.
Source: blueprint point-transport paragraph; BS 6.8.15
(blueprint: def-real-lisse-realization-data). -/
structure TransportAt (a : At D l hl E (point D l hl)) (p : PointAt D l hl E a)
    (h : (point D l hl).scheme ⟶ (point D l hl).scheme) [IsIso h]
    (ah : Along D l hl E h a a) where
  target : ∀ K : Raw D l hl E (point D l hl),
    ((pointModuleDerivedRationalization l E).obj
      ((pointCompletedDerivedSections D.k l E).obj
        ((pull D l hl E h).obj K).obj.obj)) ≅
    ((pointModuleDerivedRationalization l E).obj
      ((pointCompletedDerivedSections D.k l E).obj
        ((integralDerivedPullback l E h).obj K.obj.obj)))
  target_normalization : ∀ K : Raw D l hl E (point D l hl),
    HEq (target K).hom (𝟙 ((pointModuleDerivedRationalization l E).obj
      ((pointCompletedDerivedSections D.k l E).obj
        ((integralDerivedPullback l E h).obj K.obj.obj))))
  square : ∀ (K : Raw D l hl E (point D l hl)) (hK : Lisse D l hl E (point D l hl) K)
    (z : (fibre D l hl E).obj K),
    (ordinaryPointTransport D l hl E h ((a.sheaf D l hl E).obj K)
        ((p.comparison.hom.app ⟨K, hK⟩) z)) =
      ((sections D l hl E).map (ah.comparison K hK).hom)
        ((p.comparison.hom.app ⟨(pull D l hl E h).obj K, ah.preserves K hK⟩)
          ((fibreNormalization D l hl E ((pull D l hl E h).obj K)).inv
            (((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} E) 0).map
              (target K).inv)
              ((transport D l hl E h K) ((fibreNormalization D l hl E K).hom z)))))

/-- Pure sections in the actual ordinary sheaf tensor.
Source: Stacks 03EK (blueprint: def-real-lisse-realization-data). -/
def pure {X : Base D l hl} (M N : Modules D l hl E X) (U : X.scheme.ProEtᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) : (M ⊗ N).val.obj U :=
  ((SheafOfModules.tensorObjIsoSheafification
    (R := rationalCoefficientSheaf l X.scheme E) M N).inv.val.app U)
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((adicLisseForget X.scheme).obj (rationalCoefficientSheaf l X.scheme E)).obj)).unit.app
        (M.val ⊗ N.val)).app U (m ⊗ₜ[(rationalCoefficientSheaf l X.scheme E).obj.obj U] n))

/-- Ordinary extension composes by multiplying its two scalar factors.
Source: BS 6.8.2 (blueprint: def-real-lisse-realization-data). -/
structure FieldComposition (G : Type u) [Field G] [Algebra ℚ_[l] G]
    [FiniteDimensional ℚ_[l] G] (i : E →ₐ[ℚ_[l]] F) (j : F →ₐ[ℚ_[l]] G)
    (X : Base D l hl) (aE : At D l hl E X) (aF : At D l hl F X)
    (aG : At D l hl G X) (bEF : FieldChange D l hl E F i X aE aF)
    (bFG : FieldChange D l hl F G j X aF aG)
    (bEG : FieldChange D l hl E G (j.comp i) X aE aG) where
  coefficient : bEF.coefficient ≫ bFG.coefficient = bEG.coefficient
  ordinary : pbcExtend bEF.coefficient ⋙ pbcExtend bFG.coefficient ≅
    pbcExtend bEG.coefficient
  sections : ∀ (M : Modules D l hl E X) (U : X.scheme.ProEtᵒᵖ)
    (b : (rationalCoefficientSheaf l X.scheme F).obj.obj U)
    (c : (rationalCoefficientSheaf l X.scheme G).obj.obj U) (m : M.val.obj U),
    (ordinary.hom.app M).val.app U
      (pbcTensorSection bFG.coefficient ((pbcExtend bEF.coefficient).obj M) U c
        (pbcTensorSection bEF.coefficient M U b m)) =
      pbcTensorSection bEG.coefficient M U (c * bFG.coefficient.hom.app U b) m
  compatibility : ∀ (K : Raw D l hl E X) (hK : Lisse D l hl E X K),
    (aG.sheaf D l hl G).map
        ((sfRationalScalarComp l E F i X.scheme D.p hl G j).hom.app K) ≫
        (bEG.comparison K hK).hom =
      (bFG.comparison _ (bEF.preserves K hK)).hom ≫
        (pbcExtend bFG.coefficient).map (bEF.comparison K hK).hom ≫
          ordinary.hom.app ((aE.sheaf D l hl E).obj K)

/-- Coefficient extension commutes with pullback through the same balanced section map.
Source: BS 6.8.15 (blueprint: def-real-lisse-realization-data). -/
structure Mixed (i : E →ₐ[ℚ_[l]] F) {X Y : Base D l hl} (f : X.scheme ⟶ Y.scheme)
    (aXE : At D l hl E X) (aYE : At D l hl E Y)
    (aXF : At D l hl F X) (aYF : At D l hl F Y)
    (afE : Along D l hl E f aXE aYE) (afF : Along D l hl F f aXF aYF)
    (bX : FieldChange D l hl E F i X aXE aXF)
    (bY : FieldChange D l hl E F i Y aYE aYF) where
  ordinary : pbcExtend bY.coefficient ⋙ ordinaryPull l F f ≅
    ordinaryPull l E f ⋙ pbcExtend bX.coefficient
  sections : ∀ (M : Modules D l hl E Y) (U : Y.scheme.ProEt)
    (b : (rationalCoefficientSheaf l Y.scheme F).obj.obj (op U)) (m : M.val.obj (op U)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
      (ContinuousRational.moduleUnit f (coefficientPull l F f)
        ((pbcExtend bY.coefficient).obj M) U (pbcTensorSection bY.coefficient M (op U) b m)) =
      pbcTensorSection bX.coefficient ((ordinaryPull l E f).obj M)
        (op ((proEtaleBaseChange f).obj U))
        (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
          (coefficientPull l F f)).hom.app (op U) b)
        (ContinuousRational.moduleUnit f (coefficientPull l E f) M U m)
  compatibility : ∀ (K : Raw D l hl E Y) (hK : Lisse D l hl E Y K),
    (aXF.sheaf D l hl F).map
        ((rationalPullbackScalarComparison l E F i f).hom.app K) ≫
        (afF.comparison _ (bY.preserves K hK)).hom ≫
        (ordinaryPull l F f).map (bY.comparison K hK).hom ≫
        ordinary.hom.app ((aYE.sheaf D l hl E).obj K) =
      (bX.comparison _ (afE.preserves K hK)).hom ≫
        (pbcExtend bX.coefficient).map (afE.comparison K hK).hom

/-- Tensor comparison under finite extension, fixed on pure sections.
Source: BS 6.8.15 (blueprint: def-real-lisse-realization-data). -/
structure FieldTensor (i : E →ₐ[ℚ_[l]] F) (X : Base D l hl)
    (aE : At D l hl E X) (aF : At D l hl F X)
    (tE : TensorAt D l hl E X aE) (tF : TensorAt D l hl F X aF)
    (b : FieldChange D l hl E F i X aE aF) where
  ordinary : ∀ M N : Modules D l hl E X,
    ((pbcExtend b.coefficient).obj (M ⊗ N) ≅
      ((pbcExtend b.coefficient).obj M ⊗ (pbcExtend b.coefficient).obj N))
  sections : ∀ (M N : Modules D l hl E X) (U : X.scheme.ProEtᵒᵖ)
    (c d : (rationalCoefficientSheaf l X.scheme F).obj.obj U)
    (m : M.val.obj U) (n : N.val.obj U),
    (ordinary M N).inv.val.app U
      (pure D l hl F _ _ U (pbcTensorSection b.coefficient M U c m)
        (pbcTensorSection b.coefficient N U d n)) =
      pbcTensorSection b.coefficient (M ⊗ N) U (c * d) (pure D l hl E M N U m n)
  compatibility : ∀ (K L : Raw D l hl E X)
    (hK : Lisse D l hl E X K) (hL : Lisse D l hl E X L),
    (aF.sheaf D l hl F).map
        ((rationalTensorScalarComparison l E F i X.scheme).hom.app (K, L)) ≫
        (tF.tensor _ _ (b.preserves K hK) (b.preserves L hL)).hom ≫
        ((b.comparison K hK).hom ⊗ₘ (b.comparison L hL).hom) =
      (b.comparison _ (tE.tensor_mem K L hK hL)).hom ≫
        (pbcExtend b.coefficient).map (tE.tensor K L hK hL).hom ≫
          (ordinary ((aE.sheaf D l hl E).obj K) ((aE.sheaf D l hl E).obj L)).hom

/-- Pullback commutes with ordinary tensor on the canonical pulled-back generators.
Source: BS 6.8.15 (blueprint: def-real-lisse-realization-data). -/
structure PullTensor {X Y : Base D l hl} (f : X.scheme ⟶ Y.scheme)
    (aX : At D l hl E X) (aY : At D l hl E Y)
    (tX : TensorAt D l hl E X aX) (tY : TensorAt D l hl E Y aY)
    (af : Along D l hl E f aX aY) where
  ordinary : ∀ M N : Modules D l hl E Y,
    ((ordinaryPull l E f).obj (M ⊗ N) ≅
      ((ordinaryPull l E f).obj M ⊗ (ordinaryPull l E f).obj N))
  sections : ∀ (M N : Modules D l hl E Y) (U : Y.scheme.ProEt)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)),
    (ordinary M N).hom.val.app (op ((proEtaleBaseChange f).obj U))
      (ContinuousRational.moduleUnit f (coefficientPull l E f) (M ⊗ N) U
        (pure D l hl E M N (op U) m n)) =
      pure D l hl E _ _ (op ((proEtaleBaseChange f).obj U))
        (ContinuousRational.moduleUnit f (coefficientPull l E f) M U m)
        (ContinuousRational.moduleUnit f (coefficientPull l E f) N U n)
  compatibility : ∀ (K L : Raw D l hl E Y)
    (hK : Lisse D l hl E Y K) (hL : Lisse D l hl E Y L),
    (aX.sheaf D l hl E).map (canonicalRationalPullbackTensor l E f K L).inv ≫
        (af.comparison _ (tY.tensor_mem K L hK hL)).hom ≫
        (ordinaryPull l E f).map (tY.tensor K L hK hL).hom ≫
        (ordinary _ _).hom =
      (tX.tensor _ _ (af.preserves K hK) (af.preserves L hL)).hom ≫
        ((af.comparison K hK).hom ⊗ₘ (af.comparison L hL).hom)

/-- The complete finite-field family, with one coherent choice of normalized comparisons.
Source: BS 6.8.14(2), 6.8.15 (blueprint: def-real-lisse-realization-data). -/
structure Family where
  realization : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (X : Base D l hl), At D l hl A X
  tensor : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (X : Base D l hl), TensorAt D l hl A X (realization A X)
  along : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {X Y : Base D l hl} (f : X.scheme ⟶ Y.scheme),
    Along D l hl A f (realization A X) (realization A Y)
  composition : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {X Y Z : Base D l hl} (f : X.scheme ⟶ Y.scheme) (g : Z.scheme ⟶ X.scheme),
    Composition D l hl A f g (realization A X) (realization A Y) (realization A Z)
      (along A f) (along A g) (along A (g ≫ f))
  identity : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (X : Base D l hl),
    Identity D l hl A X (realization A X) (along A (𝟙 X.scheme))
  fieldChange : ∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (X : Base D l hl),
    FieldChange D l hl A B i X (realization A X) (realization B X)
  fieldComposition : ∀ (A B C : Type u) [Field A] [Field B] [Field C]
    [Algebra ℚ_[l] A] [Algebra ℚ_[l] B] [Algebra ℚ_[l] C]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B] [FiniteDimensional ℚ_[l] C]
    (i : A →ₐ[ℚ_[l]] B) (j : B →ₐ[ℚ_[l]] C) (X : Base D l hl),
    FieldComposition D l hl A B C i j X (realization A X) (realization B X) (realization C X)
      (fieldChange A B i X) (fieldChange B C j X) (fieldChange A C (j.comp i) X)
  mixed : ∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) {X Y : Base D l hl} (f : X.scheme ⟶ Y.scheme),
    Mixed D l hl A B i f (realization A X) (realization A Y) (realization B X) (realization B Y)
      (along A f) (along B f) (fieldChange A B i X) (fieldChange A B i Y)
  fieldTensor : ∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (X : Base D l hl),
    FieldTensor D l hl A B i X (realization A X) (realization B X) (tensor A X) (tensor B X)
      (fieldChange A B i X)
  pullTensor : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {X Y : Base D l hl} (f : X.scheme ⟶ Y.scheme),
    PullTensor D l hl A f (realization A X) (realization A Y) (tensor A X) (tensor A Y) (along A f)
  point : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A],
    PointAt D l hl A (realization A (LisseRealization.point D l hl))
  transport : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (h : (LisseRealization.point D l hl).scheme ⟶ (LisseRealization.point D l hl).scheme)
    [IsIso h], TransportAt D l hl A (realization A (LisseRealization.point D l hl)) (point A) h
      (along A h)

variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Ordinary module sheaves at a finite subfield of the algebraic closure.
Source: blueprint common-stage convention (blueprint: def-real-lisse-realization-data). -/
abbrev StageModules (X : Base D l hl) (i : AlgebraicallyClosedCoefficients.Index l Ω) :=
  Modules D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) X

/-- A common-stage realization with transitions given by ordinary scalar extension.
The induced functor uses the existing quotient of representatives. Its exact image condition
and Hom bijections concern the lisse heart; no global lattice is selected.
Source: BS 6.8.2, 6.8.14--6.8.15 and blueprint common-stage clause
(blueprint: def-real-lisse-realization-data). -/
structure CommonStage (a : Family D l hl) (X : Base D l hl) where
  system : StageSystem (StageModules D l hl Ω X)
  transition : ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j),
    system.T h = pbcExtend
      (a.fieldChange (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) X).coefficient
  comparison : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X.scheme).Morphism system
  stages : ∀ i : AlgebraicallyClosedCoefficients.Index l Ω,
    comparison.Φ i = (a.realization (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) X).sheaf
      D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
  fully_faithful : ∀ K L : generalAlgebraicallyClosedConstructibleCategory l Ω X.scheme,
    sfCommonStageHeartProperty l X.scheme Ω K → IsCommonStageLisse l Ω X.scheme K →
    sfCommonStageHeartProperty l X.scheme Ω L → IsCommonStageLisse l Ω X.scheme L →
    Function.Bijective (comparison.functor.map : (K ⟶ L) → _)
  image : ∀ M : system.PairCategory,
    (∃ (i : AlgebraicallyClosedCoefficients.Index l Ω) (N : StageModules D l hl Ω X i),
      N.IsFiniteLocallyFree ∧ Nonempty (M ≅ (system.ι i).obj N)) ↔
    ∃ K : generalAlgebraicallyClosedConstructibleCategory l Ω X.scheme,
      sfCommonStageHeartProperty l X.scheme Ω K ∧ IsCommonStageLisse l Ω X.scheme K ∧
        Nonempty (comparison.functor.obj K ≅ M)

end WeilConjectures.LisseRealization
