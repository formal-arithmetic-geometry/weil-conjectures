/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q130
-/
module

public import Sheaf.Paper.CurveMiddleExtension
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfImmersionCompletedPullbackComparison
public import Sheaf.Paper.SfOpenClosedTriangleAllStages
public import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.Paper.A1QbarOpenClosedCohomology
import Sheaf.Paper.CommonStageCurveWeilMiddleExtension

/-! # Constructibility of the ordinary adic middle extension

Source: blueprint main-20261015, sec-deligne-laumon-a1/sk-i-dl-a1-local,
prop-a1-curve-boundary-sequence.proof.md, first and finite-boundary sentences;
Bhatt--Scholze, Section 6.8
(blueprint: lem-a1-adic-middle-extension-constructible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

section CanonicalComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary inverse image of completed module sheaves, with the published
finite-projection-normalized coefficient map. Source: Stacks 03D2 and BS 6.8
(blueprint: lem-a1-adic-middle-extension-constructible). -/
abbrev adicOrdinaryPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleRingModulePullback f (completedIntegralCommRingSheafUnrestricted l E Y)
    (completedIntegralCommRingSheafUnrestricted l E X)
    (asIso (sfRecollementCoefficientMap l E f))

/-- Its ordinary right adjoint, retaining the same specified coefficient comparison.
Source: Stacks 03D2 (blueprint: lem-a1-adic-middle-extension-constructible). -/
abbrev adicOrdinaryPush {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleRingModuleDirectImage f (completedIntegralCommRingSheafUnrestricted l E Y)
    (completedIntegralCommRingSheafUnrestricted l E X)
    (asIso (sfRecollementCoefficientMap l E f))

/-- The Roos augmentation of ordinary inverse image is fixed by its two cone
coordinates and every tensor-unit generator. Source: Stacks 03D2, 08TC; BS 6.8
(blueprint: lem-a1-adic-middle-extension-constructible).
Proof: send the inverse-image unit of x to the inverse-image unit of 1 tensor x
in every finite reduction. These maps commute with reduction transitions, so their
product is killed by 1-s. Use this product in the first cone coordinate and zero
in the second. This gives a chain map naturally in P. Adjunction-unit generators
locally generate module inverse image; the two cone coordinates jointly determine
a chain map. Thus these equations also prove uniqueness. -/
theorem adicPullAugmentation_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! η : (adicOrdinaryPull l E f).mapHomologicalComplex (.up ℤ) ⟶
        integralOperationsPullbackComplexFunctor l E f,
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ)
        (i : ℤ) (n : ℕ) (V : Y.ProEt) (x : (P.X i).val.obj (op V)),
        (((η.app P).f i ≫
            (CochainComplex.mappingCocone.fst
              (towerTransitionEndomorphism
                (K := fun n ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj
                  (op n))
                (integralOperationsTowerStep
                  ((integralOperationsPullbackTowerFunctor l E f).obj P)))).f i ≫
            (Pi.π (fun n ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj
              (op n)) n).f i).val.app (op ((proEtaleBaseChange f).obj V)))
          (proEtaleRingModuleUnitSection f
            (completedIntegralCommRingSheafUnrestricted l E Y)
            (completedIntegralCommRingSheafUnrestricted l E X)
            (asIso (sfRecollementCoefficientMap l E f)) (P.X i) V x) =
          integralOperationsPullbackGenerator l E f n
            (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
            (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x)) ∧
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ),
        (η.app P).f i ≫
          (CochainComplex.mappingCocone.snd
            (towerTransitionEndomorphism
              (K := fun n ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj
                (op n))
              (integralOperationsTowerStep
                ((integralOperationsPullbackTowerFunctor l E f).obj P)))).v
                  i (i - 1) (by omega) = 0 := by
  sorry

/-- The uniquely generator-normalized augmentation, not an arbitrary comparison.
Source: Stacks 03D2, 08TC (blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicPullAugmentation {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (adicPullAugmentation_existsUnique l E f).exists.choose

/-- On constructible complete objects, immersion pullback is ordinary exact
inverse image. The equation fixes its comparison on every flat K-flat representative.
Source: BS 6.8 and Stacks 08TC
(blueprint: lem-a1-adic-middle-extension-constructible).
Proof: immersion inverse image preserves countable products. Pull the completion
Roos triangle through this exact functor. The generator-normalized augmentation
above is its completion unit, hence is invertible on complete objects. Compose
with integralDerivedPullbackComparison on good complexes and descend through
K-flat localization. The displayed equality fixes every component on resolutions,
so naturality and resolution independence prove uniqueness. -/
theorem adicPullComparison_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsImmersion f] :
    ∃! a : (sfIntegralConstructible l E Y).ι ⋙ integralDerivedPullback l E f ≅
        (sfIntegralConstructible l E Y).ι ⋙ (adicOrdinaryPull l E f).mapDerivedCategory,
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ)
        (hP : integralOperationsGoodComplex l E Y P)
        (hK : sfIntegralConstructible l E Y (DerivedCategory.Q.obj P)),
        a.hom.app ⟨DerivedCategory.Q.obj P, hK⟩ ≫
            (adicOrdinaryPull l E f).mapDerivedCategoryFactors.hom.app P ≫
            DerivedCategory.Q.map ((adicPullAugmentation l E f).app P) =
          (integralDerivedPullbackComparison l E f).hom.app ⟨P, hP⟩ := by
  sorry

/-- The comparison determined on representatives by the actual Roos unit.
Source: BS 6.8 (blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicPullComparison {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] :=
  (adicPullComparison_existsUnique l E f).exists.choose

/-- Site base-change comparison for a square commuting with two automorphisms.
Source: the Frobenius-reindexing step of the blueprint boundary-sequence proof
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicSquareSites {X Y : Scheme.{u}} (f : X ⟶ Y)
    (gX : Aut X) (gY : Aut Y) (w : gX.hom ≫ f = f ≫ gY.hom) :
    proEtaleBaseChange f ⋙ proEtaleBaseChange gX.hom ≅
      proEtaleBaseChange gY.hom ⋙ proEtaleBaseChange f :=
  (MorphismProperty.Over.pullbackComp gX.hom f).symm ≪≫
    eqToIso (congrArg (fun h ↦ proEtaleBaseChange h) w) ≪≫
      MorphismProperty.Over.pullbackComp f gY.hom

/-- Direct-image reindexing is fixed on each section by the actual fibre-product
pasting map. Source: Stacks 03D8 and the blueprint Frobenius step
(blueprint: lem-a1-adic-middle-extension-constructible).
Proof: precomposition evaluates the two images on the two iterated fibre products.
Pasting identifies them. Finite-projection normalization of the coefficient maps
makes this identification linear. Restrictions commute with pasting, yielding a
natural isomorphism. The displayed values specify every section map uniquely. -/
theorem adicSquarePush_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    (gX : Aut X) (gY : Aut Y) (w : gX.hom ≫ f = f ≫ gY.hom) :
    ∃! d : adicOrdinaryPush l E f ⋙ adicOrdinaryPush l E gY.hom ≅
        adicOrdinaryPush l E gX.hom ⋙ adicOrdinaryPush l E f,
      ∀ (M : scalarReductionSource l E X) (V : Y.ProEt)
        (x : M.val.obj (op ((proEtaleBaseChange f).obj
          ((proEtaleBaseChange gY.hom).obj V)))),
        (d.hom.app M).val.app (op V) x =
          M.val.map ((adicSquareSites f gX gY w).hom.app V).op x := by
  sorry

/-- The section-normalized direct-image square.
Source: Stacks 03D8 (blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicSquarePush {X Y : Scheme.{u}} (f : X ⟶ Y)
    (gX : Aut X) (gY : Aut Y) (w : gX.hom ≫ f = f ≫ gY.hom) :=
  (adicSquarePush_existsUnique l E f gX gY w).exists.choose

/-- Inverse-image commutation is the counit mate of actual section reindexing,
using the published tensor-unit-normalized module adjunctions.
Source: Stacks 03D8 (blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicSquareModule {X Y : Scheme.{u}} (f : X ⟶ Y)
    (gX : Aut X) (gY : Aut Y) (w : gX.hom ≫ f = f ≫ gY.hom) :
    adicOrdinaryPull l E gY.hom ⋙ adicOrdinaryPull l E f ≅
      adicOrdinaryPull l E f ⋙ adicOrdinaryPull l E gX.hom :=
  ((conjugateIsoEquiv
    ((sfRecollementModuleAdjunction l E gY.hom).comp
      (sfRecollementModuleAdjunction l E f))
    ((sfRecollementModuleAdjunction l E f).comp
      (sfRecollementModuleAdjunction l E gX.hom))).symm
        (adicSquarePush l E f gX gY w)).symm

/-- The module square acts on every degree of an ordinary complex.
Source: Stacks 015F, blueprint Frobenius step
(blueprint: lem-a1-adic-middle-extension-constructible).
Proof: apply the module square in each degree. Its naturality for the differential
is the chain-map identity. The inverse is degreewise its inverse. Naturality on
complexes and uniqueness both follow degreewise. -/
theorem adicSquareComplex_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    (gX : Aut X) (gY : Aut Y) (w : gX.hom ≫ f = f ≫ gY.hom) :
    ∃! e : (adicOrdinaryPull l E gY.hom).mapHomologicalComplex (.up ℤ) ⋙
          (adicOrdinaryPull l E f).mapHomologicalComplex (.up ℤ) ≅
        (adicOrdinaryPull l E f).mapHomologicalComplex (.up ℤ) ⋙
          (adicOrdinaryPull l E gX.hom).mapHomologicalComplex (.up ℤ),
      ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ) (i : ℤ),
        (e.hom.app P).f i = (adicSquareModule l E f gX gY w).hom.app (P.X i) := by
  sorry

/-- The uniquely degreewise normalized square on ordinary complexes.
Source: Stacks 015F (blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicSquareComplex {X Y : Scheme.{u}} (f : X ⟶ Y)
    (gX : Aut X) (gY : Aut Y) (w : gX.hom ≫ f = f ≫ gY.hom) :=
  (adicSquareComplex_existsUnique l E f gX gY w).exists.choose

/-- The same square on the derived localization retains its representative equation.
Source: Stacks 015F, 06YS (blueprint: lem-a1-adic-middle-extension-constructible).
Proof: all ordinary inverse-image functors here are exact. Their termwise functors
invert quasi-isomorphisms. Descend the uniquely normalized complex square along Q.
The factorization equation specifies the value on every representative; localization
naturality proves existence and uniqueness on every roof. -/
theorem adicSquareDerived_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    (gX : Aut X) (gY : Aut Y) (w : gX.hom ≫ f = f ≫ gY.hom) :
    ∃! e : (adicOrdinaryPull l E gY.hom).mapDerivedCategory ⋙
          (adicOrdinaryPull l E f).mapDerivedCategory ≅
        (adicOrdinaryPull l E f).mapDerivedCategory ⋙
          (adicOrdinaryPull l E gX.hom).mapDerivedCategory,
      ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
        (adicOrdinaryPull l E f).mapDerivedCategory.map
            ((adicOrdinaryPull l E gY.hom).mapDerivedCategoryFactors.hom.app P) ≫
          (adicOrdinaryPull l E f).mapDerivedCategoryFactors.hom.app
            (((adicOrdinaryPull l E gY.hom).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((adicSquareComplex l E f gX gY w).hom.app P) =
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (adicOrdinaryPull l E gX.hom).mapDerivedCategory.map
            ((adicOrdinaryPull l E f).mapDerivedCategoryFactors.hom.app P) ≫
          (adicOrdinaryPull l E gX.hom).mapDerivedCategoryFactors.hom.app
            (((adicOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P) := by
  sorry

/-- The derived square with its exact representative normalization.
Source: Stacks 06YS (blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicSquareDerived {X Y : Scheme.{u}} (f : X ⟶ Y)
    (gX : Aut X) (gY : Aut Y) (w : gX.hom ≫ f = f ≫ gY.hom) :=
  (adicSquareDerived_existsUnique l E f gX gY w).exists.choose

/-- Completed constructible inverse images commute with the given automorphisms,
through the normalized ordinary square and normalized Roos comparisons.
Source: BS 6.8, blueprint Frobenius step
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicSquareIntegral {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (gX : Aut X) (gY : Aut Y) (w : gX.hom ≫ f = f ≫ gY.hom)
    (K : sfIntegralConstructibleCategory l E Y) :
    (constructibleIntegralPullback l E f).obj
        ((constructibleIntegralPullback l E gY.hom).obj K) ≅
      (constructibleIntegralPullback l E gX.hom).obj
        ((constructibleIntegralPullback l E f).obj K) :=
  ObjectProperty.isoMk _
    ((adicPullComparison l E f).app ((constructibleIntegralPullback l E gY.hom).obj K) ≪≫
      (adicOrdinaryPull l E f).mapDerivedCategory.mapIso
        ((adicPullComparison l E gY.hom).app K) ≪≫
      (adicSquareDerived l E f gX gY w).app K.obj ≪≫
      (adicOrdinaryPull l E gX.hom).mapDerivedCategory.mapIso
        ((adicPullComparison l E f).app K).symm ≪≫
      ((adicPullComparison l E gX.hom).app
        ((constructibleIntegralPullback l E f).obj K)).symm)

/-- Ordinary restriction of ordinary open direct image has its actual adjunction
counit as an isomorphism. Source: Stacks 03DI, BS 6.8
(blueprint: lem-a1-adic-middle-extension-constructible).
Proof: on the open subsite every test object is already an object over the open.
The counit evaluates a section on that same object, hence is the identity in these
coordinates. The inverse is its unit inclusion. These identifications respect the
specified coefficient map and all restrictions. -/
@[instance] theorem adicOpenCounit_isIso {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : scalarReductionSource l E X) :
    IsIso ((sfRecollementModuleAdjunction l E j).counit.app M) := by
  sorry

end CanonicalComparison

/-- Geometric base change of the open immersion, without choosing another model.
Source: the geometric immersion pair in the blueprint boundary-sequence proof
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionOpen {D : FiniteFieldDatum.{u}} (c : MiddleExtensionCurve D) :
    (D.geometricFiber c.U).left ⟶ (D.geometricFiber c.C).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map c.j).left

/-- Geometric hypotheses needed by the recorded lisse coefficient category.
Source: the blueprint boundary-sequence proof and its base-change step
(blueprint: lem-a1-adic-middle-extension-constructible).
Proof: separatedness and finite type are stable under base change. Finite type over
k implies Noetherianness. Smoothness is stable under base change, and a dense open
stays dense along the open geometric projection. This includes empty and disconnected
curves; neither properness nor connectedness is used. -/
theorem adicMiddleExtension_geometric_properties {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) :
    IsNoetherian (D.geometricFiber c.U).left ∧
      (D.geometricFiber c.U).left.IsSeparated ∧
      IsNoetherian (D.geometricFiber c.C).left ∧
      IsOpenImmersion (adicMiddleExtensionOpen c) ∧
      DenseRange (adicMiddleExtensionOpen c).base := by
  sorry

/-- The geometric open is Noetherian, as a consequence of the curve hypotheses.
Source: the blueprint boundary-sequence proof
(blueprint: lem-a1-adic-middle-extension-constructible). -/
instance adicMiddleExtension_noetherian_open {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) : IsNoetherian (D.geometricFiber c.U).left :=
  (adicMiddleExtension_geometric_properties c).1

/-- The geometric open is separated, as a consequence of the curve hypotheses.
Source: the blueprint boundary-sequence proof
(blueprint: lem-a1-adic-middle-extension-constructible). -/
instance adicMiddleExtension_separated_open {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) : (D.geometricFiber c.U).left.IsSeparated :=
  (adicMiddleExtension_geometric_properties c).2.1

/-- The geometric open immersion, with the inherited instance exposed.
Source: blueprint boundary-sequence proof
(blueprint: lem-a1-adic-middle-extension-constructible). -/
instance adicMiddleExtension_openImmersion {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) : IsOpenImmersion (adicMiddleExtensionOpen c) :=
  (adicMiddleExtension_geometric_properties c).2.2.2.1

/-- The reduced closed complement over the model field, formed from its vanishing
ideal. This is a real closed subscheme, including an empty complement.
Source: Stacks 01J4; blueprint boundary-sequence proof
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionBoundary0 {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) : Over (Spec (.of D.k₀)) :=
  Over.mk ((IdealSheafData.vanishingIdeal
    ⟨(c.j.left.opensRange : Set c.C.left)ᶜ,
      c.j.left.opensRange.isOpen.isClosed_compl⟩).subschemeι ≫ c.C.hom)

/-- The actual closed inclusion of the reduced complement over the model field.
Source: Stacks 01J4 (blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionClosed0 {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) : adicMiddleExtensionBoundary0 c ⟶ c.C :=
  Over.homMk (IdealSheafData.vanishingIdeal
    ⟨(c.j.left.opensRange : Set c.C.left)ᶜ,
      c.j.left.opensRange.isOpen.isClosed_compl⟩).subschemeι rfl

/-- Finite type and quasi-compactness of the reduced boundary are consequences of
its closed inclusion into the finite-type model curve.
Source: Stacks 01J4, 01T6 (blueprint: lem-a1-adic-middle-extension-constructible).
Proof: the vanishing ideal defines the reduced closed immersion. A closed immersion
is finite type and quasi-compact. Compose it with the finite-type quasi-compact
structure morphism of C0. This also handles the empty boundary. -/
theorem adicMiddleExtensionBoundary0_finite {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) :
    LocallyOfFiniteType (adicMiddleExtensionBoundary0 c).hom ∧
      QuasiCompact (adicMiddleExtensionBoundary0 c).hom := by
  sorry

/-- The boundary's finite-type instance, derived from the curve.
Source: Stacks 01T6 (blueprint: lem-a1-adic-middle-extension-constructible). -/
instance adicMiddleExtensionBoundary0_locallyFinite {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) :
    LocallyOfFiniteType (adicMiddleExtensionBoundary0 c).hom :=
  (adicMiddleExtensionBoundary0_finite c).1

/-- The boundary's quasi-compactness instance, derived from the curve.
Source: Stacks 01T6 (blueprint: lem-a1-adic-middle-extension-constructible). -/
instance adicMiddleExtensionBoundary0_quasiCompact {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) : QuasiCompact (adicMiddleExtensionBoundary0 c).hom :=
  (adicMiddleExtensionBoundary0_finite c).2

/-- The actual geometric base change of the reduced closed inclusion.
Source: blueprint boundary-sequence proof
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionClosed {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) :
    (D.geometricFiber (adicMiddleExtensionBoundary0 c)).left ⟶
      (D.geometricFiber c.C).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
    (adicMiddleExtensionClosed0 c)).left

/-- This geometric map is the reduced closed complement of the geometric open.
Source: Stacks 01J4 and the blueprint base-change step
(blueprint: lem-a1-adic-middle-extension-constructible).
Proof: closed immersions and complements commute with base change. The model
boundary is reduced and finite over a perfect field, hence is geometrically
reduced. Its geometric base change is therefore the reduced closed complement.
The range statement follows on the cartesian squares. -/
theorem adicMiddleExtensionClosed_properties {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) :
    IsClosedImmersion (adicMiddleExtensionClosed c) ∧
      IsReduced (D.geometricFiber (adicMiddleExtensionBoundary0 c)).left ∧
      Set.range (adicMiddleExtensionClosed c).base =
        (Set.range (adicMiddleExtensionOpen c).base)ᶜ := by
  sorry

/-- The geometric closed immersion instance, with no new hypothesis.
Source: Stacks 01J4 (blueprint: lem-a1-adic-middle-extension-constructible). -/
instance adicMiddleExtension_closedImmersion {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) : IsClosedImmersion (adicMiddleExtensionClosed c) :=
  (adicMiddleExtensionClosed_properties c).1

/-- Geometric Frobenius commutes with every base-changed map over the finite field.
Source: Weil II 1.1.7; blueprint Frobenius step
(blueprint: lem-a1-adic-middle-extension-constructible).
Proof: the two composites have the same projection to the model and the same
coefficient-field projection, namely geometric field Frobenius. The universal
property of the defining fibre product makes the composites equal. -/
theorem adicGeometricFrobenius_naturality (D : FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    (D.geometricFrobenius X₀).hom ≫
        ((Over.pullback (Spec.map
          (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left =
      ((Over.pullback (Spec.map
          (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left ≫
        (D.geometricFrobenius Y₀).hom := by
  sorry

variable (l : ℕ) [Fact l.Prime] (Ω : Type (u + 1)) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Realize the recorded ordinary image at one coefficient field in the current
intrinsic completed-coefficient presentation. All maps are the published coefficient
restriction, whose ring isomorphism is normalized by every finite quotient projection.
Source: def-wf-middle-extension and the blueprint boundary-sequence proof
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionIntegral {U C : Scheme.{u}} (j : U ⟶ C)
    (E : Padic.FiniteCoefficientFields l Ω) (F : AdicIntegralDiagram l E.val U) :
    DerivedCategory (scalarReductionSource l (pbcFiniteField.{u} l Ω E) C) :=
  (ImmersionCompletedPullback.transport l (pbcFiniteField.{u} l Ω E) C).obj
    (middleExtensionIntegralComplex l Ω E j F)

/-- Lisse adic sheaves on the geometric open, with all domain instances derived
from the given curve and the distinct coefficient prime.
Source: def-wf-middle-extension, geometric-fibre convention
(blueprint: lem-a1-adic-middle-extension-constructible). -/
abbrev adicMiddleExtensionLisse {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p) :=
  letI := adicMiddleExtension_noetherian_open c
  letI := adicMiddleExtension_separated_open c
  letI := fun x ↦ sfWeilPrimeInvertible D l hl c.U x
  LisseAlgebraicSheaf l (D.geometricFiber c.U).left Ω

/-- The finite coefficient pair is retained literally; no model is chosen.
Source: def-wf-middle-extension and its lisse finite-stage convention
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionLissePair {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl) :=
  letI := adicMiddleExtension_noetherian_open c
  letI := adicMiddleExtension_separated_open c
  letI := fun x ↦ sfWeilPrimeInvertible D l hl c.U x
  lisseAlgebraicPair l (D.geometricFiber c.U).left Ω F

/-- The integral lattice already contained in the recorded lisse pair.
Source: def-wf-middle-extension, ordinary coefficient sheaf convention
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionLisseModel {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl) :=
  letI := adicMiddleExtension_noetherian_open c
  letI := adicMiddleExtension_separated_open c
  letI := fun x ↦ sfWeilPrimeInvertible D l hl c.U x
  (lisseCoefficientPairModel l (D.geometricFiber c.U).left Ω
    (adicMiddleExtensionLissePair l Ω c hl F)).integral

/-- The completed integral module of the input finite-stage lisse system, obtained
by the recorded inverse limit and its normalized coefficient transport.
Source: def-wf-middle-extension (blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionLisseModule {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl) :=
  (DerivedCategory.homologyFunctor _ 0).obj
    (adicMiddleExtensionIntegral l Ω (𝟙 (D.geometricFiber c.U).left)
      (adicMiddleExtensionLissePair l Ω c hl F).base
      (adicMiddleExtensionLisseModel l Ω c hl F).obj)

/-- The input module placed in degree zero.
Source: def-wf-middle-extension (blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionInputIntegral {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl) :=
  (DerivedCategory.singleFunctor _ 0).obj (adicMiddleExtensionLisseModule l Ω c hl F)

/-- Ordinary j_* of that module, placed in degree zero before any localization.
Source: def-wf-middle-extension (blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionImageIntegral {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl) :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((adicOrdinaryPush l
      (pbcFiniteField.{u} l Ω (adicMiddleExtensionLissePair l Ω c hl F).base)
      (adicMiddleExtensionOpen c)).obj (adicMiddleExtensionLisseModule l Ω c hl F))

/-- The ordinary-module construction agrees with the recorded finite-level
ordinary image. This is a comparison of explicit objects, not a definition by choice.
Source: def-wf-middle-extension and BS 6.8
(blueprint: lem-a1-adic-middle-extension-constructible).
Proof: both constructions are inverse limits of the same finite lisse systems.
Ordinary direct image preserves limits. Comparison pullback and associated modules
identify the finite-level coefficient presentations; the maps are normalized on
constant coefficient sections. The completed-ring comparison preserves every
finite projection. Degree-zero H0 and the single functor recover the same module.
Taking their limit comparison and placing it in degree zero gives the isomorphism. -/
theorem adicMiddleExtensionImageIntegral_comparison {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl) :
    Nonempty (adicMiddleExtensionImageIntegral l Ω c hl F ≅
      adicMiddleExtensionIntegral l Ω (adicMiddleExtensionOpen c)
        (adicMiddleExtensionLissePair l Ω c hl F).base
        (adicMiddleExtensionLisseModel l Ω c hl F).obj) := by
  sorry

/-- Both actual single-sheaf models are constructible and complete.
Source: the first step of the blueprint boundary-sequence proof; BS 6.8
(blueprint: lem-a1-adic-middle-extension-constructible).
Proof: the given lisse system has finite locally free reductions with a common
bound. Its completion is the input module. Ordinary image of a lisse sheaf along
a dense open of a smooth curve is lisse on the open and constructible at the finite
boundary. Integral inertia invariants are finite modules over the coefficient DVR.
Their finite reductions have a common cohomological interval, including possible
Tor in degree -1. The two modules are complete, so their degree-zero complexes
satisfy sfIntegralConstructible. No higher derived image is substituted. Empty
and disconnected curves cause no exception; connectedness and properness are unused. -/
theorem adicMiddleExtensionIntegral_mem {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl) :
    sfIntegralConstructible l
        (pbcFiniteField.{u} l Ω (adicMiddleExtensionLissePair l Ω c hl F).base)
        (D.geometricFiber c.U).left (adicMiddleExtensionInputIntegral l Ω c hl F) ∧
      sfIntegralConstructible l
        (pbcFiniteField.{u} l Ω (adicMiddleExtensionLissePair l Ω c hl F).base)
        (D.geometricFiber c.C).left (adicMiddleExtensionImageIntegral l Ω c hl F) := by
  sorry

/-- The actual input in the integral full subcategory.
Source: BS 6.8 (blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionInputModel {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl) :
    sfIntegralConstructibleCategory l
      (pbcFiniteField.{u} l Ω (adicMiddleExtensionLissePair l Ω c hl F).base)
      (D.geometricFiber c.U).left :=
  ⟨adicMiddleExtensionInputIntegral l Ω c hl F,
    (adicMiddleExtensionIntegral_mem l Ω c hl F).1⟩

/-- The actual ordinary image in the integral full subcategory.
Source: BS 6.8 (blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionImageModel {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl) :
    sfIntegralConstructibleCategory l
      (pbcFiniteField.{u} l Ω (adicMiddleExtensionLissePair l Ω c hl F).base)
      (D.geometricFiber c.C).left :=
  ⟨adicMiddleExtensionImageIntegral l Ω c hl F,
    (adicMiddleExtensionIntegral_mem l Ω c hl F).2⟩

/-- Include the actual integral model at its finite coefficient stage.
Source: def-weil-constructible-heart
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicStageObject (Y : Scheme.{u}) (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y) :=
  (GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
    ((sfRationalConstructibleLocalization l _ Y).obj K)

/-- Literal finite-stage pullback objects agree with the published common-stage
pullback object formula. Source: def-weil-derived-pullback-tensor-hom
(blueprint: lem-a1-adic-middle-extension-constructible).
Proof: unfold the stage inclusion and use the object clauses of
commonStageDerivedPullback_existsUnique and rationalDerivedPullback_existsUnique.
Their objects retain the original coefficient stage and integral model. -/
theorem adicStagePull_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y) :
    (commonStageDerivedPullback l Ω f).obj (adicStageObject l Ω Y L K) =
      adicStageObject l Ω X L
        ((constructibleIntegralPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).obj K) := by
  sorry

/-- The identity comparison supplied by that literal stage object equality.
Source: def-weil-derived-pullback-tensor-hom
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicStagePullIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y) :=
  eqToIso (adicStagePull_obj l Ω f L K)

/-- Canonical automorphism commutation at a common-stage object. All comparisons
are obtained from the tensor-unit mate on module sections and its normalized Roos
descent; the stage inclusions carry the actual integral arrows.
Source: blueprint Frobenius step
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicSquareCommonStage {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (gX : Aut X) (gY : Aut Y) (w : gX.hom ≫ f = f ≫ gY.hom)
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y) :
    (commonStageDerivedPullback l Ω f).obj
        ((commonStageDerivedPullback l Ω gY.hom).obj (adicStageObject l Ω Y L K)) ≅
      (commonStageDerivedPullback l Ω gX.hom).obj
        ((commonStageDerivedPullback l Ω f).obj (adicStageObject l Ω Y L K)) :=
  (commonStageDerivedPullback l Ω f).mapIso (adicStagePullIso l Ω gY.hom L K) ≪≫
    adicStagePullIso l Ω f L
      ((constructibleIntegralPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) gY.hom).obj K) ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion L).mapIso
      ((sfRationalConstructibleLocalization l _ X).mapIso
        (adicSquareIntegral l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
          f gX gY w K)) ≪≫
    (adicStagePullIso l Ω gX.hom L
      ((constructibleIntegralPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).obj K)).symm ≪≫
    (commonStageDerivedPullback l Ω gX.hom).mapIso (adicStagePullIso l Ω f L K).symm

/-- The input lisse sheaf in the recorded common-stage category, in degree zero.
Source: def-wf-middle-extension (blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionInput {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl) :=
  adicStageObject l Ω (D.geometricFiber c.U).left
    (adicMiddleExtensionLissePair l Ω c hl F).base
    (adicMiddleExtensionInputModel l Ω c hl F)

/-- The ordinary image A=j_*F in the recorded common-stage category, in degree zero.
Source: def-wf-middle-extension (blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionObject {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl) :=
  adicStageObject l Ω (D.geometricFiber c.C).left
    (adicMiddleExtensionLissePair l Ω c hl F).base
    (adicMiddleExtensionImageModel l Ω c hl F)

/-- The recorded inverse image along j, with coefficient units derived from the
finite-field datum. Source: def-weil-derived-pullback-tensor-hom
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionOpenPull {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl c.U x
  letI := fun x ↦ sfWeilPrimeInvertible D l hl c.C x
  commonStageDerivedPullback l Ω (adicMiddleExtensionOpen c)

/-- The recorded inverse image along the geometric reduced closed complement.
Source: def-weil-derived-pullback-tensor-hom
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionClosedPull {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl (adicMiddleExtensionBoundary0 c) x
  letI := fun x ↦ sfWeilPrimeInvertible D l hl c.C x
  commonStageDerivedPullback l Ω (adicMiddleExtensionClosed c)

/-- The specified B=i^*A, using exactly the published completed inverse image.
Source: blueprint boundary-sequence proof
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionBoundaryObject {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl) :=
  (adicMiddleExtensionClosedPull l Ω c hl).obj (adicMiddleExtensionObject l Ω c hl F)

/-- Integral restriction along j, with its coefficient units derived from the datum.
Source: def-weil-derived-pullback-tensor-hom
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionOpenIntegralPull {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl c.U x
  letI := fun x ↦ sfWeilPrimeInvertible D l hl c.C x
  constructibleIntegralPullback l
    (pbcFiniteField.{u} l Ω (adicMiddleExtensionLissePair l Ω c hl F).base)
    (adicMiddleExtensionOpen c)

/-- Open restriction of A is identified with the input by the actual ordinary
counit, transported through the representative-normalized completed pullback.
Source: Stacks 03DI; blueprint Frobenius step
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionOpenRestrictionIntegral {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl) :
    (adicMiddleExtensionOpenIntegralPull l Ω c hl F).obj
        (adicMiddleExtensionImageModel l Ω c hl F) ≅
      adicMiddleExtensionInputModel l Ω c hl F :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl c.U x
  letI := fun x ↦ sfWeilPrimeInvertible D l hl c.C x
  ObjectProperty.isoMk (sfIntegralConstructible l
    (pbcFiniteField.{u} l Ω (adicMiddleExtensionLissePair l Ω c hl F).base)
    (D.geometricFiber c.U).left)
    ((adicPullComparison l
      (pbcFiniteField.{u} l Ω (adicMiddleExtensionLissePair l Ω c hl F).base)
      (adicMiddleExtensionOpen c)).app (adicMiddleExtensionImageModel l Ω c hl F) ≪≫
      ((adicOrdinaryPull l
        (pbcFiniteField.{u} l Ω (adicMiddleExtensionLissePair l Ω c hl F).base)
        (adicMiddleExtensionOpen c)).mapDerivedCategorySingleFunctor 0).app
          ((adicOrdinaryPush l
            (pbcFiniteField.{u} l Ω (adicMiddleExtensionLissePair l Ω c hl F).base)
            (adicMiddleExtensionOpen c)).obj (adicMiddleExtensionLisseModule l Ω c hl F)) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (asIso ((sfRecollementModuleAdjunction l
          (pbcFiniteField.{u} l Ω (adicMiddleExtensionLissePair l Ω c hl F).base)
          (adicMiddleExtensionOpen c)).counit.app (adicMiddleExtensionLisseModule l Ω c hl F))))

/-- The common-stage open counit, with no new coefficient-stage choice.
Source: Stacks 03DI (blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionOpenRestriction {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl) :
    (adicMiddleExtensionOpenPull l Ω c hl).obj (adicMiddleExtensionObject l Ω c hl F) ≅
      adicMiddleExtensionInput l Ω c hl F :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl c.U x
  letI := fun x ↦ sfWeilPrimeInvertible D l hl c.C x
  adicStagePullIso l Ω (adicMiddleExtensionOpen c)
    (adicMiddleExtensionLissePair l Ω c hl F).base
    (adicMiddleExtensionImageModel l Ω c hl F) ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion _).mapIso
      ((sfRationalConstructibleLocalization l _ _).mapIso
        (adicMiddleExtensionOpenRestrictionIntegral l Ω c hl F))

/-- The canonical commuting pullback square at A for the open immersion.
Source: blueprint Frobenius step
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionOpenFrobenius {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl c.U x
  letI := fun x ↦ sfWeilPrimeInvertible D l hl c.C x
  adicSquareCommonStage l Ω (adicMiddleExtensionOpen c)
    (D.geometricFrobenius c.U) (D.geometricFrobenius c.C)
    (adicGeometricFrobenius_naturality D c.j)
    (adicMiddleExtensionLissePair l Ω c hl F).base
    (adicMiddleExtensionImageModel l Ω c hl F)

/-- The canonical commuting pullback square at A for the reduced closed immersion.
Source: blueprint Frobenius step
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionClosedFrobenius {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl (adicMiddleExtensionBoundary0 c) x
  letI := fun x ↦ sfWeilPrimeInvertible D l hl c.C x
  adicSquareCommonStage l Ω (adicMiddleExtensionClosed c)
    (D.geometricFrobenius (adicMiddleExtensionBoundary0 c)) (D.geometricFrobenius c.C)
    (adicGeometricFrobenius_naturality D (adicMiddleExtensionClosed0 c))
    (adicMiddleExtensionLissePair l Ω c hl F).base
    (adicMiddleExtensionImageModel l Ω c hl F)

/-- Ordinary degree-zero constructibility of A and its boundary inverse image.
Source: blueprint first and finite-boundary sentences; BS 6.8.14--15
(blueprint: lem-a1-adic-middle-extension-constructible).
Proof: the geometric curve satisfies the same smooth, separated, finite-type,
pure-dimension-one hypotheses as the model. The ordinary open image of a lisse
adic sheaf is constructible on this curve; its integral model above is a single
module. Localization and common-stage inclusion put it in both standard halves.
The closed inverse image is exact on ordinary module sheaves, and its comparison
with completed pullback is the normalized immersion comparison. It therefore
remains a single module in degree zero and belongs to both halves on Z. Neither
argument requires a connected or proper curve. The empty boundary gives zero. -/
theorem adicMiddleExtension_heart {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl) :
    sfCommonStageHeartProperty l (D.geometricFiber c.C).left Ω
        (adicMiddleExtensionObject l Ω c hl F) ∧
      sfCommonStageHeartProperty l
        (D.geometricFiber (adicMiddleExtensionBoundary0 c)).left Ω
        (adicMiddleExtensionBoundaryObject l Ω c hl F) := by
  sorry

/-- The ordinary adjunction uniquely determines the induced Weil isomorphism on A.
Its restriction is theta_F, conjugated by the actual open counit and canonical
commuting pullback square. This is precisely j_* theta_F after the automorphism
base-change comparison. Source: blueprint Frobenius step
(blueprint: lem-a1-adic-middle-extension-constructible).
Proof: ordinary j_* is right adjoint to exact j^* on constructible sheaves.
The canonical automorphism square and open counit turn theta_F into a map
j^*g_C^*A to F. Transpose it to g_C^*A to A. Apply the same construction to
its inverse. Their composites restrict to identities; adjunction faithfulness
for maps into j_*F makes them identities. The displayed counit equation fixes
the transpose uniquely, so this gives a unique isomorphism. This construction
works for every common-stage theta_F, whether or not it preserves the input lattice. -/
theorem adicMiddleExtensionWeilIso_existsUnique {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl)
    (theta : (sfCommonStageWeilFrobeniusPullback D l hl c.U Ω).obj
      (adicMiddleExtensionInput l Ω c hl F) ≅ adicMiddleExtensionInput l Ω c hl F) :
    ∃! a : (sfCommonStageWeilFrobeniusPullback D l hl c.C Ω).obj
        (adicMiddleExtensionObject l Ω c hl F) ≅ adicMiddleExtensionObject l Ω c hl F,
      (adicMiddleExtensionOpenPull l Ω c hl).map a.hom ≫
          (adicMiddleExtensionOpenRestriction l Ω c hl F).hom =
        (adicMiddleExtensionOpenFrobenius l Ω c hl F).hom ≫
          (sfCommonStageWeilFrobeniusPullback D l hl c.U Ω).map
            (adicMiddleExtensionOpenRestriction l Ω c hl F).hom ≫ theta.hom := by
  sorry

/-- The unique adjunction-normalized induced Weil isomorphism on the ordinary image.
Source: blueprint Frobenius step
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionWeilIso {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl)
    (theta : (sfCommonStageWeilFrobeniusPullback D l hl c.U Ω).obj
      (adicMiddleExtensionInput l Ω c hl F) ≅ adicMiddleExtensionInput l Ω c hl F) :=
  (adicMiddleExtensionWeilIso_existsUnique l Ω c hl F theta).exists.choose

/-- A with precisely the induced structure, as a fixed pair in the recorded category.
Source: def-weil-weil-sheaf-complex; blueprint Frobenius step
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionWeil {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl)
    (theta : (sfCommonStageWeilFrobeniusPullback D l hl c.U Ω).obj
      (adicMiddleExtensionInput l Ω c hl F) ≅ adicMiddleExtensionInput l Ω c hl F) :
    sfCommonStageWeilComplex D l hl c.C Ω :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk (adicMiddleExtensionObject l Ω c hl F)
    (adicMiddleExtensionWeilIso l Ω c hl F theta)

/-- B with i^* of the induced structure on A, composed with the canonical commuting
square for g_C i = i g_Z. Source: blueprint Frobenius step
(blueprint: lem-a1-adic-middle-extension-constructible). -/
def adicMiddleExtensionBoundaryWeil {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl)
    (theta : (sfCommonStageWeilFrobeniusPullback D l hl c.U Ω).obj
      (adicMiddleExtensionInput l Ω c hl F) ≅ adicMiddleExtensionInput l Ω c hl F) :
    sfCommonStageWeilComplex D l hl (adicMiddleExtensionBoundary0 c) Ω :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk (adicMiddleExtensionBoundaryObject l Ω c hl F)
    ((adicMiddleExtensionClosedFrobenius l Ω c hl F).symm ≪≫
      (adicMiddleExtensionClosedPull l Ω c hl).mapIso
        (adicMiddleExtensionWeilIso l Ω c hl F theta))

/-- The ordinary adic middle extension and its reduced boundary restriction,
with their specified induced Weil structures, lie in the constructible hearts.
Source: blueprint first and finite-boundary sentences; BS 6.8.14--15
(blueprint: lem-a1-adic-middle-extension-constructible).
Proof: adicMiddleExtension_heart gives the two degree-zero heart carriers using
the ordinary image and exact closed inverse image. The canonical open counit
and commuting Frobenius square uniquely induce theta_A by adjunction, exactly
j_*theta_F after automorphism base change. The closed commuting square followed
by i^*theta_A gives theta_B. Both are isomorphisms. The recorded Weil-sheaf
subcategory is the inverse image of the heart under the fixed-pair forgetful
functor, so these two carrier assertions give the stated memberships. -/
theorem adicMiddleExtension_constructible {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : adicMiddleExtensionLisse l Ω c hl)
    (theta : (sfCommonStageWeilFrobeniusPullback D l hl c.U Ω).obj
      (adicMiddleExtensionInput l Ω c hl F) ≅ adicMiddleExtensionInput l Ω c hl F) :
    ((sfCommonStageHeartProperty l (D.geometricFiber c.C).left Ω).inverseImage
        (sfCommonStageWeilForget D l hl c.C Ω))
        (adicMiddleExtensionWeil l Ω c hl F theta) ∧
      ((sfCommonStageHeartProperty l
        (D.geometricFiber (adicMiddleExtensionBoundary0 c)).left Ω).inverseImage
        (sfCommonStageWeilForget D l hl (adicMiddleExtensionBoundary0 c) Ω))
        (adicMiddleExtensionBoundaryWeil l Ω c hl F theta) := by
  sorry

end WeilConjectures
