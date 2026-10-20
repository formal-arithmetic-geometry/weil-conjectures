/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q128
-/
module

public import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
public import Sheaf.AlgebraicGeometry.StrictTowerOpenExtension
public import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.CompletedDirectImageLimits
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.RingedEtaleOriginWitness
public import Sheaf.Paper.StrictTowerExchangeMateNormalization
public import WeilConjectures.Compactification.BaseChange
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Paper.CompletedBaseChangeMap
import Sheaf.Paper.CompletedOpenExchangeTransport
import Sheaf.Paper.PbcActualStrictPullback
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

public import Sheaf.Paper.CompletedCompactSupportExchange
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.Paper.ExactProductFunctorStrictLimit
public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.Paper.ProjectionCompactification
public import Sheaf.Paper.CompleteCompactSupportProetale
import Sheaf.Paper.KoszulReconstruction
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.FlatRingedDiagramRestriction
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.PbcQbarCompletedPullback

/-!
# Strict-tower realization of completed compact-support exchange

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-cbc,
Definition 1939 and the proof of thm-cbc-complete-proetale; Stacks 03DI, 09BP, 0A07
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).

All comparisons below are adjunction mates or their exact derived transports.
The strict composite is constructed before applying either Rlim or evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe t uC vC uD vD
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Pointwise preservation transferred to the finite-limit class.
Source: Mathlib functor-category limits
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
instance cbcRealizationWhiskerLimits {C : Type uC} {D : Type uD} [Category.{vC} C]
    [Category.{vD} D] [HasFiniteLimits C] (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) where
  preservesFiniteLimits _ _ _ := inferInstance

/-- Pointwise preservation transferred to the finite-colimit class.
Source: Mathlib functor-category colimits
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
instance cbcRealizationWhiskerColimits {C : Type uC} {D : Type uD} [Category.{vC} C]
    [Category.{vD} D] [HasFiniteColimits C] (F : C ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) where
  preservesFiniteColimits _ _ _ := inferInstance

/-- Constant-tower/Rlim adjunction for an arbitrary coefficient sheaf.
Source: Stacks 079P (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationLimitAdj (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    (Functor.const ℕᵒᵖ : reductionModules T R ⥤ _).mapDerivedCategory ⊣ completedRlim T R :=
  (constLimAdj : (Functor.const ℕᵒᵖ : reductionModules T R ⥤ _) ⊣
    completedTowerLimit T R).mapDerivedCategoryRightDerivedAdjunction

/-- Exact transport of the identity constant-diagram comparison.
Source: Stacks 079P (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationConst {T S : Scheme.{t}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    {R' : Sheaf (ProEt.topology S) CommRingCat.{t + 1}}
    (F : reductionModules T R ⥤ reductionModules S R') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory ⋙ (Functor.const ℕᵒᵖ).mapDerivedCategory ≅
      (Functor.const ℕᵒᵖ).mapDerivedCategory ⋙
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ F) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The canonical limit comparison, defined by the constant-diagram mate.
This definition fixes its value on resolutions and on strict augmentations.
Source: Stacks 09BP, 0A07
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationLimitMap {T S : Scheme.{t}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    {R' : Sheaf (ProEt.topology S) CommRingCat.{t + 1}}
    (F : reductionModules T R ⥤ reductionModules S R') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    completedRlim T R ⋙ F.mapDerivedCategory ⟶
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapDerivedCategory ⋙ completedRlim S R' :=
  mateEquiv (cbcRealizationLimitAdj T R) (cbcRealizationLimitAdj S R')
    (cbcRealizationConst F).hom

/-- The specified mate is invertible for an exact product-preserving functor.
Source: Stacks 09BP and the normalized strict-limit lemma
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof: apply lem-cbc-exact-product-functor-strict-limit. Its signed Roos formula
is induced by the canonical product map. On a K-injective tower it is the ordinary
limit comparison followed by a target resolution; adjunction transposition shows
that this is exactly cbcRealizationLimitMap. The normalized comparison is invertible,
and its augmentation equation also identifies the constant-diagram mate. -/
theorem cbcRealizationLimitMap_isIso {T S : Scheme.{t}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    {R' : Sheaf (ProEt.topology S) CommRingCat.{t + 1}}
    (F : reductionModules T R ⥤ reductionModules S R') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (_products : ∀ M : ℕ → reductionModules T R, IsIso (piComparison F M)) :
    IsIso (cbcRealizationLimitMap F) := by
  sorry

/-- Restriction of the scalar action on the ordinary module category.
Source: Stacks 03D3 (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
abbrev cbcRealizationRes (T : Scheme.{t}) :=
  proEtaleRingRestrictScalars (exchangeScalar d T)

/-- The recorded open extension adjunction transported by the section-normalized map.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationOpenAdj {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcOpenShriek d j inferInstance ⊣
      proEtaleRingModulePullback j (d.completedRing T) (d.completedRing U)
        (d.integralRingIso j) :=
  Adjunction.ofNatIsoRight (cbcOpenAdjunction d j inferInstance)
    (@asIso _ _ _ _ (cbcPullToRestriction d j) (cbcPullToRestriction_isIso d j)).symm

/-- Termwise completed open extension on strict towers, retaining every transition.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
abbrev cbcRealizationTowerJ {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (cbcOpenShriek d j inferInstance)

/-- The exact derived open functor on completed strict towers.
Source: Stacks 03DJ (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
abbrev cbcRealizationJ {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :=
  (cbcRealizationTowerJ d j).mapDerivedCategory

/-- Derived adjunction on completed towers with the normalized open unit.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationTowerAdj {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcRealizationJ d j ⊣ d.towerPull j :=
  Adjunction.ofNatIsoRight
    ((cbcRealizationOpenAdj d j).whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
    (d.towerModulePull j).rightDerivedFunctorIsoMapDerivedCategory

/-- The inverse tensor/open comparison is the transpose of the reduced open unit.
It is one strict-tower map, not a family of maps in separate derived categories.
Source: Stacks 03DI, 0E8I
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationReductionInv {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : d.derived U) :
    (cbcRealizationJ d j).obj ((completedReductionTower U d).obj K) ⟶
      (completedReductionTower T d).obj ((cbcDerivedOpenShriek d j inferInstance).obj K) :=
  ((cbcRealizationTowerAdj d j).homEquiv _ _).symm
    ((completedReductionTower U d).map ((cbcDerivedOpenAdjunction d j).unit.app K) ≫
      (d.reductionTowerPullbackIso j).inv.app
        ((cbcDerivedOpenShriek d j inferInstance).obj K))

/-- The tensor/open transpose is natural and invertible.
Source: Stacks 03DI, 0E8I
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof: naturality is naturality of the open unit and of the strict reduction/pullback
comparison. On K-flat representatives its evaluation is the sheafified balancing map
j_!(Q) tensor P_n to j_!(Q tensor j^*P_n). Extension preserves K-flatness: tensor
with an acyclic ambient complex is extension of tensor with its exact restriction.
The inverse balancing maps commute with differentials and all quotient transitions.
Thus the inverse exists in the derived category of strict towers itself. -/
theorem cbcRealizationReductionInv_properties {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    (∀ K : d.derived U, IsIso (cbcRealizationReductionInv d j K)) ∧
      ∀ (K L : d.derived U) (k : K ⟶ L),
        (cbcRealizationJ d j).map ((completedReductionTower U d).map k) ≫
            cbcRealizationReductionInv d j L =
          cbcRealizationReductionInv d j K ≫
            (completedReductionTower T d).map
              ((cbcDerivedOpenShriek d j inferInstance).map k) := by
  sorry

/-- The canonical tensor comparison on the full strict quotient tower.
Source: Stacks 0E8I (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationReduction {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : d.derived U) :
    (completedReductionTower T d).obj ((cbcDerivedOpenShriek d j inferInstance).obj K) ≅
      (cbcRealizationJ d j).obj ((completedReductionTower U d).obj K) :=
  (@asIso _ _ _ _ (cbcRealizationReductionInv d j K)
    ((cbcRealizationReductionInv_properties d j).1 K)).symm

/-- Scalar restriction/open extension comparison, defined by the pullback mate.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationScalarOpenInv {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcRealizationRes d U ⋙ ProEtale.StrictTower.moduleJ A j ⟶
      cbcOpenShriek d j inferInstance ⋙ cbcRealizationRes d T :=
  (mateEquiv (cbcRealizationOpenAdj d j) (ProEtale.StrictTower.moduleJAdj A j)).symm
    (@asIso _ _ _ _ (proEtaleRingRestrictionPullbackInv j
      (exchangeConstantRing T A) (d.completedRing T)
      (exchangeConstantRing U A) (d.completedRing U)
      (exchangeScalar d T) (exchangeScalar d U)
      (exchangeConstantIso j A) (d.integralRingIso j) (exchangeScalar_comm d j))
      (proEtaleRingRestrictionPullbackInv_isIso j
        (exchangeConstantRing T A) (d.completedRing T)
        (exchangeConstantRing U A) (d.completedRing U)
        (exchangeScalar d T) (exchangeScalar d U)
        (exchangeConstantIso j A) (d.integralRingIso j) (exchangeScalar_comm d j))).inv

/-- The scalar/open mate is invertible and preserves the normalized open adjunction.
Source: Stacks 03DI
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof: the extension presheaf has the same direct-sum summands and restriction maps
after scalar restriction. Its action is the completed action composed with the scalar
map. Sheafification therefore gives the identity on the underlying additive sheaf.
The open unit includes the structure-map summand and the counit evaluates that
summand; both are unchanged. Its transpose is the displayed mate, so it is invertible. -/
theorem cbcRealizationScalarOpenInv_isIso {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] : IsIso (cbcRealizationScalarOpenInv d j) := by
  sorry

/-- Canonical scalar/open comparison on ordinary modules.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationScalarOpen {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcOpenShriek d j inferInstance ⋙ cbcRealizationRes d T ≅
      cbcRealizationRes d U ⋙ ProEtale.StrictTower.moduleJ A j :=
  (@asIso _ _ _ _ (cbcRealizationScalarOpenInv d j)
    (cbcRealizationScalarOpenInv_isIso d j)).symm

/-- Apply scalar/open comparison to a whole strict diagram, then derive exactly.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationTowerScalarOpen {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcRealizationJ d j ⋙ exchangeTowerRes d T ≅
      exchangeTowerRes d U ⋙ ProEtale.StrictTower.J A j :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Functor.whiskeringRightObjCompIso _ _ ≪≫
        (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (cbcRealizationScalarOpen d j) ≪≫
        (Functor.whiskeringRightObjCompIso _ _).symm) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Scalar/open comparison on single derived objects, by exact descent.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationDerivedScalarOpen {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcDerivedOpenShriek d j inferInstance ⋙ (cbcRealizationRes d T).mapDerivedCategory ≅
      (cbcRealizationRes d U).mapDerivedCategory ⋙
        (ProEtale.StrictTower.moduleJ A j).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (cbcRealizationScalarOpen d j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The quotient/open tensor identification followed by scalar/open identification.
Source: Stacks 03DI, 0E8I
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationQuotientOpen {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : d.derived U) :
    (exchangeTowerRes d T).obj
        ((completedReductionTower T d).obj ((cbcDerivedOpenShriek d j inferInstance).obj K)) ≅
      (ProEtale.StrictTower.J A j).obj
        ((exchangeTowerRes d U).obj ((completedReductionTower U d).obj K)) :=
  (exchangeTowerRes d T).mapIso (cbcRealizationReduction d j K) ≪≫
    (cbcRealizationTowerScalarOpen d j).app ((completedReductionTower U d).obj K)

/-- Products are preserved by scalar restriction and by quasi-compact constant open extension.
Source: Stacks 03D3, 09BP
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof: restriction leaves the underlying additive sheaves and all limits unchanged.
For open extension, use j!N = ker(j*N to i*i^-1j*N). Direct images preserve
products sectionwise and closed inverse image preserves products on the pro-etale
site. Kernels commute with products. These are the canonical projection maps,
including for the empty product; no qcqs hypothesis on the ambient scheme is used. -/
theorem cbcRealizationProducts (T : Scheme.{t}) :
    (∀ M : ℕ → reductionModules T (d.completedRing T),
      IsIso (piComparison (cbcRealizationRes d T) M)) ∧
      ∀ {U : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
        (M : ℕ → ProEtale.StrictTower.Modules A U),
        IsIso (piComparison (ProEtale.StrictTower.moduleJ A j) M) := by
  sorry

/-- The specified scalar-restriction/Rlim isomorphism.
Source: Stacks 03D3 (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationResLimit (T : Scheme.{t}) :
    completedRlim T (d.completedRing T) ⋙ (cbcRealizationRes d T).mapDerivedCategory ≅
      exchangeTowerRes d T ⋙ completedRlim T (exchangeConstantRing T A) :=
  @asIso _ _ _ _ (cbcRealizationLimitMap (cbcRealizationRes d T))
    (cbcRealizationLimitMap_isIso _ (cbcRealizationProducts d T).1)

/-- The specified constant open-extension/Rlim isomorphism.
Source: Stacks 09BP (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationOpenLimit (d : AdicCoefficientDatum A) {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] [QuasiCompact j] :
    completedRlim U (exchangeConstantRing U A) ⋙
        (ProEtale.StrictTower.moduleJ A j).mapDerivedCategory ≅
      ProEtale.StrictTower.J A j ⋙ completedRlim T (exchangeConstantRing T A) :=
  @asIso _ _ _ _ (cbcRealizationLimitMap (ProEtale.StrictTower.moduleJ A j))
    (cbcRealizationLimitMap_isIso _ ((cbcRealizationProducts d T).2 j))

/-- Direct-image/Rlim comparison for constant coefficients, as the conjugate
of the identity constant-diagram/pullback comparison, including both units.
Source: Stacks 0A07 (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationPushLimit {U T : Scheme.{t}} (f : U ⟶ T) :
    completedRlim U (exchangeConstantRing U A) ⋙
        (ProEtale.StrictTower.moduleDirectImage A f).rightDerivedFunctor ≅
      ProEtale.StrictTower.R A f ⋙ completedRlim T (exchangeConstantRing T A) :=
  conjugateIsoEquiv
    (((proEtaleRingModuleAdjunction f (exchangeConstantRing T A)
      (exchangeConstantRing U A) (exchangeConstantIso f A)).mapDerivedCategoryRightDerivedAdjunction
      ).comp (cbcRealizationLimitAdj U (exchangeConstantRing U A)))
    ((cbcRealizationLimitAdj T (exchangeConstantRing T A)).comp (ProEtale.StrictTower.adj A f))
    (cbcRealizationConst (ProEtale.StrictTower.modulePullback A f)).symm

/-- The single-object direct-image/scalar comparison, with its published universal units.
Source: Stacks 0D6E (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationResPush {U T : Scheme.{t}} (f : U ⟶ T) :
    d.push f ⋙ (cbcRealizationRes d T).mapDerivedCategory ≅
      (cbcRealizationRes d U).mapDerivedCategory ⋙
        (ProEtale.StrictTower.moduleDirectImage A f).rightDerivedFunctor :=
  proEtaleRingRestrictionDerivedDirectImage f
    (exchangeConstantRing T A) (d.completedRing T)
    (exchangeConstantRing U A) (d.completedRing U)
    (exchangeScalar d T) (exchangeScalar d U)
    (exchangeConstantIso f A) (d.integralRingIso f) (exchangeScalar_comm d f)

/-- Canonical constant-tower presentation of completed pullback.
Source: Stacks 099M and finite reduction comparison
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationPullLimit {U T : Scheme.{t}} (f : U ⟶ T) (K : d.derived T) :
    (cbcRealizationRes d U).mapDerivedCategory.obj ((d.completedPull f).obj K) ≅
      (completedRlim U (exchangeConstantRing U A)).obj
        ((ProEtale.StrictTower.G A f).obj
          ((exchangeTowerRes d T).obj ((completedReductionTower T d).obj K))) :=
  (cbcRealizationResLimit d U).app
      ((d.towerPull f).obj ((completedReductionTower T d).obj K)) ≪≫
    (completedRlim U (exchangeConstantRing U A)).mapIso
      ((exchangeResPull d f).app ((completedReductionTower T d).obj K))

variable {X' X Y' Y : Scheme.{t}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {g : Y' ⟶ Y} {g' : X' ⟶ X}

/-- The actual strict-tower proper/open composite, defined before evaluation.
The proper mate is the normalization dependency's mate on constant A towers.
Source: blueprint Definition 1939 and strict normalization, final paragraph
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationStrict (c : Compactification f) (c' : Compactification f')
    (gbar : c'.Z ⟶ c.Z) (sp : ChosenCartesianSquare gbar c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i gbar)
    (M : ProEtale.StrictTower.Derived A X) :
    (ProEtale.StrictTower.G A g).obj
        ((ProEtale.StrictTower.R A c.g).obj ((ProEtale.StrictTower.J A c.i).obj M)) ⟶
      (ProEtale.StrictTower.R A c'.g).obj
        ((ProEtale.StrictTower.J A c'.i).obj ((ProEtale.StrictTower.G A g').obj M)) :=
  (exchangeConstantSquare (A := A) sp).exchangeTowerMate.app
      ((ProEtale.StrictTower.J A c.i).obj M) ≫
    (ProEtale.StrictTower.R A c'.g).map
      ((ProEtale.StrictTower.beta A g' c'.i c.i gbar sj.w
        (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd)).hom.app M)

/-- Source identification: specified strict projection, scalar/limit comparison,
proper corner b, and canonical quotient/open tensor comparison, in that order.
Source: blueprint strict realization, proof step 9
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationSource (c : Compactification f) (c' : Compactification f')
    (gbar : c'.Z ⟶ c.Z) (K : d.derived X) :
    (cbcRealizationRes d Y').mapDerivedCategory.obj
        ((d.completedPull g).obj
          ((d.push c.g).obj ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).obj K))) ≅
      (completedRlim Y' (exchangeConstantRing Y' A)).obj
        ((ProEtale.StrictTower.G A g).obj
          ((ProEtale.StrictTower.R A c.g).obj
            ((ProEtale.StrictTower.J A c.i).obj
              ((exchangeTowerRes d X).obj ((completedReductionTower X d).obj K))))) :=
  ((cbcRealizationRes d Y').mapDerivedCategory).mapIso
      ((completedRlim Y' (d.completedRing Y')).mapIso
        (d.towerH (f := c.g) (f' := c'.g) (g := g) (g' := gbar)
          ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).obj K))) ≪≫
    (cbcRealizationResLimit d Y').app _ ≪≫
    (completedRlim Y' (exchangeConstantRing Y' A)).mapIso
      ((exchangeCornerB d c.g g).app _ ≪≫
        (ProEtale.StrictTower.G A g).mapIso
          ((ProEtale.StrictTower.R A c.g).mapIso (cbcRealizationQuotientOpen d c.i K)))

/-- Target identification: inverse direct-image/limit and extension/limit maps,
followed by inverse completed-pullback, scalar/open, and scalar/direct-image maps.
Source: blueprint strict realization, proof step 9
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationTarget (c' : Compactification f') (g' : X' ⟶ X)
    [qc : QuasiCompact c'.i] (K : d.derived X) :
    (completedRlim Y' (exchangeConstantRing Y' A)).obj
        ((ProEtale.StrictTower.R A c'.g).obj
          ((ProEtale.StrictTower.J A c'.i).obj ((ProEtale.StrictTower.G A g').obj
            ((exchangeTowerRes d X).obj ((completedReductionTower X d).obj K))))) ≅
      (cbcRealizationRes d Y').mapDerivedCategory.obj
        ((d.push c'.g).obj ((cbcDerivedOpenShriek d c'.i c'.isOpenImmersion).obj
          ((d.completedPull g').obj K))) :=
  ((cbcRealizationPushLimit (A := A) c'.g).app _).symm ≪≫
    (ProEtale.StrictTower.moduleDirectImage A c'.g).rightDerivedFunctor.mapIso
      (((cbcRealizationOpenLimit d c'.i).app _).symm ≪≫
        (ProEtale.StrictTower.moduleJ A c'.i).mapDerivedCategory.mapIso
          (cbcRealizationPullLimit d g' K).symm ≪≫
        ((cbcRealizationDerivedScalarOpen d c'.i).app ((d.completedPull g').obj K)).symm) ≪≫
    ((cbcRealizationResPush d c'.g).app _).symm

/-- Quasi-compactness of the base-changed open follows from the supplied square.
Source: Stacks 01K5 (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
abbrev cbcRealizationOpenQC [QuasiCompact f] (c : Compactification f)
    (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (sj : OpenImmersionSquare g' c'.i c.i gbar) : QuasiCompact c'.i :=
  MorphismProperty.of_isPullback
    (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd)
      (c.quasiCompact_openImmersion inferInstance)

/-- The ordered completed compact-support exchange is the image of the actual
strict-tower composite under the specified, normalized source and target comparisons.
All isomorphisms in the statement are the definitions above; none is an existential
isomorphism of endpoints. The theorem's naturality and evaluation clauses follow below.

Source: blueprint main-20261015, Definition 1939 and proof of thm-cbc-complete-proetale
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof, following the ten DAG steps:
1. Restriction of scalars preserves the direct-sum extension presheaf, its scalar
   action, sheafification, unit and counit. Exact descent gives the tower comparison.
2. Put F = j!K. Its assumed intrinsic completeness gives quotient-unit completeness
   by Koszul reconstruction. Its finite origins are j!L_n: etale extension and
   comparison pullback are exact. Each L_n keeps its own lower bound.
3. Use strictTowerExchangeMateNormalization with precisely H,H' of the definition.
   It gives d Res(v') = E b on strict towers, before evaluating anything.
4. The inverse open comparison is the transpose of the open unit. Scalar restriction
   preserves that unit. FiniteOpenExchangeScalars identifies all quotient transitions
   and compatible ambient actions, so the actual strict open map is beta.
5. Recollement writes open extension as a kernel of product-preserving functors.
   Closed inverse image preserves products. This verifies the canonical product map,
   also on the empty family, without requiring the ambient scheme to be qcqs.
6. Apply exactProductFunctorStrictLimit to extension and restriction. Its signed
   Roos and resolution normalizations identify its comparison with the constant mate
   used above. The formula for a composite cancels the intermediate Roos comparisons,
   hence scalar restriction and open extension give the same normalized limit map.
7. The ordered open factor is Rlim(beta), then inverse extension/limit comparison,
   with finite-reduction and coefficient comparisons on its two ends.
8. Flatness of constant-to-completed coefficients implies that scalar restriction
   preserves K-injective diagrams. On the same K-injective representative the
   completed direct-image/limit comparison restricts to cbcRealizationPushLimit.
9. Naturality of this last comparison moves Rlim(beta) through direct image.
   Substitute the proper and open factors; cancel the middle comparison and use
   functoriality of Rlim. The result is the displayed identity of actual morphisms.
10. Every factor is natural in K. Evaluation preserves the already defined composite;
    proper normalization and the inverse-open-unit normalization identify it with
    the specified finite proper/open exchange. No faithfulness of evaluation is used. -/
theorem completeProetaleStrictTowerRealization [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare gbar c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i gbar)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (_origins : PbcHasCompatibleEtaleOrigins X d K.obj)
    (_completeOpen : cbcCompleteProperty d c.Z r a ha
      ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).obj K.obj)) :
    (cbcRealizationRes d Y').mapDerivedCategory.map
        (completedCompactSupportExchange d c c' gbar sp sj r a ha K) =
      (cbcRealizationSource d c c' gbar (g := g) K.obj).hom ≫
        (completedRlim Y' (exchangeConstantRing Y' A)).map
          (cbcRealizationStrict (A := A) c c' gbar sp sj
            ((exchangeTowerRes d X).obj ((completedReductionTower X d).obj K.obj))) ≫
        (cbcRealizationTarget d c' g' (qc := cbcRealizationOpenQC c c' gbar sj) K.obj).hom := by
  sorry

/-- The canonical single-object pullback square, by exact descent of its module square.
Source: Stacks 07A7 (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationSingleSquare {V W S T : Scheme.{t}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    (ProEtale.StrictTower.modulePullback A i).mapDerivedCategory ⋙
        (ProEtale.StrictTower.modulePullback A r).mapDerivedCategory ≅
      (ProEtale.StrictTower.modulePullback A p).mapDerivedCategory ⋙
        (ProEtale.StrictTower.modulePullback A k).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (ProEtale.StrictTower.moduleSquareG A k r p i h) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The specified single-object proper mate. On a quotient object its scalar action
is the inherited P_n action; scalar restriction preserves its unit and counit.
Source: Stacks 07A7 (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationSingleProper {V W S T : Scheme.{t}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    (ProEtale.StrictTower.moduleDirectImage A p).rightDerivedFunctor ⋙
        (ProEtale.StrictTower.modulePullback A i).mapDerivedCategory ⟶
      (ProEtale.StrictTower.modulePullback A k).mapDerivedCategory ⋙
        (ProEtale.StrictTower.moduleDirectImage A r).rightDerivedFunctor :=
  mateEquiv
    (proEtaleRingModuleAdjunction p (exchangeConstantRing T A)
      (exchangeConstantRing W A) (exchangeConstantIso p A)).mapDerivedCategoryRightDerivedAdjunction
    (proEtaleRingModuleAdjunction r (exchangeConstantRing S A)
      (exchangeConstantRing V A) (exchangeConstantIso r A)).mapDerivedCategoryRightDerivedAdjunction
    (cbcRealizationSingleSquare (A := A) k r p i h).hom

/-- The inverse-open-unit map is invertible for any Cartesian open square.
Source: Stacks 03DI, 09AE
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof: identify the right adjoints by restriction on the same pulled-back test
object. Their unique left-adjoint comparison is invertible and its inverse
transposes to the pulled-back open unit. This is singleBetaInv by its definition. -/
theorem cbcRealizationSingleBeta_isIso {U' U T' T : Scheme.{t}}
    (a : U' ⟶ U) (j' : U' ⟶ T') (j : U ⟶ T) (b : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ b)
    (_sq : IsPullback a j' j b) :
    IsIso (ProEtale.StrictTower.singleBetaInv A a j' j b h) := by
  sorry

/-- The forward single-object open exchange, with the exact finite unit normalization.
Source: Stacks 03DI (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationSingleOpen {U' U T' T : Scheme.{t}}
    (a : U' ⟶ U) (j' : U' ⟶ T') (j : U ⟶ T) (b : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ b)
    (sq : IsPullback a j' j b) :
    (ProEtale.StrictTower.moduleJ A j).mapDerivedCategory ⋙
        (ProEtale.StrictTower.modulePullback A b).mapDerivedCategory ≅
      (ProEtale.StrictTower.modulePullback A a).mapDerivedCategory ⋙
        (ProEtale.StrictTower.moduleJ A j').mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (@asIso _ _ _ _ (ProEtale.StrictTower.singleBetaInv A a j' j b h)
        (cbcRealizationSingleBeta_isIso (A := A) a j' j b h sq)).symm ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Evaluate the source through the specified pullback, direct-image and open comparisons.
Source: Stacks 07A7 (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationEvalSource (c : Compactification f) (g : Y' ⟶ Y)
    (M : ProEtale.StrictTower.Derived A X) (n : ℕ) :=
  (ProEtale.StrictTower.evalG A g n).hom.app
      ((ProEtale.StrictTower.R A c.g).obj ((ProEtale.StrictTower.J A c.i).obj M)) ≫
    (ProEtale.StrictTower.modulePullback A g).mapDerivedCategory.map
      ((ProEtale.StrictTower.evalR A c.g n).app ((ProEtale.StrictTower.J A c.i).obj M)) ≫
    (ProEtale.StrictTower.modulePullback A g).mapDerivedCategory.map
      ((ProEtale.StrictTower.moduleDirectImage A c.g).rightDerivedFunctor.map
        ((ProEtale.StrictTower.evalJ A c.i n).hom.app M))

/-- Evaluate the target through the specified direct-image, open and pullback comparisons.
Source: Stacks 07A7 (blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationEvalTarget (c' : Compactification f') (g' : X' ⟶ X)
    (M : ProEtale.StrictTower.Derived A X) (n : ℕ) :=
  (ProEtale.StrictTower.evalR A c'.g n).app
      ((ProEtale.StrictTower.J A c'.i).obj ((ProEtale.StrictTower.G A g').obj M)) ≫
    (ProEtale.StrictTower.moduleDirectImage A c'.g).rightDerivedFunctor.map
      ((ProEtale.StrictTower.evalJ A c'.i n).hom.app ((ProEtale.StrictTower.G A g').obj M)) ≫
    (ProEtale.StrictTower.moduleDirectImage A c'.g).rightDerivedFunctor.map
      ((ProEtale.StrictTower.moduleJ A c'.i).mapDerivedCategory.map
        ((ProEtale.StrictTower.evalG A g' n).hom.app M))

/-- The specified finite proper/open composite, in its scalar-restricted single-object
coordinates. For M = Res(K_bullet), n denotes the quotient P_(n+1), not a new coefficient
choice. The proper factor is the adjunction mate and the open factor the inverse-unit mate.
Source: Stacks 07A7, 03DI
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationFinite (c : Compactification f) (c' : Compactification f')
    (gbar : c'.Z ⟶ c.Z) (sp : ChosenCartesianSquare gbar c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i gbar)
    (N : DerivedCategory (ProEtale.StrictTower.Modules A X)) :=
  (cbcRealizationSingleProper (A := A) gbar c'.g c.g g sp.w).app
      ((ProEtale.StrictTower.moduleJ A c.i).mapDerivedCategory.obj N) ≫
    (ProEtale.StrictTower.moduleDirectImage A c'.g).rightDerivedFunctor.map
      ((cbcRealizationSingleOpen (A := A) g' c'.i c.i gbar sj.w
        (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd)).hom.app N)

/-- Evaluation describes the actual strict composite using the normalized finite mates.
It does not reconstruct a tower map from evaluations.
Source: blueprint strict realization, proof step 10; Stacks 07A7 and 03DI
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof: evaluation commutes with exact G and J and evaluates their units termwise.
Its direct-image comparison is the mate of the pullback/evaluation comparison.
The mate correspondence therefore identifies evaluation of the proper factor
with cbcRealizationSingleProper. Transpose the open inverse: both sides are the
same evaluated open unit, hence agree. Compose these two equalities, using
naturality of evalR at beta. On quotient objects, constant/completed finite
reduction and strictTowerExchangeMateNormalization identify the proper mate with
the specified finite etale exchange; finite open scalar compatibility does the
same for the open mate, retaining the P_n actions and their quotient transitions. -/
theorem completeProetaleStrictTowerRealization_evaluation
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare gbar c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i gbar)
    (M : ProEtale.StrictTower.Derived A X) (n : ℕ) :
    (ProEtale.StrictTower.ev A Y' n).map
        (cbcRealizationStrict (A := A) c c' gbar sp sj M) ≫
        cbcRealizationEvalTarget (A := A) c' g' M n =
      cbcRealizationEvalSource (A := A) c g M n ≫
        cbcRealizationFinite (A := A) c c' gbar sp sj ((ProEtale.StrictTower.ev A X n).obj M) := by
  sorry

/-- The strict realization and both canonical endpoint identifications are natural in K.
Source: blueprint strict realization, final paragraph
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof: the quotient tensor comparison is a transpose of the natural open unit.
All scalar, projection and limit comparisons are natural transformations, and
proper/open factors are normalized adjunction mates. Compose their naturality
squares in the order of the definitions. No condition on the chosen lower bounds
of the finite origins is used, and maps of derived objects need no lift to a
chosen strict complex. -/
theorem completeProetaleStrictTowerRealization_naturality [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (sj : OpenImmersionSquare g' c'.i c.i gbar)
    (K L : d.derived X) (k : K ⟶ L) :
    (cbcRealizationRes d Y').mapDerivedCategory.map
        ((d.completedPull g).map ((d.push c.g).map
          ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).map k))) ≫
        (cbcRealizationSource d c c' gbar (g := g) L).hom =
      (cbcRealizationSource d c c' gbar (g := g) K).hom ≫
        (completedRlim Y' (exchangeConstantRing Y' A)).map
          ((ProEtale.StrictTower.G A g).map ((ProEtale.StrictTower.R A c.g).map
            ((ProEtale.StrictTower.J A c.i).map
              ((exchangeTowerRes d X).map ((completedReductionTower X d).map k))))) ∧
    (completedRlim Y' (exchangeConstantRing Y' A)).map
        ((ProEtale.StrictTower.R A c'.g).map ((ProEtale.StrictTower.J A c'.i).map
          ((ProEtale.StrictTower.G A g').map
            ((exchangeTowerRes d X).map ((completedReductionTower X d).map k))))) ≫
        (cbcRealizationTarget d c' g' (qc := cbcRealizationOpenQC c c' gbar sj) L).hom =
      (cbcRealizationTarget d c' g' (qc := cbcRealizationOpenQC c c' gbar sj) K).hom ≫
        (cbcRealizationRes d Y').mapDerivedCategory.map
          ((d.push c'.g).map ((cbcDerivedOpenShriek d c'.i c'.isOpenImmersion).map
            ((d.completedPull g').map k))) := by
  sorry

/-- Source presentation for the ordered open factor, using the same quotient/open map.
Source: blueprint Definition 1939
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationOpenSource (c : Compactification f) (c' : Compactification f')
    (gbar : c'.Z ⟶ c.Z) (K : d.derived X) :=
  cbcRealizationPullLimit d gbar ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).obj K) ≪≫
    (completedRlim c'.Z (exchangeConstantRing c'.Z A)).mapIso
      ((ProEtale.StrictTower.G A gbar).mapIso (cbcRealizationQuotientOpen d c.i K))

/-- The target of the open factor uses inverse extension/limit, followed by the
inverse pullback presentation and scalar/open transport, in precisely this order.
Source: Stacks 09BP and blueprint Definition 1939
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
def cbcRealizationOpenTarget (c' : Compactification f') (g' : X' ⟶ X)
    [qc : QuasiCompact c'.i] (K : d.derived X) :=
  ((cbcRealizationOpenLimit d c'.i).app
      ((ProEtale.StrictTower.G A g').obj
        ((exchangeTowerRes d X).obj ((completedReductionTower X d).obj K)))).symm ≪≫
    (ProEtale.StrictTower.moduleJ A c'.i).mapDerivedCategory.mapIso
      (cbcRealizationPullLimit d g' K).symm ≪≫
    ((cbcRealizationDerivedScalarOpen d c'.i).app ((d.completedPull g').obj K)).symm

/-- The published completed open factor, with its derived quasi-compactness instance.
Source: blueprint Definition 1939
(blueprint: lem-cbc-complete-proetale-strict-tower-realization). -/
abbrev cbcRealizationOpenFactor [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (sj : OpenImmersionSquare g' c'.i c.i gbar)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory) :=
  letI : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  (cbcDatumCompletedExchange d sj r a ha).app K

/-- The ordered open-factor formula uses the already defined beta and normalized limit mate.
Source: blueprint Definition 1939; Stacks 03DI and 09BP
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof: scalar restriction preserves the open unit and its transpose, on whole strict
complexes, hence preserves beta before evaluation. The finite-reduction comparisons
respect every quotient transition. Apply Rlim to this beta and then the inverse
canonical extension/limit comparison. The exact-product strict-limit theorem identifies
that comparison with cbcRealizationOpenLimit, with its resolution and augmentation
normalizations. The resulting map obeys the ordinary-exchange/completion-unit equation
of cbcDatumCompletedExchange. Completeness and that definition's uniqueness identify
the maps. Both displayed endpoints use the same finite reduction and scalar transports. -/
theorem completeProetaleStrictTowerRealization_open [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (sj : OpenImmersionSquare g' c'.i c.i gbar)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory) :
    (cbcRealizationRes d c'.Z).mapDerivedCategory.map
        (cbcRealizationOpenFactor d c c' gbar sj r a ha K) =
      (cbcRealizationOpenSource d c c' gbar K.obj).hom ≫
        (completedRlim c'.Z (exchangeConstantRing c'.Z A)).map
          ((ProEtale.StrictTower.beta A g' c'.i c.i gbar sj.w
            (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd)).hom.app
              ((exchangeTowerRes d X).obj ((completedReductionTower X d).obj K.obj))) ≫
        (cbcRealizationOpenTarget d c' g' (qc := cbcRealizationOpenQC c c' gbar sj) K.obj).hom := by
  sorry

end AlgebraicGeometry.Scheme
