/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingedOpenExtensionProducts
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.CategoryTheory.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Algebra.Homology.ScalarInternalHomDataSupplement
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
public import WeilConjectures.CategoryTheory.StrictRoosComparison
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.RoosComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.StrictRoosNormalization
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.Logic.Denumerable
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.CategoryTheory.RingedOpenScalarAdjunction
import WeilConjectures.SixFunctors.ExactLocalizationInverseMate
public import WeilConjectures.AlgebraicGeometry.NormalizedLimitSquareCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.SixFunctors.OpenTensorNormalizationData
public import Mathlib.CategoryTheory.Adjunction.Whiskering

import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
/-!
# Scalar and normalized inverse-limit coherence for ringed open extension

Source: Stacks Project, Tags 09BP, 03DI, 03DJ and 03CY; the final paragraph of
blueprint `lem-cbc-completed-extension-zero-comparison.proof.md`
(blueprint: lem-cbc-ringed-open-scalar-limit-coherence).

## Main statements

- `ringedOpenScalarLimitCoherence`: canonical scalar/open and normalized-limit coherence.
- `CbcLimitNormalized`: the specified ordinary-limit and K-injective normalization.
- `CbcAugmentationCompatible`: compatibility with all strict augmentation maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096

universe u vA uA vB uB vC uC vD uD wA wB wC wD

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
attribute [-instance] RingedOpenScalar.scalarLimits RingedOpenScalar.scalarColimits
  RingedOpenScalar.sliceLimits RingedOpenScalar.sliceColimits

namespace CategoryTheory

section
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasLimits A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasLimits B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Actual derived postcomposition on strict towers, with levelwise exactness.
Source: Stacks 03DJ, 05RU
(blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
abbrev cbcTowerDerived : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤
    DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) :=
  @Functor.mapDerivedCategory _ _ _ _ _ _ _ _
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) inferInstance
    (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)

/-- The actual complex-to-derived factorization for tower postcomposition.
Source: Stacks 05RU (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
abbrev cbcTowerFactors :=
  @Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) inferInstance
    (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)

/-- The ordinary-limit unit normalization of the specified comparison. This is the
K-injective normalization of `exactProductFunctorStrictLimit`: on a K-injective tower
it reads `F lim I → lim FI → Rlim FI`. Its Roos description is precisely that theorem's
signed two-summand formula, not an unspecified triangle isomorphism.
Source: Stacks 0941; normalized comparison in
(blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
structure CbcLimitNormalized
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB)
    (lambda : LA ⋙ F.mapDerivedCategory ≅ cbcTowerDerived F ⋙ LB) : Prop where
  equation : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    F.mapDerivedCategory.map (etaA.app X) ≫ lambda.hom.app (DerivedCategory.Q.obj X) ≫
        LB.map ((cbcTowerFactors F).hom.app X) =
      F.mapDerivedCategoryFactors.hom.app (limit X.asFunctor) ≫
        DerivedCategory.Q.map
          (limit.lift _ ((F.mapHomologicalComplex (.up ℤ)).mapCone (limit.cone X.asFunctor))) ≫
        etaB.app ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj X)

end

section
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [K.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits K] [PreservesFiniteColimits K]

/-- Canonical localization of a commuting square, using the existing derived composition
and natural-isomorphism transports, including their exact complex factorizations.
Source: Stacks 05RU (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
def cbcDerivedSquare (e : F ⋙ G ≅ H ⋙ K) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ K.mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso e

/-- The same canonical square on derived strict towers, using levelwise exactness.
Source: Stacks 05RU (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
def cbcDerivedTowerSquare
    [HasLimits A] [HasLimits B] [HasLimits C] [HasLimits D]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{wC} (ℕᵒᵖ ⥤ C)] [HasDerivedCategory.{wD} (ℕᵒᵖ ⥤ D)]
    (e : F ⋙ G ≅ H ⋙ K) :
    cbcTowerDerived F ⋙ cbcTowerDerived G ≅ cbcTowerDerived H ⋙ cbcTowerDerived K :=
  CategoryTheory.NormalizedLimitSquare.towerSquare F G H K e

end

/-- The recorded exact-derived adjunction applied to the actual tower adjunction.
Source: Stacks 015F (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
def cbcDerivedTowerAdjunction
    {A B : Type uA} [Category.{vA} A] [Category.{vA} B] [Abelian A] [Abelian B]
    [HasLimits A] [HasLimits B]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ B)]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : F ⊣ G) :
    cbcTowerDerived F ⊣ cbcTowerDerived G :=
  CategoryTheory.RoosAdjunctionUnit.towerAdjunction adj

/-- Unit and counit equations for the scalar/open-extension square.
Source: Stacks 03DI, the two explicit Hom maps
(blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
def CbcAdjunctionCompatible
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {JS : A ⥤ C} {JR : B ⥤ D} {rU : A ⥤ B} {rT : C ⥤ D}
    {qS : C ⥤ A} {qR : D ⥤ B}
    (e : JS ⋙ rT ≅ rU ⋙ JR) (d : rT ⋙ qR ≅ qS ⋙ rU)
    (adjS : JS ⊣ qS) (adjR : JR ⊣ qR) : Prop :=
  (∀ N : A, rU.map (adjS.unit.app N) ≫ d.inv.app (JS.obj N) ≫
    qR.map (e.hom.app N) = adjR.unit.app (rU.obj N)) ∧
  (∀ Q : C, e.hom.app (qS.obj Q) ≫ JR.map (d.inv.app Q) ≫
    adjR.counit.app (rT.obj Q) = rT.map (adjS.counit.app Q))

/-- Canonical square on complexes with its composition factors explicit.
Source: Stacks 03DJ (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
def cbcComplexSquare
    {A : Type uA} [Category.{vA} A] [Preadditive A]
    {B : Type uB} [Category.{vB} B] [Preadditive B]
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive] (e : F ⋙ G ≅ H ⋙ K) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ K.mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex e (.up ℤ)

section EquationCalculus

variable {A B C D : Type uA} [Category.{vA} A] [Category.{vA} B]
  [Category.{vA} C] [Category.{vA} D]
  {JS : A ⥤ C} {JR : B ⥤ D} {rU : A ⥤ B} {rT : C ⥤ D}
  {qS : C ⥤ A} {qR : D ⥤ B}
  (e : JS ⋙ rT ≅ rU ⋙ JR) (d : rT ⋙ qR ≅ qS ⋙ rU)
  (adjS : JS ⊣ qS) (adjR : JR ⊣ qR)

private theorem inverseMate_of_unit
    (hu : ∀ N : A, rU.map (adjS.unit.app N) ≫ d.inv.app (JS.obj N) ≫
      qR.map (e.hom.app N) = adjR.unit.app (rU.obj N)) :
    ((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv)).natTrans = e.inv := by
  ext N
  apply (adjR.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change adjR.unit.app (rU.obj N) ≫ qR.map
      (((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv)).natTrans.app N) = _
  have h := unit_mateEquiv_symm adjS adjR (TwoSquare.mk _ _ _ _ d.inv) N
  change rU.map (adjS.unit.app N) ≫ d.inv.app (JS.obj N) =
    adjR.unit.app (rU.obj N) ≫ qR.map
      (((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv)).natTrans.app N) at h
  rw [← h, ← hu N]
  simp only [Category.assoc]
  rw [← qR.map_comp, Iso.hom_inv_id_app]
  erw [qR.map_id]
  erw [Category.comp_id]

private theorem equations_of_inverseMate
    (hm : ((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv)).natTrans = e.inv) :
    CbcAdjunctionCompatible e d adjS adjR := by
  have hu (N : A) := unit_mateEquiv_symm adjS adjR (TwoSquare.mk _ _ _ _ d.inv) N
  have hc (Q : C) := mateEquiv_counit_symm adjS adjR (TwoSquare.mk _ _ _ _ d.inv) Q
  constructor
  · intro N
    have hu' := hu N
    change rU.map (adjS.unit.app N) ≫ d.inv.app (JS.obj N) =
      adjR.unit.app (rU.obj N) ≫ qR.map
        (((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv)).natTrans.app N) at hu'
    rw [hm] at hu'
    rw [reassoc_of% hu']
    rw [← qR.map_comp, Iso.inv_hom_id_app]
    erw [qR.map_id]
    rw [Category.comp_id]
  · intro Q
    have hc' := hc Q
    change JR.map (d.inv.app Q) ≫ adjR.counit.app (rT.obj Q) =
      (((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv)).natTrans.app (qS.obj Q)) ≫
        rT.map (adjS.counit.app Q) at hc'
    rw [hm] at hc'
    rw [hc', Iso.hom_inv_id_app_assoc]

variable [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [JS.Additive] [JR.Additive] [rU.Additive] [rT.Additive] [qS.Additive] [qR.Additive]

private theorem equations_complex (he : CbcAdjunctionCompatible e d adjS adjR) :
    CbcAdjunctionCompatible
      (JS := JS.mapHomologicalComplex (.up ℤ))
      (JR := JR.mapHomologicalComplex (.up ℤ))
      (rU := rU.mapHomologicalComplex (.up ℤ))
      (rT := rT.mapHomologicalComplex (.up ℤ))
      (qS := qS.mapHomologicalComplex (.up ℤ))
      (qR := qR.mapHomologicalComplex (.up ℤ))
      (cbcComplexSquare JS rT rU JR e)
      (cbcComplexSquare rT qR qS rU d)
      (adjS.mapHomologicalComplex (.up ℤ)) (adjR.mapHomologicalComplex (.up ℤ)) := by
  unfold cbcComplexSquare
  constructor
  · intro N
    apply HomologicalComplex.Hom.ext
    funext i
    exact he.1 (N.X i)
  · intro Q
    apply HomologicalComplex.Hom.ext
    funext i
    exact he.2 (Q.X i)

omit [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [JS.Additive] [JR.Additive] [rU.Additive] [rT.Additive] [qS.Additive] [qR.Additive] in
private theorem equations_tower (he : CbcAdjunctionCompatible e d adjS adjR) :
    CbcAdjunctionCompatible
      (JS := (Functor.whiskeringRight ℕᵒᵖ A C).obj JS)
      (JR := (Functor.whiskeringRight ℕᵒᵖ B D).obj JR)
      (rU := (Functor.whiskeringRight ℕᵒᵖ A B).obj rU)
      (rT := (Functor.whiskeringRight ℕᵒᵖ C D).obj rT)
      (qS := (Functor.whiskeringRight ℕᵒᵖ C A).obj qS)
      (qR := (Functor.whiskeringRight ℕᵒᵖ D B).obj qR)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso e)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso d)
      (adjS.whiskerRight ℕᵒᵖ) (adjR.whiskerRight ℕᵒᵖ) := by
  constructor
  · intro N
    ext n
    simpa [Adjunction.whiskerRight] using he.1 (N.obj n)
  · intro Q
    ext n
    simpa [Adjunction.whiskerRight] using he.2 (Q.obj n)

variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} B]
  [HasDerivedCategory.{wA} C] [HasDerivedCategory.{wA} D]
  [PreservesFiniteLimits JS] [PreservesFiniteColimits JS]
  [PreservesFiniteLimits JR] [PreservesFiniteColimits JR]
  [PreservesFiniteLimits rU] [PreservesFiniteColimits rU]
  [PreservesFiniteLimits rT] [PreservesFiniteColimits rT]
  [PreservesFiniteLimits qS] [PreservesFiniteColimits qS]
  [PreservesFiniteLimits qR] [PreservesFiniteColimits qR]

private theorem cbcDerivedSquare_symm :
    cbcDerivedSquare rU JR JS rT e.symm = (cbcDerivedSquare JS rT rU JR e).symm := by
  apply Iso.ext
  simp only [cbcDerivedSquare, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Functor.mapDerivedCategoryNatIso_symm, Iso.symm_inv, Category.assoc]

private theorem equations_derived (he : CbcAdjunctionCompatible e d adjS adjR) :
    CbcAdjunctionCompatible (cbcDerivedSquare JS rT rU JR e) (cbcDerivedSquare rT qR qS rU d)
      (OpenTensorNormalization.exactDerivedAdjunction adjS)
      (OpenTensorNormalization.exactDerivedAdjunction adjR) := by
  have hm := inverseMate_of_unit e d adjS adjR he.1
  have : IsIso
      ((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.symm.hom)).natTrans := by
    change IsIso ((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv)).natTrans
    rw [hm]
    infer_instance
  have hiso : asIso
      ((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.symm.hom)).natTrans = e.symm := by
    apply Iso.ext
    exact hm
  have hd := (exact_localization_inverse_mate adjS adjR d.symm).2.1
  rw [hiso] at hd
  change ((mateEquiv (OpenTensorNormalization.exactDerivedAdjunction adjS)
      (OpenTensorNormalization.exactDerivedAdjunction adjR)).symm
      (TwoSquare.mk _ _ _ _ (cbcDerivedSquare qS rU rT qR d.symm).hom)).natTrans =
        (cbcDerivedSquare rU JR JS rT e.symm).hom at hd
  rw [cbcDerivedSquare_symm, cbcDerivedSquare_symm] at hd
  exact equations_of_inverseMate _ _ _ _ hd

omit [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} B]
    [HasDerivedCategory.{wA} C] [HasDerivedCategory.{wA} D] in
private theorem equations_derived_tower
    [HasLimits A] [HasLimits B] [HasLimits C] [HasLimits D]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ C)] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ D)]
    (he : CbcAdjunctionCompatible e d adjS adjR) :
    CbcAdjunctionCompatible (cbcDerivedTowerSquare JS rT rU JR e)
      (cbcDerivedTowerSquare rT qR qS rU d)
      (cbcDerivedTowerAdjunction adjS) (cbcDerivedTowerAdjunction adjR) := by
  let : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      JS) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      JS) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      JR) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      JR) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      rT) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      rT) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      rU) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      rU) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      qS) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      qS) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      qR) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      qR) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact equations_derived _ _ _ _ (equations_tower e d adjS adjR he)

end EquationCalculus

section
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasLimits A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasLimits B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Compatibility with every strict augmentation, written via its ordinary-limit cone
and the universal derived-limit unit. These are precisely the canonical maps of the
signed Roos normalization, including quotient-tower completion units.
Source: Stacks 0941 (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
structure CbcAugmentationCompatible
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB)
    (lambda : LA ⋙ F.mapDerivedCategory ≅ cbcTowerDerived F ⋙ LB) : Prop where
  equation : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (Q : CochainComplex A ℤ)
    (gamma : (Functor.const ℕᵒᵖ).obj Q ⟶ X.asFunctor),
    F.mapDerivedCategory.map
        (DerivedCategory.Q.map (limit.lift X.asFunctor ⟨Q, gamma⟩) ≫ etaA.app X) ≫
      lambda.hom.app (DerivedCategory.Q.obj X) ≫ LB.map ((cbcTowerFactors F).hom.app X) =
    F.mapDerivedCategoryFactors.hom.app Q ≫ DerivedCategory.Q.map
      (limit.lift _ ((F.mapHomologicalComplex (.up ℤ)).mapCone ⟨Q, gamma⟩)) ≫
        etaB.app ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj X)

end
section CoherenceHelpers
universe v w u' v' w' c h r
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open RingedOpenScalar in
private theorem comparisonSheaves
    {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max c h r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c h r}]
    {R S : Sheaf J CommRingCat.{max c h r}} (U : C) (a : R ⟶ S) :
    ∃ e : localizedSystemExtension.{c, h, r} S U ⋙ scalars.{c, h, r} a ≅
      sliceScalars.{c, h, r} U a ⋙ localizedSystemExtension.{c, h, r} R U,
    (∀ (N : SheafOfModules.{max c h r} ((rings.{c, h, r} S).over U))
      (V : Cᵒᵖ) (phi : V.unop ⟶ U) (x : N.val.obj (op (Over.mk phi))),
      (e.hom.app N).val.app V (generator.{c, h, r} U S N V phi x) =
        generator.{c, h, r} U R ((sliceScalars.{c, h, r} U a).obj N) V phi x) ∧
    Equations e (restrictionIso.{c, h, r} U a)
      (localizedSystemAdjunction.{c, h, r} S U)
      (localizedSystemAdjunction.{c, h, r} R U) := by
  obtain ⟨p, hp, e, he, hq, ht⟩ := RingedOpenScalar.comparison.{c, h, r, 0} U a
  exact ⟨e, he, hq⟩

private theorem restriction_identity {C : Type c} [Category.{h} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max c h r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c h r}]
    {R S : Sheaf J CommRingCat.{max c h r}} (U : C) (a : R ⟶ S)
    (M : SheafOfModules.{max c h r} (RingedOpenScalar.rings S)) (V : (Over U)ᵒᵖ)
    (x : (((RingedOpenScalar.scalars.{c, h, r} a) ⋙
      localizedSystemRestriction.{c, h, r} R U).obj M).val.obj V) :
    ((RingedOpenScalar.restrictionIso.{c, h, r} U a).hom.app M).val.app V x = x := by
  rfl

private theorem exactProducts_of_epi {A : Type u} [Category.{v} A] [Abelian A]
    [HasCountableProducts A]
    (he : ∀ (X Y : ℕ → A) (f : ∀ n, X n ⟶ Y n),
      (∀ n, Epi (f n)) → Epi (Limits.Pi.map f)) : HasExactLimitsOfShape (Discrete ℕ) A := by
  let : (lim (J := Discrete ℕ) (C := A)).PreservesEpimorphisms := ⟨fun {X Y} f hf ↦ by
    have : ∀ n : ℕ, Epi (f.app ⟨n⟩) := fun n ↦ inferInstance
    have : Epi (Limits.Pi.map (fun n : ℕ ↦ f.app ⟨n⟩)) := he _ _ _ this
    have hmap : lim.map f = (Pi.isoLimit X).inv ≫
        Limits.Pi.map (fun n : ℕ ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit Y).hom := by
      apply limit.hom_ext
      rintro ⟨n⟩
      simp only [Category.assoc, Pi.isoLimit_hom_π, Limits.Pi.map_π,
        Pi.isoLimit_inv_π_assoc]
      exact limMap_π f ⟨n⟩
    rw [hmap]
    infer_instance
  ⟩
  exact hasExactLimitsOfShape_of_preservesEpi A (Discrete ℕ)

private theorem scalarProducts {C : Type c} [Category.{h} C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{r}}
    [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (a : R ⟶ S) (I : Type r) :
    PreservesLimitsOfShape (Discrete I) (SheafOfModules.restrictScalars.{r} a) := by
  let G := SheafOfModules.toSheaf.{r} R
  have : PreservesLimitsOfShape (Discrete I) (SheafOfModules.toSheaf.{r} S) :=
    ((moduleSheaves_colimits_forgetful S).2.2.2.2.2 (Discrete I)).1
  have : PreservesLimitsOfShape (Discrete I) G :=
    ((moduleSheaves_colimits_forgetful R).2.2.2.2.2 (Discrete I)).1
  have : ReflectsLimitsOfShape (Discrete I) G := reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : PreservesLimitsOfShape (Discrete I)
      (SheafOfModules.restrictScalars.{r} a ⋙ G) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete I) (SheafOfModules.toSheaf.{r} S))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ G

private theorem countableComparison {A : Type u} [Category.{v} A]
    {B : Type u'} [Category.{v'} B] [HasProducts.{v} A] [HasProducts.{v} B]
    (F : A ⥤ B) (h : ∀ (I : Type v) (N : I → A), IsIso (piComparison F N))
    (N : ℕ → A) : IsIso (piComparison F N) := by
  let : ∀ (N : ULift.{v} ℕ → A), PreservesLimit (Discrete.functor N) F :=
    fun N ↦ by
      have := h (ULift.{v} ℕ) N
      exact PreservesProduct.of_iso_comparison F N
  let : PreservesLimitsOfShape (Discrete (ULift.{v} ℕ)) F :=
    preservesLimitsOfShape_of_discrete F
  let : PreservesLimitsOfShape (Discrete ℕ) F :=
    preservesLimitsOfShape_of_equiv
      (Discrete.equivalence (Equiv.ulift : ULift.{v} ℕ ≃ ℕ)) F
  infer_instance

private theorem towerGrothendieck {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] :
    IsGrothendieckAbelian.{v} (ℕᵒᵖ ⥤ A) := by
  let G := separator A
  have hG := isSeparator_separator A
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : ℕᵒᵖ ↦ (evaluationLeftAdjoint A j).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext j
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight A j
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  let : HasSeparator (ℕᵒᵖ ⥤ A) := ⟨_, hS.isSeparator_coproduct⟩
  let : HasFilteredColimitsOfSize.{v, v} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{v, v} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact { locallySmall := ⟨fun P Q ↦ small_of_injective
    (f := fun f : P ⟶ Q ↦ f.app) (fun f g h ↦ NatTrans.ext h)⟩ }

section Normalization
open NormalizedLimitSquare RoosAdjunctionUnit
variable {A : Type u} [Category.{v} A] [Abelian A] [HasLimits A]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
  [IsGrothendieckAbelian.{v} (ℕᵒᵖ ⥤ A)]
  {LA : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A}
  {etaA : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LA}

private theorem corner_unit (a : Corner LA etaA)
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    etaA.app X ≫ a.theta.hom.app (DerivedCategory.Q.obj X) ≫ a.factors.hom.app X =
      DerivedCategory.Q.map (roosι X) := by
  let T := CochainComplex.kInjectiveResolutionFunctor.{v} (ℕᵒᵖ ⥤ A)
  let q : X ⟶ T.obj X := (CochainComplex.toKInjectiveResolution.{v} (ℕᵒᵖ ⥤ A)).app X
  have : QuasiIso q := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ X).2
  let theta : DerivedCategory.Q ⋙ LA ≅ roosF ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft DerivedCategory.Q a.theta ≪≫ a.factors
  have htheta : LA.map (DerivedCategory.Q.map q) ≫ theta.hom.app (T.obj X) =
      theta.hom.app X ≫ DerivedCategory.Q.map (roosF.map q) := theta.hom.naturality q
  have heta : DerivedCategory.Q.map (roosLimitFunctor.map q) ≫ etaA.app (T.obj X) =
      etaA.app X ≫ LA.map (DerivedCategory.Q.map q) := etaA.naturality q
  have hq : IsIso (DerivedCategory.Q.map (roosF.map q)) := by
    have he : DerivedCategory.Q.map (roosF.map q) =
        theta.inv.app X ≫ LA.map (DerivedCategory.Q.map q) ≫ theta.hom.app (T.obj X) := by
      rw [htheta, Iso.inv_hom_id_app_assoc]
    rw [he]
    infer_instance
  change etaA.app X ≫ theta.hom.app X = _
  apply (cancel_mono (DerivedCategory.Q.map (roosF.map q))).mp
  have hn := a.normalization (T.obj X) (fun _ ↦ inferInstance)
  change etaA.app (T.obj X) ≫ theta.hom.app (T.obj X) = _ at hn
  calc
    _ = etaA.app X ≫ LA.map (DerivedCategory.Q.map q) ≫ theta.hom.app (T.obj X) := by
      rw [Category.assoc, ← htheta]
    _ = DerivedCategory.Q.map (roosLimitFunctor.map q) ≫
        etaA.app (T.obj X) ≫ theta.hom.app (T.obj X) := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ z ≫ theta.hom.app (T.obj X)) heta.symm
    _ = _ := by
      rw [hn]
      exact (DerivedCategory.Q.map_comp _ _).symm.trans
        ((congrArg DerivedCategory.Q.map (roosι_natural q)).trans
          (DerivedCategory.Q.map_comp _ _))

variable {B : Type u'} [Category.{v'} B] [Abelian B] [HasLimits B]
  [HasDerivedCategory.{w'} B] [HasDerivedCategory.{w'} (ℕᵒᵖ ⥤ B)]
  {LB : DerivedCategory.{w'} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{w'} B}
  {etaB : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LB}
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

omit [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
    [IsGrothendieckAbelian.{v} (ℕᵒᵖ ⥤ A)] in
private theorem inclusion_coordinates (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosι X).f (p + 1) ≫ (coordinates X p).hom =
      biprod.lift ((Limits.Pi.lift (fun n : ℕ ↦ limit.π X.asFunctor (op n))).f (p + 1)) 0 := by
  dsimp only [coordinates, Iso.trans_hom]
  rw [← Category.assoc, ← Category.assoc, roosι_χ]
  apply biprod.hom_ext <;> simp [Category.assoc]

omit [IsGrothendieckAbelian.{v} (ℕᵒᵖ ⥤ A)] in
private theorem comparison_inclusion (a : Corner LA etaA) (b : Corner LB etaB)
    (c : Comparison a b F) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (roosι X) ≫ c.kappa.hom.app X =
      limit.lift _ ((F.mapHomologicalComplex (.up ℤ)).mapCone (limit.cone X.asFunctor)) ≫
        roosι ((towerComplex F).obj X) := by
  apply HomologicalComplex.Hom.ext
  funext i
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
  apply (cancel_mono (coordinates ((towerComplex F).obj X) p).hom).mp
  simp only [HomologicalComplex.comp_f, Category.assoc, Functor.mapHomologicalComplex_map_f]
  rw [c.coordinate_formula, ← Category.assoc, ← Category.assoc, ← F.map_comp,
    inclusion_coordinates, Category.assoc, inclusion_coordinates]
  apply biprod.hom_ext
  · simp only [Category.assoc]
    erw [biprod.map_fst]
    simp only [← Category.assoc, Functor.biprodComparison_fst]
    rw [← F.map_comp, biprod.lift_fst]
    simp only [Category.assoc, biprod.lift_fst]
    apply (cancel_mono (piComparison (HomologicalComplex.eval B (.up ℤ) (p + 1))
      (fun n : ℕ ↦ ((towerComplex F).obj X).asFunctor.obj (op n)))).mp
    apply Limits.Pi.hom_ext
    intro n
    simp only [Category.assoc, piComparison_comp_π, HomologicalComplex.eval_map]
    change ((F.mapHomologicalComplex (.up ℤ)).map
        (Limits.Pi.lift (fun n : ℕ ↦ limit.π X.asFunctor (op n)))).f (p + 1) ≫
      (piComparison (F.mapHomologicalComplex (.up ℤ))
        (fun n : ℕ ↦ X.asFunctor.obj (op n))).f (p + 1) ≫
      (Pi.π (fun n : ℕ ↦ ((towerComplex F).obj X).asFunctor.obj (op n)) n).f
        (p + 1) = _
    have hc := congrArg (fun z ↦ z.f (p + 1))
      (piComparison_comp_π (F.mapHomologicalComplex (.up ℤ))
        (fun n : ℕ ↦ X.asFunctor.obj (op n)) n)
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at hc
    erw [hc]
    change F.map ((Limits.Pi.lift (fun n : ℕ ↦
      limit.π X.asFunctor (op n))).f (p + 1)) ≫
        F.map ((Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n).f (p + 1)) = _
    rw [← F.map_comp, ← HomologicalComplex.comp_f, Limits.Pi.lift_π]
    have hb := congrArg (fun z ↦ z.f (p + 1))
      (limit.lift_π ((F.mapHomologicalComplex (.up ℤ)).mapCone
        (limit.cone X.asFunctor)) (op n))
    erw [← HomologicalComplex.comp_f, Limits.Pi.lift_π]
    exact hb.symm
  · simp only [Category.assoc]
    erw [biprod.map_snd]
    simp only [← Category.assoc, Functor.biprodComparison_snd]
    rw [← F.map_comp, biprod.lift_snd, F.map_zero, zero_comp]
    simp only [Category.assoc, biprod.lift_snd, comp_zero]

private theorem comparison_normalized
    [IsGrothendieckAbelian.{v'} (ℕᵒᵖ ⥤ B)]
    (a : Corner LA etaA) (b : Corner LB etaB) (c : Comparison a b F) :
    CbcLimitNormalized F LA LB etaA etaB c.lambda := by
  constructor
  intro X
  let Y := (towerComplex F).obj X
  let beta := limit.lift _ ((F.mapHomologicalComplex (.up ℤ)).mapCone
    (limit.cone X.asFunctor))
  apply (cancel_mono (b.theta.hom.app (DerivedCategory.Q.obj Y) ≫ b.factors.hom.app Y)).mp
  simp only [Category.assoc]
  erw [reassoc_of% (b.theta.hom.naturality ((towerFactors F).hom.app X))]
  rw [c.conjugation]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  dsimp only [Y]
  erw [← c.descent X]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, corner_unit]
  simp only [Category.assoc]
  rw [corner_unit a X]
  rw [reassoc_of% (F.mapDerivedCategoryFactors.hom.naturality (roosι X))]
  rw [← DerivedCategory.Q.map_comp, comparison_inclusion F a b c X,
    DerivedCategory.Q.map_comp]

omit [IsGrothendieckAbelian.{v} (ℕᵒᵖ ⥤ A)] in
private theorem normalized_augmentation
    (lambda : LA ⋙ F.mapDerivedCategory ≅ cbcTowerDerived F ⋙ LB)
    (hn : CbcLimitNormalized F LA LB etaA etaB lambda) :
    CbcAugmentationCompatible F LA LB etaA etaB lambda := by
  constructor
  intro X P gamma
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [hn.equation X]
  rw [reassoc_of% (F.mapDerivedCategoryFactors.hom.naturality
    (limit.lift X.asFunctor ⟨P, gamma⟩))]
  rw [← DerivedCategory.Q.map_comp_assoc]
  congr 2
  congr 1
  apply limit.hom_ext
  intro n
  simp only [Category.assoc, limit.lift_π]
  change (F.mapHomologicalComplex (.up ℤ)).map (limit.lift X.asFunctor ⟨P, gamma⟩) ≫
    (F.mapHomologicalComplex (.up ℤ)).map (limit.π X.asFunctor n) =
      (F.mapHomologicalComplex (.up ℤ)).map (gamma.app n)
  rw [← Functor.map_comp, limit.lift_π]

end Normalization
end CoherenceHelpers
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

section CoherentNormalization
variable {A B C D : Type uA} [Category.{vA} A] [Category.{vA} B]
  [Category.{vA} C] [Category.{vA} D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasLimits A] [HasLimits B] [HasLimits C] [HasLimits D]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} B]
  [HasDerivedCategory.{wA} C] [HasDerivedCategory.{wA} D]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ B)]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ C)] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ D)]
  [IsGrothendieckAbelian.{vA} (ℕᵒᵖ ⥤ A)] [IsGrothendieckAbelian.{vA} (ℕᵒᵖ ⥤ B)]
  [IsGrothendieckAbelian.{vA} (ℕᵒᵖ ⥤ C)] [IsGrothendieckAbelian.{vA} (ℕᵒᵖ ⥤ D)]
  {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {K : C ⥤ D}
  [F.Additive] [G.Additive] [H.Additive] [K.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits K] [PreservesFiniteColimits K]
  {LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A}
  {LB : DerivedCategory.{wA} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wA} B}
  {LC : DerivedCategory.{wA} (ℕᵒᵖ ⥤ C) ⥤ DerivedCategory.{wA} C}
  {LD : DerivedCategory.{wA} (ℕᵒᵖ ⥤ D) ⥤ DerivedCategory.{wA} D}
  {etaA : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LA}
  {etaB : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LB}
  {etaC : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LC}
  {etaD : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LD}
  {e : F ⋙ G ≅ H ⋙ K}

private theorem coherent_normalizations
    (c : NormalizedLimitSquare.Coherence F G H K LA etaA LB etaB LC etaC LD etaD e) :
    ∃ (lF : LA ⋙ F.mapDerivedCategory ≅ cbcTowerDerived F ⋙ LB)
      (lG : LB ⋙ G.mapDerivedCategory ≅ cbcTowerDerived G ⋙ LD)
      (lH : LA ⋙ H.mapDerivedCategory ≅ cbcTowerDerived H ⋙ LC)
      (lK : LC ⋙ K.mapDerivedCategory ≅ cbcTowerDerived K ⋙ LD),
      CbcLimitNormalized F LA LB etaA etaB lF ∧ CbcLimitNormalized G LB LD etaB etaD lG ∧
      CbcLimitNormalized H LA LC etaA etaC lH ∧ CbcLimitNormalized K LC LD etaC etaD lK ∧
      CbcAugmentationCompatible F LA LB etaA etaB lF ∧
      CbcAugmentationCompatible G LB LD etaB etaD lG ∧
      CbcAugmentationCompatible H LA LC etaA etaC lH ∧
      CbcAugmentationCompatible K LC LD etaC etaD lK ∧
      ∀ M : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A),
        G.mapDerivedCategory.map (lF.hom.app M) ≫
          lG.hom.app ((cbcTowerDerived F).obj M) ≫
          LD.map ((cbcDerivedTowerSquare F G H K e).hom.app M) =
        (cbcDerivedSquare F G H K e).hom.app (LA.obj M) ≫
          K.mapDerivedCategory.map (lH.hom.app M) ≫
          lK.hom.app ((cbcTowerDerived H).obj M) := by
  -- Accept both the existential API and the preceding published record API.
  first
  | have nF := comparison_normalized _ _ _ c.comparisonF
    have nG := comparison_normalized _ _ _ c.comparisonG
    have nH := comparison_normalized _ _ _ c.comparisonH
    have nK := comparison_normalized _ _ _ c.comparisonK
    refine ⟨c.comparisonF.lambda, c.comparisonG.lambda, c.comparisonH.lambda,
      c.comparisonK.lambda, nF, nG, nH, nK,
      normalized_augmentation _ _ nF, normalized_augmentation _ _ nG,
      normalized_augmentation _ _ nH, normalized_augmentation _ _ nK, ?_⟩
    exact c.normalized_square
  | cases c with
    | intro d h =>
      have nF := comparison_normalized _ _ _ d.comparisonF
      have nG := comparison_normalized _ _ _ d.comparisonG
      have nH := comparison_normalized _ _ _ d.comparisonH
      have nK := comparison_normalized _ _ _ d.comparisonK
      refine ⟨d.comparisonF.lambda, d.comparisonG.lambda, d.comparisonH.lambda,
        d.comparisonK.lambda, nF, nG, nH, nK,
        normalized_augmentation _ _ nF, normalized_augmentation _ _ nG,
        normalized_augmentation _ _ nH, normalized_augmentation _ _ nK, ?_⟩
      exact h.2.2.2.2.2.1

end CoherentNormalization

end CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Existing sheafification specialized to the site's fixed coefficient universe.
Source: Stacks 03CY (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcAbSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, 0} T

/-- Existing locally bijective description at the same coefficient universe.
Source: Stacks 03CY (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcAbLocallyBijective (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T

/-- Existing ring sheafification specialized to the same coefficient universe.
Source: Stacks 03CY (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcRingSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, 0} T

variable {T : Scheme.{u}} (U : T.ProEt)
  {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)

/-- The recorded exactness instance at the actual pro-etale site universes.
Source: Stacks 03DJ (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcExtensionAdditive (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    (localizedSystemExtension.{u + 1, u, 0} R U).Additive :=
  SheafOfModules.localizedSystemExtensionAdditive.{u + 1, u, 0} R U

/-- The recorded exactness instance at the actual pro-etale site universes.
Source: Stacks 03DJ (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcExtensionLimits (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    PreservesFiniteLimits (localizedSystemExtension.{u + 1, u, 0} R U) :=
  SheafOfModules.localizedSystemExtensionLimits.{u + 1, u, 0} R U

/-- The recorded exactness instance at the actual pro-etale site universes.
Source: Stacks 03DJ (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcExtensionColimits (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    PreservesFiniteColimits (localizedSystemExtension.{u + 1, u, 0} R U) :=
  SheafOfModules.localizedSystemExtensionColimits.{u + 1, u, 0} R U

/-- The recorded exactness instance at the actual pro-etale site universes.
Source: Stacks 03DJ (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcRestrictionAdditive (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    (localizedSystemRestriction.{u + 1, u, 0} R U).Additive :=
  SheafOfModules.localizedSystemRestrictionAdditive.{u + 1, u, 0} R U

/-- The recorded exactness instance at the actual pro-etale site universes.
Source: Stacks 03DJ (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcRestrictionLimits (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    PreservesFiniteLimits (localizedSystemRestriction.{u + 1, u, 0} R U) :=
  SheafOfModules.localizedSystemRestrictionLimits.{u + 1, u, 0} R U

/-- The recorded exactness instance at the actual pro-etale site universes.
Source: Stacks 03DJ (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcRestrictionColimits (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    PreservesFiniteColimits (localizedSystemRestriction.{u + 1, u, 0} R U) :=
  SheafOfModules.localizedSystemRestrictionColimits.{u + 1, u, 0} R U

/-- The actual restricted coefficient morphism on the slice presentation of the open.
Source: Stacks 03DI (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
abbrev cbcSliceCoefficientMap :=
  ((ProEt.topology T).overPullback CommRingCat.{u + 1} U).map a

/-- Scalar restriction on the literal restricted ring sheaves. The explicit type retains
Mathlib's ringed slice presentation; the data is the recorded restriction functor itself.
Source: Stacks 03DI (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
def cbcSliceScalarRestriction :
    ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over U) ⥤
      ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U) :=
  RingedOpenScalar.sliceScalars.{u + 1, u, 0} U a

/-- Additivity of the existing scalar functor, in the literal slice presentation.
Source: Stacks 03DA (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcSliceScalarAdditive : (cbcSliceScalarRestriction U a).Additive :=
  inferInstanceAs (scalarRestriction.{u + 1, u, u + 1} (cbcSliceCoefficientMap U a)).Additive

open Classical in
/-- The sheafified image of one actual extension-presheaf generator.
Source: Stacks 03DI and 03CY (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
def cbcExtensionGenerator (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (N : ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)) (V : T.ProEtᵒᵖ)
    (phi : V.unop ⟶ U) (x : N.val.obj (op (Over.mk phi))) :
    ((localizedSystemExtension.{u + 1, u, 0} R U).obj N).val.obj V :=
  RingedOpenScalar.generator.{u + 1, u, 0} U R N V phi x

variable [HasDerivedCategory.{wA} (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over
  U))]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over
    U))]
variable [HasDerivedCategory.{wA} (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over
  U))]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over
    U))]
variable [HasDerivedCategory.{wA} (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R))]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R))]
variable [HasDerivedCategory.{wA} (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S))]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S))]

/-- The recorded scalar-restriction exactness in the literal slice presentation.
Source: Stacks 03DA (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcSliceScalarLimits : PreservesFiniteLimits (cbcSliceScalarRestriction U a) :=
  letI : HasDerivedCategory.{wA}
      (scalarModules.{u + 1, u, u + 1} ((ProEt.topology T).over U) (R.over U)) :=
    inferInstanceAs (HasDerivedCategory.{wA}
      (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)))
  letI : HasDerivedCategory.{wA}
      (scalarModules.{u + 1, u, u + 1} ((ProEt.topology T).over U) (S.over U)) :=
    inferInstanceAs (HasDerivedCategory.{wA}
      (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over U)))
  scalarRestriction_limits.{u + 1, u, u + 1, wA} (cbcSliceCoefficientMap U a)

/-- The recorded scalar-restriction exactness in the literal slice presentation.
Source: Stacks 03DA (blueprint: lem-cbc-ringed-open-scalar-limit-coherence). -/
instance cbcSliceScalarColimits : PreservesFiniteColimits (cbcSliceScalarRestriction U a) :=
  letI : HasDerivedCategory.{wA}
      (scalarModules.{u + 1, u, u + 1} ((ProEt.topology T).over U) (R.over U)) :=
    inferInstanceAs (HasDerivedCategory.{wA}
      (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)))
  letI : HasDerivedCategory.{wA}
      (scalarModules.{u + 1, u, u + 1} ((ProEt.topology T).over U) (S.over U)) :=
    inferInstanceAs (HasDerivedCategory.{wA}
      (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over U)))
  scalarRestriction_colimits.{u + 1, u, u + 1, wA} (cbcSliceCoefficientMap U a)

attribute [local irreducible] localizedSystemAdjunction
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
attribute [local irreducible] Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategoryCompIso
  RingedOpenScalar.derivedSquare cbcDerivedSquare

attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
attribute [local instance] cbcAbSheafify cbcAbLocallyBijective
private theorem ambient_exact (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u + 1}
      (proEtaleModuleCoefficients R)) := by
  let : Abelian (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R)) :=
    RingedOpenScalar.ambientAbelian.{u + 1, u, 0} _
  apply CategoryTheory.exactProducts_of_epi
  intro X Y f hf
  exact (ProEt.countableProducts_exact.{u, 0, 0} T R).2.2 ℕ X Y f hf

private theorem slice_exact {T : Scheme.{u}} (U : T.ProEt)
    [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u + 1}
      ((proEtaleModuleCoefficients R).over U)) := by
  let : Abelian (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R)) :=
    RingedOpenScalar.ambientAbelian.{u + 1, u, 0} _
  let : Abelian (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)) :=
    RingedOpenScalar.sliceAbelian.{u + 1, u, 0} U _
  let Z : TopologicalSpace.Closeds T :=
    ⟨(Set.range U.hom)ᶜ, (IsOpenImmersion.isOpen_range U.hom).isClosed_compl⟩
  let i := (IdealSheafData.vanishingIdeal Z).subschemeι
  have hi : Set.range i = (Z : Set T) :=
    (IdealSheafData.reduced_induced_closed_subscheme T Z).2.2.2.2.2.1
  have hU : Set.range U.hom = (Set.range i)ᶜ := by
    rw [hi]
    exact (compl_compl _).symm
  obtain ⟨q, hq, ai, aj, hci, hu, hz, hz', hl, hc, hi', hci', hs, hfiltered⟩ :=
    proEtale_ringed_open_closed i U hU R
  let : HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R)) := ambient_exact T R
  have : ∀ M, IsIso (aj.unit.app M) := hu
  have : IsIso aj.unit := NatIso.isIso_of_isIso_app _
  let ff := aj.fullyFaithfulLOfIsIsoUnit
  let := ff.full
  let := ff.faithful
  let : PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u + 1} (proEtaleModuleCoefficients R) U) :=
    SheafOfModules.localizedSystemRestrictionColimits.{u + 1, u, 0} R U
  exact aj.hasExactLimitsOfShape (Discrete ℕ)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] cbcDerivedTowerSquare cbcDerivedTowerAdjunction
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapHomologicalComplex NatIso.mapHomologicalComplex

/-- Scalar restriction and open extension commute canonically, compatibly with their
adjunctions and with the specified normalized inverse-limit comparisons.

Source: Stacks 09BP, 03DI, 03DJ and 03CY; the completed-extension-zero blueprint proof
(blueprint: lem-cbc-ringed-open-scalar-limit-coherence).

Proof plan, following the node:

1. Use the slice-site identification of [lem-weil-proetale-weakly-etale-localization]. For an
$S_U$-module sheaf $N$, the two extension presheaves have the same abelian groups and restriction
maps: at $V$ they are $\bigoplus_{\varphi:V\to U}N(V,\varphi)$. Their $R(V)$-actions are both
$r(s_\varphi)_\varphi=(a_V(r)s_\varphi)_\varphi$, by [def-pc-sheaf-restrict-scalars, def-weil-
extension-by-zero-presheaf]. By [def-weil-presheaf-modules-sheafification], their abelian
sheafifications coincide and the induced $R$-actions coincide by uniqueness of the extending
action. The identity thus induces $e_N:r_TJ_SN\to J_Rr_UN$ and its inverse. A map of $N$ acts on
each summand by the same map on either side, so $e$ is natural.

2. For the adjunction of [lem-pur-site-restriction-module-adjunction-exact], a map $h:N\to j^*Q$
extends to $J N\to Q$ by sending the generator $s$ in the summand indexed by $\varphi:V\to U$ to
$h_{(V,\varphi)}(s)\in Q(V)$, then using sheafification. Conversely restrict such a map and
precompose with the summand inclusion; these operations are inverse since all summand generators
generate the presheaf and sheafification has unique factorization. Consequently $\eta_N$ sends
$s$ to its summand generator followed by sheafification and $\epsilon_Q$ sends each generator to
the same section of $Q(V)$. Scalar restriction changes none of these maps. Also
$j_R^*r_T=r_Uj_S^*$ objectwise. Thus $j_R^*(e_N)\,r_U(\eta_N^S)=\eta_{r_UN}^R$ and
$\epsilon_{r_TQ}^R\,e_{j_S^*Q}=r_T(\epsilon_Q^S)$, with the displayed restriction identification
understood.

3. Scalar restriction preserves kernels because they are sectionwise kernels with the restricted
action; it preserves cokernels because sectionwise quotient groups and their abelian
sheafification are unchanged, with the unique restricted action. These kernel/cokernel
descriptions are [def-weil-sheaf-of-modules-category], and the action is [def-pc-sheaf-restrict-
scalars]. Hence $r_U,r_T$ are exact. Both $J$ and both $j^*$ are exact by [lem-pur-site-
restriction-module-adjunction-exact]. For strict towers the same conclusions hold levelwise by
[lem-weil-tower-category-levelwise-abelian]; the natural transformations of Steps 1–2 satisfy the
tower transition equations by their naturality. Apply all functors and transformations in every
cochain degree. Exactness permits descent to the unbounded derived categories by [lem-sf-exact-
functor-derived-triangulated]. The derived adjunction of [def-weil-exact-derived-adjunction] has
the localized original unit and counit, so the identities in Step 2 descend as well.

4. By [lem-weil-pbc-module-sheaves-limits-sectionwise], a product is the sectionwise product with
coordinate actions. Thus restricting scalars gives exactly the same underlying product and
projections, including the empty product, whose underlying group is zero. Invertibility of the
canonical product comparisons for $J_R,J_S$ is [lem-cbc-ringed-open-extension-products],
applicable since $j$ is quasi-compact; the base need not be quasi-compact or quasi-separated.
Countable products are exact in each of the four ringed categories by [lem-weil-proetale-
countable-products-exact], for arbitrary ring sheaves. Together with Step 3 this verifies all
hypotheses of [lem-cbc-exact-product-functor-strict-limit] for each of $r_T,J_S,J_R,r_U$. Write
$\phi_F$ for their canonical product maps and $\kappa_F$ for the maps on the two signed Roos
summands specified by that node.

5. Hereafter set $A=r_TJ_S$ and $B=J_Rr_U$. For any countable family $(N_n)$ in
$\operatorname{Mod}(S_U)$, with $P=\prod_nN_n$, form
$$u=(\prod_ne_{N_n})\,\phi_{r_T,(J_SN_n)}\,r_T(\phi_{J_S,(N_n)}),\qquad
v=\phi_{J_R,(r_UN_n)}\,J_R(\phi_{r_U,(N_n)})\,e_P.$$ Both have domain $AP$ and codomain
$\prod_nBN_n$. For every projection $\pi_n$ the defining projection equations for $\phi$ give
$\pi_nu=e_{N_n}A(\pi_n)$ and $\pi_nv=B(\pi_n)e_P$. These are equal by naturality of $e$ from Step
1, so $u=v$ by the product universal property. This is a calculation with the canonical maps of
[lem-cbc-exact-product-functor-strict-limit], rather than a choice of a product isomorphism.

6. For a strict tower complex $M$, let $H_M^q=P_M^q\oplus P_M^{q-1}$ and $d(x,y)=(dx,(1-s)x-dy)$,
as fixed in [lem-cbc-exact-product-functor-strict-limit]. Apply Step 5 separately to the families
$(M_n^q)_n$ and $(M_n^{q-1})_n$. Naturality of $e$ for the two biproduct projections shows that
$e_{H_M}$ is diagonal in these coordinates. Its naturality for the differentials and transitions
shows that the resulting equality is an equality of chain maps, with the same minus sign on both
sides. In notation $$K_A=\kappa_{r_T,J_SM}\,r_T(\kappa_{J_S,M}),\qquad
K_B=\kappa_{J_R,r_UM}\,J_R(\kappa_{r_U,M}),$$ the equality is $$H(e_M)K_A=K_Be_{H_M}.$$ All maps
are natural for strict tower chain maps. The cited normalized comparison provides their descent
to the derived categories.

7. Let $\theta$ denote the normalized natural isomorphism $L\to H$ of [lem-cbc-exact-product-
functor-strict-limit]; its normalization agrees with K-injective resolution, not just with an
unspecified Roos triangle. Substitute $\lambda_{F,M}=\theta_{FM}^{-1}\kappa_{F,M}F(\theta_M)$ in
the left-hand side of the required equation. The middle factors $r_T(\theta_{J_SM})$ and its
inverse cancel. Naturality of the target $\theta$ for $e_M:AM\to BM$ then makes that side
$$\theta_{BM}^{-1}H(e_M)K_A A(\theta_M).$$ Substitute the same formula on the right-hand side and
cancel $J_R(\theta_{r_UM})$ with its inverse. Naturality of the derived $e$ for $\theta_M:LM\to
H_M$ gives $B(\theta_M)e_{LM}=e_{H_M}A(\theta_M)$, so the right-hand side is
$$\theta_{BM}^{-1}K_Be_{H_M}A(\theta_M).$$ Step 6 proves these expressions equal. The four
functor occurrences and the target limit are exactly those in the statement. Naturality of
$\lambda$ and $e$ makes the resulting equality natural for every derived strict-tower morphism,
including morphisms represented by roofs.

8. For a strict augmentation $\gamma:\Delta C\to M$, [lem-cbc-exact-product-functor-strict-limit]
states that $\lambda_F\,F(u_\gamma)=u_{F\gamma}$. In the signed coordinates this is the equality
sending $c$ to $((F\gamma_n)(c),0)$, since $\phi_F$ is characterized by its projections. Apply
this assertion successively along $J_S,r_T$ and along $r_U,J_R$. Naturality of $e$ at $\gamma_n$
identifies the resulting augmentations: $e_{M_n}A(\gamma_n)=B(\gamma_n)e_C$. Step 7 therefore
identifies their canonical derived maps after either composite. A quotient-tower completion unit
is the map of its strict quotient augmentation, so it is included. In particular exactness
preserves the quotient maps used in such an augmentation. The argument used neither preservation
of K-injectives by scalar restriction nor tensoring along $a$; no flatness or boundedness is
needed.
-/
theorem ringedOpenScalarLimitCoherence
    [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (LUR : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
        R).over U)) ⥤
      DerivedCategory.{wA} (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)))
    (etaUR : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LUR)
    (_hUR : LUR.IsRightDerivedFunctor etaUR
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
        R).over U)) (.up
        ℤ)))
    (LUS : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
      S).over U)) ⥤
      DerivedCategory.{wA} (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over U)))
    (etaUS : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LUS)
    (_hUS : LUS.IsRightDerivedFunctor etaUS
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
        S).over U)) (.up
        ℤ)))
    (LTR : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R)) ⥤
      DerivedCategory.{wA} (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R)))
    (etaTR : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LTR)
    (_hTR : LTR.IsRightDerivedFunctor etaTR
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R))
        (.up
        ℤ)))
    (LTS : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S)) ⥤
      DerivedCategory.{wA} (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S)))
    (etaTS : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LTS)
    (_hTS : LTS.IsRightDerivedFunctor etaTS
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S))
        (.up
        ℤ)))
    : ∃ (e : (localizedSystemExtension.{u + 1, u, 0} S U) ⋙ (scalarRestriction.{u + 1, u, u + 1} a)
      ≅
        (cbcSliceScalarRestriction U a) ⋙
          (localizedSystemExtension.{u + 1, u, 0} R
          U))
      (d : (scalarRestriction.{u + 1, u, u + 1} a) ⋙ (localizedSystemRestriction.{u + 1, u, 0} R U)
        ≅
        (localizedSystemRestriction.{u + 1, u, 0} S U) ⋙ (cbcSliceScalarRestriction U a)),
      (∀ (N : ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over U))
        (V : T.ProEtᵒᵖ) (phi : V.unop ⟶ U) (x : N.val.obj (op (Over.mk phi))),
        (e.hom.app N).val.app V (cbcExtensionGenerator U S N V phi x) =
          cbcExtensionGenerator U R
            ((cbcSliceScalarRestriction U a).obj N) V phi x) ∧
      (∀ (Q : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S)) (V : (Over U)ᵒᵖ)
        (x : ((scalarRestriction.{u + 1, u, u + 1} a ⋙ localizedSystemRestriction.{u + 1, u, 0} R
          U).obj Q).val.obj
          V),
        (d.hom.app Q).val.app V x = x) ∧
      CbcAdjunctionCompatible
        (JS := localizedSystemExtension.{u + 1, u, 0} S U)
        (JR := localizedSystemExtension.{u + 1, u, 0} R U)
        (rT := scalarRestriction.{u + 1, u, u + 1} a)
        (rU := cbcSliceScalarRestriction U a)
        (qS := localizedSystemRestriction.{u + 1, u, 0} S U)
        (qR := localizedSystemRestriction.{u + 1, u, 0} R U)
        e d (localizedSystemAdjunction.{u + 1, u, 0} S U)
        (localizedSystemAdjunction.{u + 1, u, 0} R U) ∧
      CbcAdjunctionCompatible
        (JS := (localizedSystemExtension.{u + 1, u, 0} S U).mapHomologicalComplex (.up ℤ))
        (JR := (localizedSystemExtension.{u + 1, u, 0} R U).mapHomologicalComplex (.up ℤ))
        (rT := (scalarRestriction.{u + 1, u, u + 1} a).mapHomologicalComplex (.up ℤ))
        (rU := (cbcSliceScalarRestriction U a).mapHomologicalComplex (.up ℤ))
        (qS := (localizedSystemRestriction.{u + 1, u, 0} S U).mapHomologicalComplex (.up ℤ))
        (qR := (localizedSystemRestriction.{u + 1, u, 0} R U).mapHomologicalComplex (.up ℤ))
        (cbcComplexSquare (localizedSystemExtension.{u + 1, u, 0} S U)
          (scalarRestriction.{u + 1, u, u + 1} a) (cbcSliceScalarRestriction U a)
          (localizedSystemExtension.{u + 1, u, 0} R U) e)
        (cbcComplexSquare (scalarRestriction.{u + 1, u, u + 1} a)
          (localizedSystemRestriction.{u + 1, u, 0} R U)
          (localizedSystemRestriction.{u + 1, u, 0} S U) (cbcSliceScalarRestriction U a) d)
        ((localizedSystemAdjunction.{u + 1, u, 0} S U).mapHomologicalComplex (.up ℤ))
        ((localizedSystemAdjunction.{u + 1, u, 0} R U).mapHomologicalComplex (.up ℤ)) ∧
      CbcAdjunctionCompatible
        (JS := cbcTowerDerived (localizedSystemExtension.{u + 1, u, 0} S U))
        (JR := cbcTowerDerived (localizedSystemExtension.{u + 1, u, 0} R U))
        (rT := cbcTowerDerived (scalarRestriction.{u + 1, u, u + 1} a))
        (rU := cbcTowerDerived (cbcSliceScalarRestriction U a))
        (qS := cbcTowerDerived (localizedSystemRestriction.{u + 1, u, 0} S U))
        (qR := cbcTowerDerived (localizedSystemRestriction.{u + 1, u, 0} R U))
        (cbcDerivedTowerSquare (localizedSystemExtension.{u + 1, u, 0} S U) (scalarRestriction.{u +
          1, u, u + 1} a)
          (cbcSliceScalarRestriction U a)
            (localizedSystemExtension.{u + 1, u, 0} R
            U) e)
        (cbcDerivedTowerSquare (scalarRestriction.{u + 1, u, u + 1} a)
          (localizedSystemRestriction.{u + 1, u, 0} R U)
          (localizedSystemRestriction.{u + 1, u, 0} S U) (cbcSliceScalarRestriction U a) d)
        (cbcDerivedTowerAdjunction (localizedSystemAdjunction.{u + 1, u, 0} S U))
        (cbcDerivedTowerAdjunction (localizedSystemAdjunction.{u + 1, u, 0} R U)) ∧
      HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
        R).over U)) ∧
      HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
        S).over U)) ∧
      HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R))
        ∧
      HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S))
        ∧
      (∀ (I : Type (u + 1)) (N : I → ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over
        U)),
        IsIso (piComparison (localizedSystemExtension.{u + 1, u, 0} S U) N)) ∧
      (∀ (I : Type (u + 1)) (N : I → ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over
        U)),
        IsIso (piComparison (localizedSystemExtension.{u + 1, u, 0} R U) N)) ∧
      (∀ (I : Type (u + 1)) (N : I → ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S)),
        IsIso (piComparison (scalarRestriction.{u + 1, u, u + 1} a) N)) ∧
      (∀ (I : Type (u + 1)) (N : I → ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over
        U)),
        IsIso (piComparison (cbcSliceScalarRestriction U a) N)) ∧
      ∃ (lambdaJS : LUS ⋙ (localizedSystemExtension.{u + 1, u, 0} S U).mapDerivedCategory ≅
          cbcTowerDerived (localizedSystemExtension.{u + 1, u, 0} S U) ⋙ LTS)
        (lambdarT : LTS ⋙ (scalarRestriction.{u + 1, u, u + 1} a).mapDerivedCategory ≅
          cbcTowerDerived (scalarRestriction.{u + 1, u, u + 1} a) ⋙ LTR)
        (lambdarU : LUS ⋙ (cbcSliceScalarRestriction U a).mapDerivedCategory ≅
          cbcTowerDerived (cbcSliceScalarRestriction U a) ⋙ LUR)
        (lambdaJR : LUR ⋙ (localizedSystemExtension.{u + 1, u, 0} R U).mapDerivedCategory ≅
          cbcTowerDerived (localizedSystemExtension.{u + 1, u, 0} R U) ⋙ LTR),
        CbcLimitNormalized (localizedSystemExtension.{u + 1, u, 0} S U) LUS LTS etaUS etaTS lambdaJS
          ∧
        CbcLimitNormalized (scalarRestriction.{u + 1, u, u + 1} a) LTS LTR etaTS etaTR lambdarT ∧
        CbcLimitNormalized (cbcSliceScalarRestriction U a) LUS
          LUR etaUS etaUR
          lambdarU ∧
        CbcLimitNormalized (localizedSystemExtension.{u + 1, u, 0} R U) LUR LTR etaUR etaTR lambdaJR
          ∧
        CbcAugmentationCompatible (localizedSystemExtension.{u + 1, u, 0} S U) LUS LTS
          etaUS etaTS lambdaJS ∧
        CbcAugmentationCompatible (scalarRestriction.{u + 1, u, u + 1} a) LTS LTR
          etaTS etaTR lambdarT ∧
        CbcAugmentationCompatible (cbcSliceScalarRestriction U a)
          LUS LUR
          etaUS etaUR lambdarU ∧
        CbcAugmentationCompatible (localizedSystemExtension.{u + 1, u, 0} R U) LUR LTR
          etaUR etaTR lambdaJR ∧
        ∀ M : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
          S).over U)),
          (scalarRestriction.{u + 1, u, u + 1} a).mapDerivedCategory.map (lambdaJS.hom.app M) ≫
            lambdarT.hom.app ((cbcTowerDerived (localizedSystemExtension.{u + 1, u, 0} S U)).obj M)
              ≫
            LTR.map ((cbcDerivedTowerSquare (localizedSystemExtension.{u + 1, u, 0} S U)
              (scalarRestriction.{u + 1, u, u + 1} a)
              (cbcSliceScalarRestriction U a)
                (localizedSystemExtension.{u + 1, u,
                0} R U)
              e).hom.app M) =
          (cbcDerivedSquare (localizedSystemExtension.{u + 1, u, 0} S U) (scalarRestriction.{u + 1,
            u, u + 1} a)
            (cbcSliceScalarRestriction U a) (localizedSystemExtension.{u + 1, u, 0} R U) e).hom.app
              (LUS.obj M) ≫
            (localizedSystemExtension.{u + 1, u, 0} R U).mapDerivedCategory.map (lambdarU.hom.app M)
              ≫
            lambdaJR.hom.app ((cbcTowerDerived (cbcSliceScalarRestriction U a)).obj
              M) := by
  let : PreservesFiniteLimits (scalarRestriction.{u + 1, u, u + 1} a) :=
    scalarRestriction_limits.{u + 1, u, u + 1, wA} a
  let : PreservesFiniteColimits (scalarRestriction.{u + 1, u, u + 1} a) :=
    scalarRestriction_colimits.{u + 1, u, u + 1, wA} a
  have hc := CategoryTheory.comparisonSheaves.{u + 1, u, 0}
    (C := T.ProEt) (J := ProEt.topology T) (R := R) (S := S) U a
  rcases hc with ⟨e, he, heq⟩
  let d := RingedOpenScalar.restrictionIso.{u + 1, u, 0} U a
  have heq : CbcAdjunctionCompatible e d
      (localizedSystemAdjunction.{u + 1, u, 0} S U)
      (localizedSystemAdjunction.{u + 1, u, 0} R U) := heq
  refine ⟨e, d, he, ?_, heq, CategoryTheory.equations_complex _ _ _ _ heq, ?_⟩
  · exact CategoryTheory.restriction_identity.{u + 1, u, 0} U a
  · refine ⟨CategoryTheory.equations_derived_tower
      (rU := cbcSliceScalarRestriction U a)
      (rT := scalarRestriction.{u + 1, u, u + 1} a) _ _ _ _ heq, ?_⟩
    let := slice_exact U R
    let := slice_exact U S
    let := ambient_exact T R
    let := ambient_exact T S
    have hJS (I : Type (u + 1))
        (N : I → ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over U)) :
        IsIso (piComparison (localizedSystemExtension.{u + 1, u, 0} S U) N) :=
      (proEtaleRingedExtensionByZero_products U S I N).1
    have hJR (I : Type (u + 1))
        (N : I → ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)) :
        IsIso (piComparison (localizedSystemExtension.{u + 1, u, 0} R U) N) :=
      (proEtaleRingedExtensionByZero_products U R I N).1
    have hrT (I : Type (u + 1))
        (N : I → ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S)) :
        IsIso (piComparison (scalarRestriction.{u + 1, u, u + 1} a) N) := by
      let := CategoryTheory.scalarProducts.{u + 1, u, u + 1}
        ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a) I
      infer_instance
    have hrU (I : Type (u + 1))
        (N : I → ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over U)) :
        IsIso (piComparison (cbcSliceScalarRestriction U a) N) := by
      let := CategoryTheory.scalarProducts.{u + 1, u, u + 1}
        (((ProEt.topology T).overPullback RingCat.{u + 1} U).map
          ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a)) I
      change IsIso (piComparison (RingedOpenScalar.sliceScalars.{u + 1, u, 0} U a) N)
      infer_instance
    refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
      hJS, hJR, hrT, hrU, ?_⟩
    have comm (B : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
        (V : T.ProEtᵒᵖ) (x y : (proEtaleModuleCoefficients B).obj.obj V) :
        x * y = y * x := by
      exact mul_comm (G := B.obj.obj _) x y
    have commU (B : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
        (V : (Over U)ᵒᵖ) (x y : ((proEtaleModuleCoefficients B).over U).obj.obj V) :
        x * y = y * x := by
      exact mul_comm (G := B.obj.obj _) x y
    obtain ⟨c⟩ := CategoryTheory.NormalizedLimitSquare.normalizedLimitSquareCoherence.{
        wA, wA, wA, wA, u + 1, u, u + 1, u + 1, u, u + 1,
        u + 1, u, u + 1, u + 1, u, u + 1}
      ((ProEt.topology T).over U) ((proEtaleModuleCoefficients S).over U) (commU S)
      (ProEt.topology T) (proEtaleModuleCoefficients S) (comm S)
      ((ProEt.topology T).over U) ((proEtaleModuleCoefficients R).over U) (commU R)
      (ProEt.topology T) (proEtaleModuleCoefficients R) (comm R)
      (localizedSystemExtension.{u + 1, u, 0} S U)
        (CategoryTheory.countableComparison _ hJS)
      (scalarRestriction.{u + 1, u, u + 1} a)
        (CategoryTheory.countableComparison _ hrT)
      (cbcSliceScalarRestriction U a) (CategoryTheory.countableComparison _ hrU)
      (localizedSystemExtension.{u + 1, u, 0} R U)
        (CategoryTheory.countableComparison _ hJR)
      e LUS etaUS _hUS LTS etaTS _hTS LUR etaUR _hUR LTR etaTR _hTR
    let := SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
      ((ProEt.topology T).over U) ((proEtaleModuleCoefficients S).over U)
    let := SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
      ((ProEt.topology T).over U) ((proEtaleModuleCoefficients R).over U)
    let := SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
      (ProEt.topology T) (proEtaleModuleCoefficients S)
    let := SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
      (ProEt.topology T) (proEtaleModuleCoefficients R)
    let := CategoryTheory.towerGrothendieck
      (A := ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over U))
    let := CategoryTheory.towerGrothendieck
      (A := ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U))
    let := CategoryTheory.towerGrothendieck
      (A := ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S))
    let := CategoryTheory.towerGrothendieck
      (A := ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R))
    exact CategoryTheory.coherent_normalizations c

end AlgebraicGeometry.Scheme
