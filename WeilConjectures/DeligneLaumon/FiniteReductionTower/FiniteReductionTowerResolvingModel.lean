/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CompletedTowerIndependent.IntegralCompletedTowerPullbackUniverses
public import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import WeilConjectures.DeligneLaumon.FiniteReductionTower.FiniteReductionAdditiveCompatibility
import WeilConjectures.DeligneLaumon.FiniteReductionTower.FiniteReductionScalarNormalization
import all WeilConjectures.DeligneLaumon.CompletedTowerIndependent.IntegralCompletedTowerPullbackUniverses
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Localization.Construction
import all Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all Mathlib.CategoryTheory.Functor.Currying
import all Mathlib.CategoryTheory.Whiskering
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.CategoryTheory.Localization.Prod
import all Mathlib.Algebra.Homology.BifunctorFlip
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Localization.CalculusOfFractions
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import all WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement

/-! # Resolving models for finite reduction and strict tower pullback

Source: Stacks Project, derived.tex Tag 06XN, lemma-find-existence-computes,
left-derived assertion; sites-cohomology.tex Tags 06YS, 06YT, 06YP and 07A2
(blueprint: lem-a1-finite-reduction-tower-resolving-model).

The natural index n represents the positive exponent n+1. All localizations below
are localizations of complexes in the entire strict tower category. The explicit
normalization identifies total tensor with the recorded scalar-extension model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedTowerIndependent
open WeilConjectures.PrincipalKoszulStrictReplacement
  (sourceTower targetTower sourceTowerMap targetTowerMap comparison residue)

namespace WeilConjectures.FiniteReductionTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{t}} (g : X ⟶ Y)

set_option genSizeOfSpec false
set_option genInjectivity false

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

end WeilConjectures.FiniteReductionTower

namespace WeilConjectures.FiniteReductionTower

/-- The shift comparison of B_g^0 is the identity on reindexed terms: at every level
it is the standard termwise shift of the additive finite-level functor, not a free
automorphism.
Source: Stacks 014E, 0FNH
(blueprint: lem-a1-finite-reduction-tower-resolving-model). -/
def ShiftNormalization
    (c : (integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).CommShift ℤ) :
    Prop :=
  ∀ (P : CochainComplex (Modules l E Y) ℤ) (r i : ℤ) (n : ℕ),
    letI := integralOperationsLevelPullback_additive l E g n
    (((Functor.commShiftIso (integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X)
        (self := c) r).hom.app P).f i).app (op n) =
      (((unrestrictedIntegralReductionFunctor l E Y n ⋙
          integralOperationsLevelPullback l E g n ⋙
          SheafOfModules.restrictScalars
            (limit.π (integralCoefficientSheafSystem l E X) (op n))).mapCochainComplexShiftIso
          r).hom.app P).f i

/-- The cone comparison of B_g^0 commutes with the cone inclusion and, through the
given shift, with the connecting map: the image of a standard cone triangle is the
standard cone triangle of the image.
Source: Stacks 014E, derived.tex situation-classical
(blueprint: lem-a1-finite-reduction-tower-resolving-model). -/
def ConeNormalization
    (c : (integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).CommShift ℤ)
    {P P' : CochainComplex (Modules l E Y) ℤ} (f : P ⟶ P')
    (e : (integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).obj
      (CochainComplex.mappingCone f) ≅ CochainComplex.mappingCone
        ((integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).map f)) : Prop :=
  (integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).map
      (CochainComplex.mappingCone.inr f) ≫ e.hom =
    CochainComplex.mappingCone.inr
      ((integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).map f) ∧
  e.hom ≫ (CochainComplex.mappingCone.triangle
      ((integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).map f)).mor₃ =
    (integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).map
        (CochainComplex.mappingCone.triangle f).mor₃ ≫
      (Functor.commShiftIso (integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X)
        (self := c) (1 : ℤ)).hom.app P

/-- The resolving-model assertions, including the universal pair and its specified
whole-tower computation. `normalization` sends p tensor s to s tensor p in the
existing scalar-extension presentation; it therefore fixes the reduction comparison.
`chi_formula` uses the inverse of the actual augmented strict Koszul tower.
Source: Stacks 06XN, 06YT, 06YP and 07A2
(blueprint: lem-a1-finite-reduction-tower-resolving-model). -/
structure ResolvingModel where
  /-- Homotopies are carried to homotopies of strict tower complexes. -/
  homotopy : ∀ {P P' : CochainComplex (Modules l E Y) ℤ} (f f' : P ⟶ P'),
    Homotopy f f' → Nonempty (Homotopy
      ((integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).map f)
      ((integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).map f'))
  /-- Integer shifts are respected before localization. -/
  shift : (integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).CommShift ℤ
  /-- The shift comparison is the termwise identity on reindexed terms. -/
  shift_normalization : ShiftNormalization l E g shift
  /-- Mapping-cone complexes are respected before localization. -/
  cone : ∀ {P P' : CochainComplex (Modules l E Y) ℤ} (f : P ⟶ P'),
    ((integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).obj
      (CochainComplex.mappingCone f)) ≅ CochainComplex.mappingCone
        ((integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).map f)
  /-- The cone comparison is an isomorphism of standard cone triangles. -/
  cone_normalization : ∀ {P P' : CochainComplex (Modules l E Y) ℤ} (f : P ⟶ P'),
    ConeNormalization l E g shift f (cone f)
  /-- The finite tower functor inverts quasi-isomorphisms between good complexes. -/
  quasiIso : ∀ {P P' : CochainComplex (Modules l E Y) ℤ} (f : P ⟶ P'),
    integralOperationsGoodComplex l E Y P → integralOperationsGoodComplex l E Y P' →
    QuasiIso f → ∀ n : ℕ,
      QuasiIso (((integralOperationsPullbackTowerFunctor l E g).map f).app (op n))
  /-- The everywhere defined derived functor, universal counit and good computation. -/
  B : DerivedPair l E Y X
    (integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X)
  /-- The strict Koszul augmentation is a quasi-isomorphism of whole towers. -/
  augmentation_quasiIso : ∀ P : CochainComplex (Modules l E Y) ℤ,
    integralOperationsGoodComplex l E Y P →
      QuasiIso ((transpose l E Y).map (comparison l E Y P))
  /-- Each source level remains K-flat with flat terms. -/
  source_good : ∀ P : CochainComplex (Modules l E Y) ℤ,
    integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      integralOperationsGoodComplex l E Y ((sourceTower l E Y P).obj (op n))
  /-- The specified augmentation is natural for every chain map of good complexes. -/
  augmentation_naturality : ∀ {P P' : CochainComplex (Modules l E Y) ℤ} (f : P ⟶ P'),
    integralOperationsGoodComplex l E Y P → integralOperationsGoodComplex l E Y P' →
      sourceTowerMap l E Y f ≫ comparison l E Y P' =
        comparison l E Y P ≫ targetTowerMap l E Y f
  /-- Total tensor with S_n[0] is ordinary scalar extension, with actual transitions. -/
  normalizationIso : ∀ (P : CochainComplex (Modules l E Y) ℤ),
    integralOperationsGoodComplex l E Y P →
      (targetTower l E Y P ≅ ((reductionComplex l E Y).obj P).asFunctor)
  /-- The normalization is the canonical balanced section map, not a free isomorphism. -/
  normalization : ∀ (P : CochainComplex (Modules l E Y) ℤ)
      (hP : integralOperationsGoodComplex l E Y P)
      (n : ℕ) (i : ℤ) (U : Y.ProEtᵒᵖ) (x : (P.X i).val.obj U)
      (s : (integralCoefficientSheaf l E Y n).obj.obj U),
    (((normalizationIso P hP).hom.app (op n)).f i).val.app U
      (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology Y)
        (completedIntegralCommRingSheafUnrestricted l E Y) P
        ((CochainComplex.singleFunctor (Modules l E Y) 0).obj (residue l E Y n))
        i 0 i (add_zero i) U x
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (residue l E Y n)).inv.val.app U s)) =
      unrestrictedIntegralTensorSection l E Y n (P.X i) U s x
  /-- The canonical computation of strict derived reduction on P. -/
  reductionIso : ∀ (P : CochainComplex (Modules l E Y) ℤ),
    integralOperationsGoodComplex l E Y P →
      (DerivedCategory.Q.obj ((transpose l E Y).obj (targetTower l E Y P)) ≅
        (reductionPair l E Y).functor.obj (DerivedCategory.Q.obj P))
  /-- The reduction identification is fixed by the existing universal counit. -/
  reduction_computation : ∀ P hP,
    (reductionIso P hP).hom ≫ (reductionPair l E Y).counit.app P =
      DerivedCategory.Q.map ((transpose l E Y).map (normalizationIso P hP).hom)
  /-- Naturality of the reduction computation in good representatives. -/
  reduction_naturality : ∀ {P P' : CochainComplex (Modules l E Y) ℤ} (f : P ⟶ P')
      (hP : integralOperationsGoodComplex l E Y P)
      (hP' : integralOperationsGoodComplex l E Y P'),
    DerivedCategory.Q.map ((transpose l E Y).map (targetTowerMap l E Y f)) ≫
        (reductionIso P' hP').hom =
      (reductionIso P hP).hom ≫ (reductionPair l E Y).functor.map (DerivedCategory.Q.map f)
  /-- The universal tower-pullback counit computes on the strict Koszul replacement. -/
  tower_computation : ∀ P : CochainComplex (Modules l E Y) ℤ,
    integralOperationsGoodComplex l E Y P →
      IsIso ((derivedCounit l E g).app ((transpose l E Y).obj (sourceTower l E Y P)))
  /-- The actual augmentation becomes invertible after whole-tower localization. -/
  augmentation_invertible : ∀ P : CochainComplex (Modules l E Y) ℤ,
    integralOperationsGoodComplex l E Y P →
      IsIso (DerivedCategory.Q.map ((transpose l E Y).map (comparison l E Y P)))
  /-- The full strict-tower pullback computation. -/
  chi : ∀ (P : CochainComplex (Modules l E Y) ℤ),
    integralOperationsGoodComplex l E Y P →
      ((derivedPull l E g).obj
          ((reductionPair l E Y).functor.obj (DerivedCategory.Q.obj P)) ≅
        DerivedCategory.Q.obj (((towerPull l E g).mapHomologicalComplex (.up ℤ)).obj
          ((transpose l E Y).obj (sourceTower l E Y P))))
  /-- chi = epsilon^V_H composed with V of the inverse augmented resolution. -/
  chi_formula : ∀ P hP,
    (chi P hP).hom =
      (derivedPull l E g).map
        ((reductionIso P hP).inv ≫
          @inv _ _ _ _
            (DerivedCategory.Q.map ((transpose l E Y).map (comparison l E Y P)))
            (augmentation_invertible P hP)) ≫
        (derivedCounit l E g).app ((transpose l E Y).obj (sourceTower l E Y P))
  /-- Naturality for chain maps between good complexes, in the whole tower category. -/
  chi_naturality : ∀ {P P' : CochainComplex (Modules l E Y) ℤ} (f : P ⟶ P')
      (hP : integralOperationsGoodComplex l E Y P)
      (hP' : integralOperationsGoodComplex l E Y P'),
    (derivedPull l E g).map
        ((reductionPair l E Y).functor.map (DerivedCategory.Q.map f)) ≫ (chi P' hP').hom =
      (chi P hP).hom ≫ DerivedCategory.Q.map
        (((towerPull l E g).mapHomologicalComplex (.up ℤ)).map
          ((transpose l E Y).map (sourceTowerMap l E Y f)))
  /-- Naturality of beta on good complexes. -/
  beta_naturality : ∀ {P P' : CochainComplex (Modules l E Y) ℤ} (f : P ⟶ P'),
    integralOperationsGoodComplex l E Y P → integralOperationsGoodComplex l E Y P' →
      B.functor.map (DerivedCategory.Q.map f) ≫ B.counit.app P' =
        B.counit.app P ≫ DerivedCategory.Q.map
          ((integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).map f)

end WeilConjectures.FiniteReductionTower
