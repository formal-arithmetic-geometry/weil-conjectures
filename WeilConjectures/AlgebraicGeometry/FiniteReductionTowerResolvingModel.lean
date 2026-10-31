/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralCompletedTowerPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.PrincipalKoszulStrictReplacement
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
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
import WeilConjectures.AlgebraicGeometry.FiniteReductionAdditiveCompatibility
import WeilConjectures.AlgebraicGeometry.FiniteReductionScalarNormalization
import all WeilConjectures.AlgebraicGeometry.IntegralCompletedTowerPullbackUniverses
import all WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatSupplement
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
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulatedSupplement
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import all WeilConjectures.Algebra.Homology.PrincipalKoszulQuotientTowersSupplement

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

set_option genSizeOfSpec false
set_option genInjectivity false

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

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

/-- Finite reduction followed by finite inverse image has the resolving model and
the canonical strict derived tower-pullback computation.

Source: Stacks Project, derived.tex Tag 06XN, lemma-find-existence-computes,
left-derived assertion; sites-cohomology.tex Tags 06YS, 06YT, 06YP and 07A2
(blueprint: lem-a1-finite-reduction-tower-resolving-model).

Proof:
1. Apply the additive finite-level functors to dh+hd and to the cone matrix.
   Natural quotient transitions make these strict tower homotopies and cone maps.
2. Change-of-rings K-flat quasi-isomorphism invariance, finite constant inverse-image
   exactness and exact scalar restriction give levelwise quasi-isomorphisms. Tower
   cohomology is levelwise (lem-weil-tower-category-levelwise-abelian).
3. Flat-term K-flat resolutions (lem-pc-kflat-resolution) and the universal resolving
   theorem (lem-pur-left-derived-from-kflat-class) give B and beta, with beta invertible
   on every good complex.
4. Integral quotient-resolution normalization identifies the actual pi_n augmentation
   [R --t^(n+1)--> R] to S_n[0] as a quasi-isomorphism with flat K-flat source.
5. The total-tensor model (lem-pur-kflat-total-tensor-model) and fixed-factor tensor
   invariance (lem-weil-pbc-kflat-fixed-tensor-triangulated) give good H(P)_n and
   quasi-isomorphisms id_P tensor epsilon_n. The equation t^n*t=t^(n+1) and the
   quotient-cone equations give strict transitions. Tensor bifunctoriality gives
   augmentation naturality.
6. Normalize total tensor against scalar extension by p tensor s maps to s tensor p.
   The derived-reduction counit then gives reductionIso and its naturality, retaining
   the actual quotient transitions (def-weil-pbc-adic-coefficient-datum).
7. Strict diagram K-flat replacement (lem-weil-pbc-diagram-kflat-replacements) and
   the resolving-class theorem make epsilon^V invertible on H(P). Invert Qa_P and
   compose its image under V with this counit, using reductionIso, to obtain chi.
   Neither exactness of G nor invertibility of c_g is used.
8. Apply V to augmentation naturality and compose with counit naturality. This gives
   chi_naturality; beta_naturality is the naturality of the universal derived counit.
-/
theorem finite_reduction_tower_resolving_model
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    Nonempty (ResolvingModel l E g) := by
  classical
  obtain ⟨hh, c, hc, e, he⟩ := finite_reduction_additive_compatibility l E g
  obtain ⟨N, hN, hNnat⟩ := finite_reduction_scalar_normalization l E Y
  let F := integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X
  have hlevel {P P' : CochainComplex (Modules l E Y) ℤ} (f : P ⟶ P')
      (hP : integralOperationsGoodComplex l E Y P)
      (hP' : integralOperationsGoodComplex l E Y P') (hf : QuasiIso f) (n : ℕ) :
      QuasiIso (((integralOperationsPullbackTowerFunctor l E g).map f).app (op n)) := by
    let G := integralOperationsLevelPullback l E g n
    have : G.Additive := integralOperationsLevelPullback_additive l E g n
    have hG := AlgebraicGeometry.Scheme.coefficientProEtaleModulePullback_exact.{t, u} g
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
    have : PreservesFiniteLimits G := hG.1
    have : PreservesFiniteColimits G := hG.2
    let φ := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E X n)
    let U := SheafOfModules.restrictScalars.{max u (t + 1)} φ
    have hU := coefficientRestriction_exact φ
    have : PreservesFiniteLimits U := hU.1
    have : PreservesFiniteColimits U := hU.2
    have hR := finiteReduction_quasiIso l E Y n f hP hP' hf
    have hF := HomologicalComplex.quasiIso_map_of_preservesHomology
      ((unrestrictedIntegralFiniteComplex l E Y n).map f) G (hφ := hR)
    change QuasiIso ((U.mapHomologicalComplex (.up ℤ)).map _)
    exact HomologicalComplex.quasiIso_map_of_preservesHomology _ U (hφ := hF)
  have hinverts {P P' : CochainComplex (Modules l E Y) ℤ} (f : P ⟶ P')
      (hP : integralOperationsGoodComplex l E Y P)
      (hP' : integralOperationsGoodComplex l E Y P') (hf : QuasiIso f) :
      IsIso ((F ⋙ DerivedCategory.Q).map f) := by
    have ht : QuasiIso (F.map f) :=
      (HomologicalComplex.quasiIso_iff_evaluation _).2 (fun n ↦ hlevel f hP hP' hf n.unop)
    exact Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso (Towers l E X) (.up ℤ)) _ ht
  obtain ⟨L, η, hη, hk, hflat⟩ := SheafOfModules.functorial_resolution
    (completedIntegralCommRingSheafUnrestricted l E Y)
  obtain ⟨B, β, hu, hb⟩ := deriveFromFunctorialResolution
    (integralOperationsGoodComplex l E Y) (F ⋙ DerivedCategory.Q) L η
    (fun P ↦ ⟨hk P, hflat P⟩) hη (fun f hP hP' hf ↦ hinverts f hP hP' hf)
  let pair : DerivedPair l E Y X F := ⟨B, β, hu, hb⟩
  have hsource (P : CochainComplex (Modules l E Y) ℤ)
      (hP : integralOperationsGoodComplex l E Y P) (n : ℕ) :
      integralOperationsGoodComplex l E Y ((sourceTower l E Y P).obj (op n)) :=
    (PrincipalKoszulStrictReplacement.principal_koszul_strict_replacement
      l E Y P hP.1 hP.2 n).2
  have haug (P : CochainComplex (Modules l E Y) ℤ)
      (hP : integralOperationsGoodComplex l E Y P) :
      QuasiIso ((transpose l E Y).map (comparison l E Y P)) := by
    apply (HomologicalComplex.quasiIso_iff_evaluation _).2
    intro n
    exact (PrincipalKoszulStrictReplacement.principal_koszul_strict_replacement
      l E Y P hP.1 hP.2 n.unop).1
  have hai (P : CochainComplex (Modules l E Y) ℤ)
      (hP : integralOperationsGoodComplex l E Y P) :
      IsIso (DerivedCategory.Q.map ((transpose l E Y).map (comparison l E Y P))) := by
    have := haug P hP
    infer_instance
  have hv (P : CochainComplex (Modules l E Y) ℤ)
      (hP : integralOperationsGoodComplex l E Y P) :
      IsIso ((derivedCounit l E g).app ((transpose l E Y).obj (sourceTower l E Y P))) :=
    (towerPull_exists l E g).choose_spec.choose_spec.2.2 _ (fun n ↦ (hsource P hP n).1)
  let r (P : CochainComplex (Modules l E Y) ℤ)
      (hP : integralOperationsGoodComplex l E Y P) :
      DerivedCategory.Q.obj ((transpose l E Y).obj (targetTower l E Y P)) ≅
        (reductionPair l E Y).functor.obj (DerivedCategory.Q.obj P) :=
    DerivedCategory.Q.mapIso ((transpose l E Y).mapIso (N P hP)) ≪≫
      (@asIso _ _ _ _ ((reductionPair l E Y).counit.app P)
        ((reductionPair l E Y).computes P hP)).symm
  have hr (P : CochainComplex (Modules l E Y) ℤ)
      (hP : integralOperationsGoodComplex l E Y P) :
      (r P hP).hom ≫ (reductionPair l E Y).counit.app P =
        DerivedCategory.Q.map ((transpose l E Y).map (N P hP).hom) := by
    simp only [r, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_inv,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hrnat {P P' : CochainComplex (Modules l E Y) ℤ} (f : P ⟶ P')
      (hP : integralOperationsGoodComplex l E Y P)
      (hP' : integralOperationsGoodComplex l E Y P') :
      DerivedCategory.Q.map ((transpose l E Y).map (targetTowerMap l E Y f)) ≫
          (r P' hP').hom =
        (r P hP).hom ≫ (reductionPair l E Y).functor.map (DerivedCategory.Q.map f) := by
    have := (reductionPair l E Y).computes P' hP'
    apply (cancel_mono ((reductionPair l E Y).counit.app P')).1
    rw [Category.assoc, hr P' hP']
    have hn := (reductionPair l E Y).counit.naturality f
    change (reductionPair l E Y).functor.map (DerivedCategory.Q.map f) ≫ _ =
      _ ≫ DerivedCategory.Q.map ((reductionComplex l E Y).map f) at hn
    rw [Category.assoc, hn, ← Category.assoc, hr P hP]
    have ht : (transpose l E Y).map
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
          ((reductionComplex l E Y).map f)) = (reductionComplex l E Y).map f := by
      ext i n
      rfl
    have hn' := congrArg (fun a ↦ DerivedCategory.Q.map ((transpose l E Y).map a))
      (hNnat f hP hP')
    simpa only [Functor.map_comp, ht] using hn'
  let a (P : CochainComplex (Modules l E Y) ℤ)
      (hP : integralOperationsGoodComplex l E Y P) :=
    @asIso _ _ _ _
      (DerivedCategory.Q.map ((transpose l E Y).map (comparison l E Y P))) (hai P hP) ≪≫
      r P hP
  let χ (P : CochainComplex (Modules l E Y) ℤ)
      (hP : integralOperationsGoodComplex l E Y P) :=
    (derivedPull l E g).mapIso (a P hP).symm ≪≫
      @asIso _ _ _ _
        ((derivedCounit l E g).app ((transpose l E Y).obj (sourceTower l E Y P))) (hv P hP)
  have hanat {P P' : CochainComplex (Modules l E Y) ℤ} (f : P ⟶ P')
      (hP : integralOperationsGoodComplex l E Y P)
      (hP' : integralOperationsGoodComplex l E Y P') :
      DerivedCategory.Q.map ((transpose l E Y).map (sourceTowerMap l E Y f)) ≫
          (a P' hP').hom =
        (a P hP).hom ≫ (reductionPair l E Y).functor.map (DerivedCategory.Q.map f) := by
    dsimp only [a, Iso.trans_hom, asIso_hom]
    rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      PrincipalKoszulStrictReplacement.comparison_naturality,
      Functor.map_comp, Functor.map_comp, Category.assoc, hrnat f hP hP',
      ← Category.assoc]
  have hχnat {P P' : CochainComplex (Modules l E Y) ℤ} (f : P ⟶ P')
      (hP : integralOperationsGoodComplex l E Y P)
      (hP' : integralOperationsGoodComplex l E Y P') :
      (derivedPull l E g).map
          ((reductionPair l E Y).functor.map (DerivedCategory.Q.map f)) ≫ (χ P' hP').hom =
        (χ P hP).hom ≫ DerivedCategory.Q.map
          (((towerPull l E g).mapHomologicalComplex (.up ℤ)).map
            ((transpose l E Y).map (sourceTowerMap l E Y f))) := by
    apply (cancel_epi ((derivedPull l E g).map (a P hP).hom)).1
    dsimp only [χ, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom]
    rw [← Functor.map_comp_assoc, ← hanat f hP hP', Functor.map_comp]
    simp only [Category.assoc, ← Functor.map_comp_assoc,
      Iso.hom_inv_id]
    simp only [Category.comp_id]
    change (derivedPull l E g).map
        (DerivedCategory.Q.map ((transpose l E Y).map (sourceTowerMap l E Y f))) ≫
        (derivedCounit l E g).app ((transpose l E Y).obj (sourceTower l E Y P')) =
      (derivedPull l E g).map (𝟙 _) ≫
        (derivedCounit l E g).app ((transpose l E Y).obj (sourceTower l E Y P)) ≫ _
    rw [(derivedPull l E g).map_id, Category.id_comp]
    exact (derivedCounit l E g).naturality
      ((transpose l E Y).map (sourceTowerMap l E Y f))
  refine ⟨{
    homotopy := hh
    shift := c
    shift_normalization := hc
    cone := e
    cone_normalization := he
    quasiIso := fun f hP hP' hf n ↦ hlevel f hP hP' hf n
    B := pair
    augmentation_quasiIso := haug
    source_good := hsource
    augmentation_naturality := fun f _ _ ↦
      PrincipalKoszulStrictReplacement.comparison_naturality l E Y f
    normalizationIso := N
    normalization := hN
    reductionIso := r
    reduction_computation := hr
    reduction_naturality := fun f hP hP' ↦ hrnat f hP hP'
    tower_computation := hv
    augmentation_invertible := hai
    chi := χ
    chi_formula := ?_
    chi_naturality := fun f hP hP' ↦ hχnat f hP hP'
    beta_naturality := fun f _ _ ↦ β.naturality f }⟩
  intro P hP
  rfl

end WeilConjectures.FiniteReductionTower
