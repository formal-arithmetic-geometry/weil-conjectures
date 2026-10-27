/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q103, H3
-/
module

public import Sheaf.Paper.PointSystemTransportDescent
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.StrictRoosComparison
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Sheaf.Paper.ExactProductFunctorStrictLimit
import all Sheaf.Paper.CoefficientConstantTowerRoosComparison
import all Sheaf.CategoryTheory.StrictRoosDerivation
import all Sheaf.CategoryTheory.RoosComparisonHorizontalCoherence
import all Sheaf.Paper.ExactProductFunctorRoosResolution
import all Sheaf.Paper.ExactProductFunctorRoosDescent
import all Sheaf.Paper.CoefficientRingedSequenceSite
import all Sheaf.Paper.PointAutomorphismRestrictionNatural
import all Sheaf.Paper.IsomorphismScalarQuotientChainSquares
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.Algebra.Category.ModuleCat.AB

/-! # Simultaneous normalized point-system comparisons

Source: blueprint main-20261015, prop-trf-rational-frobenius-integral-model,
proof (3), integral maps as derived limits; the seven-step agent refinement
(blueprint: lem-trf-point-system-normalized-comparison-data).

All towers are strict and all derived categories are ordinary and unbounded.
The index n means the coefficient exponent n+1. The scalar universe is the
existing common lift, with no identification of site and coefficient universes.
No theorem or interface from PointSystemRoosTransport is imported.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
-- Avoid unfolding the full dependent coefficient bundle in the optional universe linter.
set_option linter.checkUnivs false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.pointReductionModuleDerived
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  CategoryTheory.roosF CategoryTheory.roosχ CategoryTheory.roosι
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.mapDerivedCategoryFactors
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.rightDerivedFunctorUnitQ

universe w wT t u a b a' b' wC wB wTC wTB
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointSystemNormalizedComparison

variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Notation for the existing ambient category, without a completeness restriction.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-normalized-comparison-data). -/
abbrev A := scalarReductionSource l E (Spec (.of D.k))

/-- Notation for the recorded exact sections with the constant integral scalar action.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-normalized-comparison-data). -/
abbrev T : A D l E ⥤
    ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E none) :=
  pointRestrictionSections l E D.k none

/-- Notation for actual sectionwise inverse image with transported completed action.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-normalized-comparison-data). -/
abbrev F (r : ℕ) : A D l E ⥤ A D l E :=
  pointRestrictionInverseImage l E (PointSystemTransport.pointPower D r).hom none

/-- The exactness and product assertions needed to form the termwise derived functors.
Source: blueprint integral-model proof (3), refinement steps 2--3
(blueprint: lem-trf-point-system-normalized-comparison-data).
Proof: inverse image reindexes sections along the site equivalence and transports
scalars by the canonical coefficient isomorphism; this preserves kernels and cokernels.
Sections at the algebraically closed point are exact by
lem-weil-point-proetale-sections-exact. Restriction through constant sections keeps
underlying groups and exactness. Products are sectionwise by
lem-weil-proetale-countable-products-exact; their canonical comparisons are evaluation
of tuples at the reindexed object and at the final object respectively. Products of
R-modules are exact by choosing a preimage in each coordinate. -/
theorem exact_products :
    (∀ r : ℕ, (F D l E r).Additive ∧ PreservesFiniteLimits (F D l E r) ∧
      PreservesFiniteColimits (F D l E r)) ∧
    (T D l E).Additive ∧ PreservesFiniteLimits (T D l E) ∧
    PreservesFiniteColimits (T D l E) ∧
    (∀ (r : ℕ) (V : ℕ → A D l E), IsIso (piComparison (F D l E r) V)) ∧
    (∀ V : ℕ → A D l E, IsIso (piComparison (T D l E) V)) ∧
    HasExactLimitsOfShape (Discrete ℕ) (A D l E) ∧
    HasExactLimitsOfShape (Discrete ℕ)
      (ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E none)) := by
  have ht := AlgebraicGeometry.ProEtale.restriction_sections_exact l E D.k none
  have : PreservesFiniteLimits (T D l E) := ht.1
  have : PreservesFiniteColimits (T D l E) := ht.2
  refine ⟨?_, pointRestrictionSectionsAdditive l E D.k none, ht.1, ht.2, ?_, ?_, ?_, inferInstance⟩
  · intro r
    exact isoSectionwiseModuleInverseImage_exact (PointSystemTransport.pointPower D r).hom
      (pointRestrictionCoefficientMap l E (PointSystemTransport.pointPower D r).hom none)
  · intro r V
    have : (F D l E r).IsEquivalence := ScalarQuotientChain.sectionwiseModules_equivalence
      (PointSystemTransport.pointPower D r).hom
      (pointRestrictionCoefficientMap l E (PointSystemTransport.pointPower D r).hom none)
    infer_instance
  · intro V
    change IsIso (piComparison (SheafOfModules.evaluation _ _ ⋙
      ModuleCat.restrictScalars _) V)
    infer_instance
  · exact ProEt.products_exact (Spec (.of D.k)) _ ℕ

/-- Additivity inherited from the exactness assertion.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-normalized-comparison-data). -/
instance fAdditive (r : ℕ) : (F D l E r).Additive := (exact_products D l E).1 r |>.1

/-- Left exactness inherited from the exactness assertion.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-normalized-comparison-data). -/
instance fLimits (r : ℕ) : PreservesFiniteLimits (F D l E r) :=
  ((exact_products D l E).1 r).2.1

/-- Right exactness inherited from the exactness assertion.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-normalized-comparison-data). -/
instance fColimits (r : ℕ) : PreservesFiniteColimits (F D l E r) :=
  ((exact_products D l E).1 r).2.2

/-- Additivity of the existing sections functor.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-normalized-comparison-data). -/
instance tAdditive : (T D l E).Additive := (exact_products D l E).2.1

/-- Exact sections preserve finite limits.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-normalized-comparison-data). -/
instance tLimits : PreservesFiniteLimits (T D l E) := (exact_products D l E).2.2.1

/-- Exact sections preserve finite colimits.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-normalized-comparison-data). -/
instance tColimits : PreservesFiniteColimits (T D l E) := (exact_products D l E).2.2.2.1

/-- Notation for the existing scalar restriction, retaining every quotient transition.
Source: Stacks 0941 (blueprint: lem-trf-point-system-normalized-comparison-data). -/
abbrev U := coefficientSequenceRestriction l E (Spec (.of D.k))

/-- The same scalar restriction applied to unbounded complexes.
Source: Stacks 0941 (blueprint: lem-trf-point-system-normalized-comparison-data). -/
abbrev X := (U D l E).mapHomologicalComplex (.up ℤ)

/-- The recorded system inverse image, with its actual finite-level actions.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-normalized-comparison-data). -/
abbrev G (r : ℕ) := PointSystemTransport.pull D l E r

/-- The existing total limit on ambient module towers.
Source: Stacks 0941 (blueprint: lem-trf-point-system-normalized-comparison-data). -/
abbrev LA := coefficientConstantTowerLimit l E (Spec (.of D.k))

/-- The recorded constant integral scalar ring has its original commutative structure.
Source: coefficient conventions
(blueprint: lem-trf-point-system-normalized-comparison-data). -/
instance scalarCommutative : CommRing (pointRestrictionScalars.{t, u} l E none) :=
  inferInstanceAs (CommRing (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))

/-- The existing total limit on constant integral scalar towers.
Source: Stacks 0941 (blueprint: lem-trf-point-system-normalized-comparison-data). -/
abbrev LR := CoefTower.totalLimit (pointRestrictionScalars.{t, u} l E none)

/-- The existing realization Rlim U.
Source: Stacks 0941 (blueprint: lem-trf-point-system-normalized-comparison-data). -/
abbrev L := coefficientSequenceLimit l E (Spec (.of D.k))

section CachedLimits
variable {C : Type a} [Category.{b} C] [Abelian C]
private instance (priority := 2000) natProductShape [HasCountableProducts C] :
    HasProductsOfShape ℕ C := HasCountableProducts.out ℕ
private instance (priority := 2000) complexNatProductShape [HasCountableProducts C] :
    HasProductsOfShape ℕ (CochainComplex C ℤ) := inferInstance
private instance (priority := 2000) complexTowerShape [HasLimitsOfShape ℕᵒᵖ C] :
    HasLimitsOfShape ℕᵒᵖ (CochainComplex C ℤ) := inferInstance
private instance (priority := 2000) natProduct [HasCountableProducts C]
    (V : ℕ → C) : HasProduct V := HasLimitsOfShape.has_limit _
private instance (priority := 2000) complexNatProduct [HasCountableProducts C]
    (V : ℕ → CochainComplex C ℤ) : HasProduct V := HasLimitsOfShape.has_limit _
private instance (priority := 2000) towerLimit [HasLimitsOfShape ℕᵒᵖ C]
    (V : ℕᵒᵖ ⥤ C) : HasLimit V := HasLimitsOfShape.has_limit _
private instance (priority := 2000) complexTowerLimit [HasLimitsOfShape ℕᵒᵖ C]
    (V : ℕᵒᵖ ⥤ CochainComplex C ℤ) : HasLimit V := HasLimitsOfShape.has_limit _
end CachedLimits

section GeneralComparison
variable {C : Type a} {B : Type a'} [Category.{b} C] [Category.{b'} B]
  [abelianC : Abelian C] [abelianB : Abelian B]
  [HasCountableProducts C] [HasCountableProducts B]
  [HasLimitsOfShape ℕᵒᵖ C] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wTC} (ℕᵒᵖ ⥤ C)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ C)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
  [(lim : (ℕᵒᵖ ⥤ C) ⥤ C).Additive] [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive]

/-- Exactness of postcomposition is componentwise.
Source: Stacks 015F (blueprint: lem-trf-point-system-normalized-comparison-data). -/
instance comparisonTowerLimits (Q : C ⥤ B) [PreservesFiniteLimits Q] :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C B).obj Q) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- Exactness of postcomposition is componentwise.
Source: Stacks 015F (blueprint: lem-trf-point-system-normalized-comparison-data). -/
instance comparisonTowerColimits (Q : C ⥤ B) [PreservesFiniteColimits Q] :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C B).obj Q) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- The signed coordinates H prime: the identity chain isomorphism of the underlying
cone has coordinate expression J(b,a)=(a,-b). Thus this uses the actual shifted cone,
with another coordinate chart, rather than an unrelated isomorphic complex.
Source: blueprint proof (3), refinement step 5
(blueprint: lem-trf-point-system-normalized-comparison-data). -/
def signedCoordinates (V : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (p : ℤ) :
    (roosF.obj V).X (p + 1) ≅ (roosP V).X (p + 1) ⊞ (roosP V).X p :=
  roosχ V p ≪≫ biprod.braiding _ _ ≪≫
    biprod.mapIso (Iso.refl _) (-(Iso.refl _))

/-- The specified comparison data for ONE of the two actual functors in this node.
The product, diagonal, resolution and augmentation fields all concern the same lambda.
This is a bundle of maps and equations, not a choice of an unspecified comparison.
Source: blueprint integral-model proof (3), refinement steps 4--7; Stacks 0941
(blueprint: lem-trf-point-system-normalized-comparison-data). -/
structure Comparison (Q : C ⥤ B) [Q.Additive]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (thetaC : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor ≅
      roosF ⋙ DerivedCategory.Q)
    (thetaB : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor ≅
      roosF ⋙ DerivedCategory.Q) where
  /-- The canonical product comparison on complexes. -/
  product : ∀ V : CochainComplex (ℕᵒᵖ ⥤ C) ℤ,
    (Q.mapHomologicalComplex (.up ℤ)).obj (roosP V) ≅
      roosP ((((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapHomologicalComplex (.up ℤ)).obj V)
  /-- Its projections are exactly Q of the original projections. -/
  product_projection : ∀ (V : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (n : ℕ),
    (product V).hom ≫ Pi.π _ n =
      (Q.mapHomologicalComplex (.up ℤ)).map (Pi.π _ n)
  /-- A natural chain isomorphism on the entire cone. -/
  kappa : roosF ⋙ Q.mapHomologicalComplex (.up ℤ) ≅
    ((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapHomologicalComplex (.up ℤ) ⋙ roosF
  /-- Both signed coordinates have the product comparison, with no cross terms. -/
  diagonal : ∀ (V : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (p : ℤ),
    (kappa.hom.app V).f (p + 1) ≫
        (roosχ ((((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapHomologicalComplex
          (.up ℤ)).obj V) p).hom ≫ biprod.fst =
      Q.map ((roosχ V p).hom ≫ biprod.fst) ≫ (product V).hom.f p ∧
    (kappa.hom.app V).f (p + 1) ≫
        (roosχ ((((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapHomologicalComplex
          (.up ℤ)).obj V) p).hom ≫ biprod.snd =
      Q.map ((roosχ V p).hom ≫ biprod.snd) ≫ (product V).hom.f (p + 1)
  /-- Conjugating by J leaves the same product map on both signed summands. -/
  signed_diagonal : ∀ (V : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (p : ℤ),
    (kappa.hom.app V).f (p + 1) ≫
        (signedCoordinates ((((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapHomologicalComplex
          (.up ℤ)).obj V) p).hom ≫ biprod.fst =
      Q.map ((signedCoordinates V p).hom ≫ biprod.fst) ≫ (product V).hom.f (p + 1) ∧
    (kappa.hom.app V).f (p + 1) ≫
        (signedCoordinates ((((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapHomologicalComplex
          (.up ℤ)).obj V) p).hom ≫ biprod.snd =
      Q.map ((signedCoordinates V p).hom ≫ biprod.snd) ≫ (product V).hom.f p
  /-- The whole ordinary inverse-limit cone comparison. -/
  beta : ∀ I : CochainComplex (ℕᵒᵖ ⥤ C) ℤ,
    (Q.mapHomologicalComplex (.up ℤ)).obj
        (((lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ)).obj I) ≅
      ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)).obj
        ((((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapHomologicalComplex (.up ℤ)).obj I)
  /-- Every leg of that cone is Q of the original leg. -/
  beta_projection : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (n : ℕ),
    (beta I).hom ≫ (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app
        ((((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapHomologicalComplex (.up ℤ)).obj I) =
      (Q.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I)
  /-- The comparison is a natural isomorphism on the entire ordinary derived category. -/
  comparison : (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor ⋙ Q.mapDerivedCategory ≅
    ((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapDerivedCategory ⋙
      (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor
  /-- Its representative equation is theta inverse, kappa, Q(theta), in Lean order. -/
  model : ∀ V : CochainComplex (ℕᵒᵖ ⥤ C) ℤ,
    Q.mapDerivedCategory.map (thetaC.hom.app V) ≫
        Q.mapDerivedCategoryFactors.hom.app (roosF.obj V) ≫
        DerivedCategory.Q.map (kappa.hom.app V) =
      comparison.hom.app (DerivedCategory.Q.obj V) ≫
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map
          (((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapDerivedCategoryFactors.hom.app V) ≫
        thetaB.hom.app ((((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapHomologicalComplex
          (.up ℤ)).obj V)
  /-- Every pair of resolutions computes this SAME comparison, using the whole cone. -/
  resolutions : ∀ (V I : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (q : V ⟶ I) [QuasiIso q]
    [I.IsKInjective] (J : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (e : (((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapHomologicalComplex
      (.up ℤ)).obj I ⟶ J) [QuasiIso e] [J.IsKInjective],
    ∃ (dI : DerivedCategory.Q.obj
        (((lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ)).obj I) ≅
        (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor.obj (DerivedCategory.Q.obj V))
      (dJ : DerivedCategory.Q.obj
        (((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)).obj J) ≅
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.obj
          (DerivedCategory.Q.obj ((((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapHomologicalComplex
            (.up ℤ)).obj I))),
      dI.hom ≫ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor.map
          (DerivedCategory.Q.map q) =
        (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctorUnitQ I ∧
      dJ.hom ≫ (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map
          (DerivedCategory.Q.map e) =
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctorUnitQ J ∧
      Q.mapDerivedCategory.map dI.hom ≫ comparison.hom.app (DerivedCategory.Q.obj V) ≫
          (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map
            (((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapDerivedCategoryFactors.hom.app V) ≫
          (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map
            (DerivedCategory.Q.map
              ((((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapHomologicalComplex (.up ℤ)).map q)) =
        Q.mapDerivedCategoryFactors.hom.app
            (((lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map (beta I).hom ≫
          DerivedCategory.Q.map
            (((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)).map e) ≫ dJ.hom
  /-- Strict augmentations retain their zero shifted coordinate under kappa. -/
  augmentations : ∀ (V : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (P : CochainComplex C ℤ)
    (gamma : ∀ n : ℕ, P ⟶ V.asFunctor.obj (op n))
    (_hgamma : ∀ n : ℕ, gamma (n + 1) ≫
      V.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n),
    ∃ (iota : P ⟶ roosF.obj V)
      (iota' : (Q.mapHomologicalComplex (.up ℤ)).obj P ⟶
        roosF.obj ((((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapHomologicalComplex
          (.up ℤ)).obj V)),
      (∀ p : ℤ, iota.f (p + 1) ≫ (roosχ V p).hom =
        biprod.lift 0 ((Pi.lift gamma).f (p + 1))) ∧
      (∀ p : ℤ, iota'.f (p + 1) ≫
          (roosχ ((((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapHomologicalComplex
            (.up ℤ)).obj V) p).hom =
        biprod.lift 0 ((Pi.lift (fun n : ℕ ↦
          (Q.mapHomologicalComplex (.up ℤ)).map (gamma n))).f (p + 1))) ∧
      (Q.mapHomologicalComplex (.up ℤ)).map iota ≫ kappa.hom.app V = iota'

end GeneralComparison

section
variable {C B : Type*} [Category* C] [Category* B] [Abelian C] [Abelian B]
  [HasCountableProducts C] [HasCountableProducts B]
  [HasLimitsOfShape ℕᵒᵖ C] [HasLimitsOfShape ℕᵒᵖ B]
  (Q : C ⥤ B) [Q.Additive] [PreservesFiniteLimits Q]
  (hQ : ∀ M : ℕ → C, IsIso (piComparison Q M))

private def limitBeta (I : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) :
    (Q.mapHomologicalComplex (.up ℤ)).obj
        (((lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ)).obj I) ≅
      ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)).obj
        ((((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapHomologicalComplex (.up ℤ)).obj I) := by
  have : PreservesLimitsOfShape (Discrete ℕ) Q := natProducts Q hQ
  have : PreservesLimitsOfShape ℕᵒᵖ Q := natProducts_preservesTowers Q
  exact (NatIso.mapHomologicalComplex (preservesLimitNatIso Q) (.up ℤ)).app I

private theorem limitBeta_projection (I : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (n : ℕ) :
    (limitBeta Q hQ I).hom ≫ (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app
        ((((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapHomologicalComplex (.up ℤ)).obj I) =
      (Q.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I) := by
  have : PreservesLimitsOfShape (Discrete ℕ) Q := natProducts Q hQ
  have : PreservesLimitsOfShape ℕᵒᵖ Q := natProducts_preservesTowers Q
  ext p
  exact preservesLimitIso_hom_π Q (I.X p) (op n)

omit [HasCountableProducts C] in
private theorem ordinaryLimit_projection (I : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (n : ℕ) :
    (ordinaryLimitIso (A := C)).hom.app I ≫ limit.π I.asFunctor (op n) =
      (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I := by
  ext p
  simp [ordinaryLimitIso,
    HomologicalComplex.functorEquivalenceInverseCompMapHomologicalComplexLim]
  rfl
private def ordinaryInclusion (I : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) :
    ((lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ)).obj I ⟶ roosF.obj I :=
  (ordinaryLimitIso (A := C)).hom.app I ≫ roosι I

private theorem ordinaryInclusion_coordinates
    (I : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (p : ℤ) :
    (ordinaryInclusion I).f (p + 1) ≫ (roosχ I p).hom =
      biprod.lift 0 ((Pi.lift (f := fun n : ℕ ↦ I.asFunctor.obj (op n)) (fun n : ℕ ↦
        (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I)).f (p + 1)) := by
  have hp : (ordinaryLimitIso (A := C)).hom.app I ≫
      Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n)) =
      Pi.lift (f := fun n : ℕ ↦ I.asFunctor.obj (op n)) (fun n : ℕ ↦
        (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I) := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, Pi.lift_π, ordinaryLimit_projection]
    erw [Pi.lift_π]
  dsimp only [ordinaryInclusion, HomologicalComplex.comp_f]
  rw [Category.assoc, roosι_χ]
  apply biprod.hom_ext
  · erw [biprod.lift_fst]; simp
  · simp only [Category.assoc, biprod.lift_snd]
    change ((ordinaryLimitIso (A := C)).hom.app I ≫
      Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1) = _
    exact congrArg (fun f ↦ f.f (p + 1)) hp
end

section CanonicalComparison
variable {C B : Type*} [Category* C] [Category* B] [Abelian C] [Abelian B]
  [HasCountableProducts C] [HasCountableProducts B]
  (Q : C ⥤ B) [Q.Additive] [PreservesLimitsOfShape (Discrete ℕ) Q]

private def canonicalKappa : roosF ⋙ Q.mapHomologicalComplex (.up ℤ) ≅
    roosTowerAction Q ⋙ roosF :=
  NatIso.ofComponents (fun V ↦ by
    have := roosAdditiveComparison_isIso Q V
    exact asIso (roosAdditiveComparison Q V))
    (fun f ↦ by
      simpa only [Functor.comp_map, asIso_hom] using roosAdditiveComparison_natural Q f)

private theorem canonicalKappa_hom (V : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) :
    (canonicalKappa Q).hom.app V = roosAdditiveComparison Q V := rfl

attribute [local irreducible] canonicalKappa
end CanonicalComparison

section
variable {C : Type a} {B : Type a'} [Category.{b} C] [Category.{b'} B]
  [Abelian C] [Abelian B]
  [HasCountableProducts C] [HasCountableProducts B]
  [HasLimitsOfShape ℕᵒᵖ C] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wTC} (ℕᵒᵖ ⥤ C)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ C)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
  [(lim : (ℕᵒᵖ ⥤ C) ⥤ C).Additive] [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive]
  (Q : C ⥤ B) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  (thetaC : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor ≅
    roosF ⋙ DerivedCategory.Q)
  (thetaB : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor ≅
    roosF ⋙ DerivedCategory.Q)
  (huC : ∀ I : CochainComplex (ℕᵒᵖ ⥤ C) ℤ,
    (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctorUnitQ I ≫ thetaC.hom.app I =
      DerivedCategory.Q.map (ordinaryInclusion (C := C) I))
  (huB : ∀ I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
    (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctorUnitQ I ≫ thetaB.hom.app I =
      DerivedCategory.Q.map (ordinaryInclusion (C := B) I))
  (hQ : ∀ M : ℕ → C, IsIso (piComparison Q M))
include huC huB hQ in
private theorem makeComparison : Nonempty (Comparison Q thetaC thetaB) := by
  have : PreservesLimitsOfShape (Discrete ℕ) Q := natProducts Q hQ
  let psi := fun V : CochainComplex (ℕᵒᵖ ⥤ C) ℤ ↦
    asIso (piComparison (Q.mapHomologicalComplex (.up ℤ))
      (fun n : ℕ ↦ V.asFunctor.obj (op n)))
  let kappa : roosF ⋙ Q.mapHomologicalComplex (.up ℤ) ≅
      ((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapHomologicalComplex (.up ℤ) ⋙ roosF :=
    canonicalKappa Q
  have hprod (V : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (n : ℕ) :
      (psi V).hom ≫ Pi.π _ n =
        (Q.mapHomologicalComplex (.up ℤ)).map (Pi.π _ n) :=
    piComparison_comp_π _ _ n
  have hdiag (V : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (p : ℤ) :
      (kappa.hom.app V).f (p + 1) ≫ (roosχ
        ((((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapHomologicalComplex (.up ℤ)).obj V) p).hom ≫
        biprod.fst = Q.map ((roosχ V p).hom ≫ biprod.fst) ≫ (psi V).hom.f p ∧
      (kappa.hom.app V).f (p + 1) ≫ (roosχ
        ((((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapHomologicalComplex (.up ℤ)).obj V) p).hom ≫
        biprod.snd = Q.map ((roosχ V p).hom ≫ biprod.snd) ≫ (psi V).hom.f (p + 1) := by
    constructor
    · dsimp only [kappa]
      rw [canonicalKappa_hom]
      exact comparison_fst Q V p
    · dsimp only [kappa]
      rw [canonicalKappa_hom]
      exact comparison_snd Q V p
  obtain ⟨lambda, hlambda⟩ : ∃ lambda : (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor ⋙
    Q.mapDerivedCategory ≅
      ((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapDerivedCategory ⋙
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor,
      ∀ V : CochainComplex (ℕᵒᵖ ⥤ C) ℤ,
        Q.mapDerivedCategory.map (thetaC.hom.app V) ≫
            Q.mapDerivedCategoryFactors.hom.app (roosF.obj V) ≫
            DerivedCategory.Q.map (kappa.hom.app V) =
          lambda.hom.app (DerivedCategory.Q.obj V) ≫
            (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map
              (((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapDerivedCategoryFactors.hom.app V) ≫
            thetaB.hom.app ((((Functor.whiskeringRight ℕᵒᵖ C B).obj Q).mapHomologicalComplex
              (.up ℤ)).obj V) := by
    let LA := (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor
    let LB := (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor
    let Qc := Q.mapHomologicalComplex (.up ℤ)
    let Qt := (Functor.whiskeringRight ℕᵒᵖ C B).obj Q
    let Qtc := Qt.mapHomologicalComplex (.up ℤ)
    let Qd := Q.mapDerivedCategory
    let Qtd := Qt.mapDerivedCategory
    let e₁ : DerivedCategory.Q ⋙ (LA ⋙ Qd) ≅ roosF ⋙ (Qc ⋙ DerivedCategory.Q) :=
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight thetaC Qd ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft roosF Q.mapDerivedCategoryFactors
    let e₂ : DerivedCategory.Q ⋙ (Qtd ⋙ LB) ≅ Qtc ⋙ (roosF ⋙ DerivedCategory.Q) :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight Qt.mapDerivedCategoryFactors LB ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Qtc thetaB
    let e : DerivedCategory.Q ⋙ (LA ⋙ Qd) ≅ DerivedCategory.Q ⋙ (Qtd ⋙ LB) :=
      e₁ ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight kappa DerivedCategory.Q ≪≫
        Functor.associator _ _ _ ≪≫ e₂.symm
    obtain ⟨lambda, hlambda⟩ := descendIso DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ)) (LA ⋙ Qd) (Qtd ⋙ LB) e
    refine ⟨lambda, ?_⟩
    intro V
    rw [hlambda V]
    have hh : e₁.hom.app V ≫ DerivedCategory.Q.map (kappa.hom.app V) =
        e.hom.app V ≫ e₂.hom.app V := by simp [e, Category.assoc]
    simpa only [e₁, e₂, Iso.trans_hom, Iso.symm_hom, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatTrans.comp_app, Category.id_comp, Category.comp_id, Category.assoc,
      Functor.map_id] using hh
  let Qc := Q.mapHomologicalComplex (.up ℤ)
  let Qt := (Functor.whiskeringRight ℕᵒᵖ C B).obj Q
  let Qtc := Qt.mapHomologicalComplex (.up ℤ)
  let beta := limitBeta Q hQ
  have hι (I : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) :
      Qc.map (ordinaryInclusion I) ≫ kappa.hom.app I =
        (beta I).hom ≫ ordinaryInclusion (Qtc.obj I) := by
    have hprodLift :
        Qc.map (Pi.lift (f := fun n : ℕ ↦ I.asFunctor.obj (op n)) (fun n : ℕ ↦
          (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I)) ≫
            (psi I).hom =
        (beta I).hom ≫ Pi.lift (f := fun n : ℕ ↦ (Qtc.obj I).asFunctor.obj (op n)) (fun n : ℕ ↦
          (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app (Qtc.obj I)) := by
      apply Pi.hom_ext
      intro n
      simp only [Category.assoc]
      erw [hprod, Pi.lift_π]
      rw [← Qc.map_comp, Pi.lift_π]
      exact (limitBeta_projection Q hQ I n).symm
    dsimp only [Qc]
    apply HomologicalComplex.Hom.ext
    funext i
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
    apply (cancel_mono (roosχ (Qtc.obj I) p).hom).mp
    apply biprod.hom_ext
    · simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        Category.assoc]
      erw [(hdiag I p).1]
      rw [← Category.assoc, ← Q.map_comp]
      have hi := congrArg (fun f ↦ f ≫ biprod.fst) (ordinaryInclusion_coordinates I p)
      simp only [Category.assoc, biprod.lift_fst] at hi
      rw [hi, Q.map_zero, zero_comp]
      have hiB := congrArg (fun z ↦ (beta I).hom.f (p + 1) ≫ z ≫ biprod.fst)
        (ordinaryInclusion_coordinates (Qtc.obj I) p)
      simpa only [Category.assoc, biprod.lift_fst, comp_zero] using hiB.symm
    · simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        Category.assoc]
      erw [(hdiag I p).2]
      rw [← Category.assoc, ← Q.map_comp]
      have hi := congrArg (fun f ↦ f ≫ biprod.snd) (ordinaryInclusion_coordinates I p)
      simp only [Category.assoc, biprod.lift_snd] at hi
      rw [hi]
      have hiB := congrArg (fun z ↦ (beta I).hom.f (p + 1) ≫ z ≫ biprod.snd)
        (ordinaryInclusion_coordinates (Qtc.obj I) p)
      have hp := congrArg (fun f ↦ f.f (p + 1)) hprodLift
      dsimp only [Qc, Functor.mapHomologicalComplex_map_f,
        HomologicalComplex.comp_f] at hp
      simp only [Category.assoc, biprod.lift_snd] at hiB
      simpa only [Category.assoc] using hp.trans hiB.symm
  have hunit (I : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) :
      Q.mapDerivedCategory.map
          ((lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctorUnitQ I) ≫
        lambda.hom.app (DerivedCategory.Q.obj I) ≫
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map
          (Qt.mapDerivedCategoryFactors.hom.app I) =
      Q.mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map (beta I).hom ≫
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctorUnitQ (Qtc.obj I) := by
    apply (cancel_mono (thetaB.hom.app (Qtc.obj I))).mp
    calc
      _ = Q.mapDerivedCategory.map
          ((lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctorUnitQ I ≫ thetaC.hom.app I) ≫
          Q.mapDerivedCategoryFactors.hom.app (roosF.obj I) ≫
          DerivedCategory.Q.map (kappa.hom.app I) := by
        rw [Functor.map_comp]
        simpa only [Category.assoc] using congrArg (fun z ↦
          Q.mapDerivedCategory.map
            ((lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctorUnitQ I) ≫ z)
          (hlambda I).symm
      _ = Q.mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map (Qc.map (ordinaryInclusion I) ≫ kappa.hom.app I) := by
        simpa only [huC, Functor.map_comp, Category.assoc] using
          congrArg (fun z ↦ z ≫ DerivedCategory.Q.map (kappa.hom.app I))
            (Q.mapDerivedCategoryFactors_hom_naturality (ordinaryInclusion I))
      _ = _ := by
        rw [hι, Functor.map_comp]
        simpa only [Category.assoc] using
          congrArg (fun z ↦ Q.mapDerivedCategoryFactors.hom.app
            (((lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ)).obj I) ≫
            DerivedCategory.Q.map (beta I).hom ≫ z)
            (huB (Qtc.obj I)).symm
  refine ⟨{
    product := psi
    product_projection := hprod
    kappa := kappa
    diagonal := hdiag
    signed_diagonal := ?_
    beta := beta
    beta_projection := limitBeta_projection Q hQ
    comparison := lambda
    model := hlambda
    resolutions := by
      intro V I q _ _ J e _ _
      have hi : IsIso ((lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctorUnitQ I) := by
        rw [(lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctorUnitQ_eq]; infer_instance
      have hj : IsIso ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctorUnitQ J) := by
        rw [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctorUnitQ_eq]; infer_instance
      let dI := asIso ((lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctorUnitQ I) ≪≫
        (asIso ((lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor.map (DerivedCategory.Q.map q))).symm
      let dJ := asIso ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctorUnitQ J) ≪≫
        (asIso ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map (DerivedCategory.Q.map e))).symm
      have hdI : dI.hom ≫ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor.map (DerivedCategory.Q.map q) =
          (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctorUnitQ I := by simp [dI]
      have hdJ : dJ.hom ≫ (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map (DerivedCategory.Q.map e) =
          (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctorUnitQ J := by simp [dJ]
      refine ⟨dI, dJ, hdI, hdJ, ?_⟩
      have hnat := lambda.hom.naturality (DerivedCategory.Q.map q)
      have hfac := ((Functor.whiskeringRight ℕᵒᵖ C B).obj
        Q).mapDerivedCategoryFactors.hom.naturality q
      dsimp only [Functor.comp_map] at hnat hfac
      calc
        _ = Q.mapDerivedCategory.map ((lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctorUnitQ I) ≫
            lambda.hom.app (DerivedCategory.Q.obj I) ≫
            (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map (((Functor.whiskeringRight ℕᵒᵖ C B).obj
              Q).mapDerivedCategoryFactors.hom.app I) := by
          erw [← (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map_comp, ← hfac, (lim : (ℕᵒᵖ ⥤ B) ⥤
            B).rightDerivedFunctor.map_comp,
            ← reassoc_of% hnat, ← Q.mapDerivedCategory.map_comp_assoc, hdI]
        _ = _ := by
          rw [hunit]
          apply (cancel_mono ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map
            (DerivedCategory.Q.map e))).mp
          simp only [Category.assoc, hdJ]
          exact congrArg (fun z ↦
            Q.mapDerivedCategoryFactors.hom.app (((lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex
              (.up ℤ)).obj I) ≫
              DerivedCategory.Q.map (beta I).hom ≫ z)
            ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctorUnitQ_naturality e).symm
    augmentations := by
      intro V P gamma hgamma
      let Qc := Q.mapHomologicalComplex (.up ℤ)
      let iota := roosAugment gamma hgamma
      refine ⟨iota, Qc.map iota ≫ kappa.hom.app V,
        roosAugment_χ gamma hgamma, ?_, rfl⟩
      intro p
      simpa only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        kappa, canonicalKappa_hom, roosTowerAction, Qc, iota] using
        roosAdditiveComparison_augmentation Q V P gamma hgamma p
  }⟩
  intro V p
  constructor
  · simpa [signedCoordinates, Category.assoc] using (hdiag V p).2
  · simpa [signedCoordinates, Category.assoc, Functor.map_neg] using
      congrArg Neg.neg (hdiag V p).1
end
section
variable {C : Type a} [Category.{b} C] [Abelian C]
  [HasCountableProducts C] [HasLimitsOfShape ℕᵒᵖ C]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wTC} (ℕᵒᵖ ⥤ C)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ C)]
  [(lim : (ℕᵒᵖ ⥤ C) ⥤ C).Additive]
private theorem normalizedCoordinates
    (theta : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor ≅
      roosF ⋙ DerivedCategory.Q)
    (hu : ∀ I : CochainComplex (ℕᵒᵖ ⥤ C) ℤ,
      (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctorUnitQ I ≫ theta.hom.app I =
        DerivedCategory.Q.map (ordinaryInclusion I))
    (I : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) [I.IsKInjective]
    (_hI : ∀ p : ℤ, Injective (I.X p)) :
    ∃ iota : ((lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ)).obj I ⟶ roosF.obj I,
      QuasiIso iota ∧
      (∀ p : ℤ, iota.f (p + 1) ≫ (roosχ I p).hom =
        biprod.lift 0 ((Pi.lift (fun n : ℕ ↦
          (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I)).f (p + 1))) ∧
      (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctorUnitQ I ≫ theta.hom.app I =
        DerivedCategory.Q.map iota := by
  have : IsIso ((lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctorUnitQ I) := by
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance
  have : IsIso (DerivedCategory.Q.map (ordinaryInclusion I)) := by
    rw [← hu I]
    infer_instance
  have hqi := (DerivedCategory.isIso_Q_map_iff_quasiIso C (ordinaryInclusion I)).mp
    inferInstance
  refine ⟨ordinaryInclusion I, hqi, ?_, hu I⟩
  intro p
  exact ordinaryInclusion_coordinates I p
end
private theorem normalizedRoos
    {C : Type a} [Category.{b} C] [Abelian C]
    [IsGrothendieckAbelian.{b} C] [IsGrothendieckAbelian.{b} (ℕᵒᵖ ⥤ C)]
    [HasCountableProducts C] [HasLimitsOfShape ℕᵒᵖ C]
    [HasExactLimitsOfShape (Discrete ℕ) C]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{wT} (ℕᵒᵖ ⥤ C)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ C)]
    [(lim : (ℕᵒᵖ ⥤ C) ⥤ C).Additive] :
    ∃ theta : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor ≅
        roosF ⋙ DerivedCategory.Q,
      ∀ I : CochainComplex (ℕᵒᵖ ⥤ C) ℤ,
        (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctorUnitQ I ≫ theta.hom.app I =
          DerivedCategory.Q.map ((ordinaryLimitIso (A := C)).hom.app I ≫ roosι I) := by
  let L := (lim : (ℕᵒᵖ ⥤ C) ⥤ C)
  let eta : L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ L.rightDerivedFunctor :=
    { app := L.rightDerivedFunctorUnitQ
      naturality := fun _ _ f ↦ L.rightDerivedFunctorUnitQ_naturality f }
  let beta := (Functor.isoWhiskerRight (ordinaryLimitIso (A := C)).symm
    DerivedCategory.Q).hom ≫ eta
  obtain ⟨e, he⟩ := normalizedRoosIso L.rightDerivedFunctor beta (fun I hI ↦ by
    have := hI
    dsimp only [beta, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, eta]
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance)
  refine ⟨e.symm, fun I ↦ ?_⟩
  have hh := congr_app he I
  change DerivedCategory.Q.map (roosι I) ≫ e.hom.app I =
    DerivedCategory.Q.map ((ordinaryLimitIso (A := C)).inv.app I) ≫
      L.rightDerivedFunctorUnitQ I at hh
  apply (cancel_mono (e.hom.app I)).mp
  simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app]
  rw [Functor.map_comp, Category.assoc, hh, ← Category.assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app]
  simp
  rfl
private theorem signedMatrix
    {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
    {P Q P' Q' Z Z' : C} (c : Z ≅ P ⊞ Q) (c' : Z' ≅ P' ⊞ Q')
    (d : Z ⟶ Z') (dp : P ⟶ P') (dq : Q ⟶ Q') (u : Q ⟶ P')
    (hd : d ≫ c'.hom = c.hom ≫
      biprod.lift (-(biprod.fst ≫ dp) - biprod.snd ≫ u) (biprod.snd ≫ dq)) :
    (c ≪≫ biprod.braiding _ _ ≪≫
      biprod.mapIso (Iso.refl _) (-Iso.refl _)).inv ≫ d ≫
      (c' ≪≫ biprod.braiding _ _ ≪≫
        biprod.mapIso (Iso.refl _) (-Iso.refl _)).hom =
      biprod.desc (biprod.lift dq u) (biprod.lift 0 (-dp)) := by
  apply (cancel_epi (c ≪≫ biprod.braiding _ _ ≪≫
    biprod.mapIso (Iso.refl _) (-Iso.refl _)).hom).mp
  rw [Iso.hom_inv_id_assoc]
  dsimp only [Iso.trans_hom]
  simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc, hd]
  simp only [Category.assoc]
  congr 1
  apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
    simp only [Iso.trans_hom, biprod.mapIso_hom, Iso.refl_hom, Preadditive.neg_iso_hom,
      biprod.braiding_hom, biprod.lift_eq, biprod.desc_eq, biprod.map_eq,
      Preadditive.add_comp, Preadditive.comp_add, Category.assoc, biprod.map_fst, biprod.map_snd,
      biprod.lift_fst, biprod.lift_snd, biprod.inl_desc, biprod.inr_desc,
      biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd,
      Category.id_comp, Category.comp_id, comp_zero, zero_comp,
      Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_sub,
      neg_neg, neg_zero, sub_zero, zero_sub, zero_add, add_zero,
      biprod.inl_fst_assoc, biprod.inl_snd_assoc,
      biprod.inr_fst_assoc, biprod.inr_snd_assoc]

attribute [local semireducible] roosF roosχ
private theorem signedDifferential {C : Type*} [Category* C] [Abelian C]
    [HasCountableProducts C] (V : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (p : ℤ) :
    (signedCoordinates V p).inv ≫ (roosF.obj V).d (p + 1) (p + 1 + 1) ≫
        (signedCoordinates V (p + 1)).hom =
      biprod.desc
        (biprod.lift ((roosP V).d (p + 1) (p + 1 + 1)) ((roosU V).f (p + 1)))
        (biprod.lift 0 (-((roosP V).d p (p + 1)))) := by
  have hd : (roosF.obj V).d (p + 1) (p + 1 + 1) ≫ (roosχ V (p + 1)).hom =
      (roosχ V p).hom ≫ biprod.lift
        (-(biprod.fst ≫ (roosP V).d p (p + 1)) -
          biprod.snd ≫ (roosU V).f (p + 1))
        (biprod.snd ≫ (roosP V).d (p + 1) (p + 1 + 1)) := by
    have hh := roos_cone_d (roosP V) (roosU V) p
    have hc (q : ℤ) : roos_cone_coords (roosU V) q = roosχ V q := rfl
    rw [hc, hc] at hh
    simpa only [roosF, roosConeFunctor, Functor.comp_obj] using hh
  exact signedMatrix (roosχ V p) (roosχ V (p + 1)) _ _ _ _ hd

attribute [local irreducible] roosF roosχ
private theorem descendPasted
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    {B : Type*} [Category* B] (F G : D ⥤ B) (H K : C ⥤ B)
    (e₁ : Q ⋙ F ≅ H) (e₂ : Q ⋙ G ≅ K) (middle : H ≅ K) :
    ∃ a : F ≅ G, ∀ X,
      a.hom.app (Q.obj X) ≫ e₂.hom.app X = e₁.hom.app X ≫ middle.hom.app X := by
  obtain ⟨a, ha⟩ := descendIso Q W F G (e₁ ≪≫ middle ≪≫ e₂.symm)
  refine ⟨a, ?_⟩
  intro X
  rw [ha X]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]

section
variable {S C B : Type*} [Category* S] [Category* C] [Category* B]
  [Abelian S] [Abelian C] [Abelian B]
  [HasCountableProducts C] [HasCountableProducts B]
  [HasLimitsOfShape ℕᵒᵖ C] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory S] [HasDerivedCategory C] [HasDerivedCategory B]
  [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ C)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
  [(lim : (ℕᵒᵖ ⥤ C) ⥤ C).Additive] [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive]
  (U : S ⥤ (ℕᵒᵖ ⥤ C)) [U.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (G : S ⥤ S) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (T : C ⥤ B) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]

/-- The realization comparison for an exact functor into strict towers.
Source: Stacks 0941 (blueprint: lem-trf-point-system-normalized-comparison-data). -/
def systemModel
    (theta : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor ≅
      roosF ⋙ DerivedCategory.Q) (M : CochainComplex S ℤ) :=
  (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor.mapIso
    (U.mapDerivedCategoryFactors.app M) ≪≫
    theta.app ((U.mapHomologicalComplex (.up ℤ)).obj M)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem realizationDescentGeneric
    (theta : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor ≅ roosF ⋙
      DerivedCategory.Q)
    (eta : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor ≅ roosF ⋙
      DerivedCategory.Q)
    (coefficient : (G).mapHomologicalComplex (.up ℤ) ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      U.mapHomologicalComplex (.up ℤ) ⋙ ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
        (F)).mapHomologicalComplex (.up ℤ))
    (fComparison : Comparison (C := C) (B := C) F theta theta)
    (tComparison : Comparison (C := C) T theta eta) :
    ∃ (a : (U.mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor) ⋙
      (F).mapDerivedCategory ≅
      (G).mapDerivedCategory ⋙ (U.mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor))
      (zeta : (U ⋙ (Functor.whiskeringRight ℕᵒᵖ C B).obj T).mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ B)
        ⥤ B).rightDerivedFunctor ≅
        (U.mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor) ⋙
          (T).mapDerivedCategory),
      (∀ M : CochainComplex (S) ℤ,
        a.hom.app (DerivedCategory.Q.obj M) ≫
          ((U.mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor)).map
            ((G).mapDerivedCategoryFactors.hom.app M) ≫
          (systemModel U theta
            (((G).mapHomologicalComplex (.up ℤ)).obj M)).hom =
        (F).mapDerivedCategory.map ((systemModel U theta M).hom) ≫
          (F).mapDerivedCategoryFactors.hom.app (roosF.obj ((U.mapHomologicalComplex (.up ℤ)).obj
            M)) ≫
          DerivedCategory.Q.map (fComparison.kappa.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj
            M)) ≫
          DerivedCategory.Q.map (roosF.map (coefficient.inv.app M))) ∧
      (∀ M : CochainComplex (S) ℤ,
        zeta.hom.app (DerivedCategory.Q.obj M) ≫
          (T).mapDerivedCategory.map ((systemModel U theta M).hom) ≫
          (T).mapDerivedCategoryFactors.hom.app (roosF.obj ((U.mapHomologicalComplex (.up ℤ)).obj
            M)) ≫
          DerivedCategory.Q.map (tComparison.kappa.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj
            M)) =
        ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor).map
          (((U ⋙ (Functor.whiskeringRight ℕᵒᵖ C B).obj T)).mapDerivedCategoryFactors.hom.app M) ≫
          eta.hom.app (((U ⋙ (Functor.whiskeringRight ℕᵒᵖ C B).obj T).mapHomologicalComplex (.up
            ℤ)).obj M)) := by
  let s : DerivedCategory.Q ⋙ (U.mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor)
    ≅ U.mapHomologicalComplex (.up ℤ) ⋙ roosF ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight (U).mapDerivedCategoryFactors ((lim : (ℕᵒᵖ ⥤ C) ⥤
      C).rightDerivedFunctor) ≪≫
      Functor.isoWhiskerLeft (U.mapHomologicalComplex (.up ℤ)) theta
  let f := F
  let gc := (G).mapHomologicalComplex (.up ℤ)
  let e₁ : DerivedCategory.Q ⋙ ((U.mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤
    C).rightDerivedFunctor) ⋙ f.mapDerivedCategory) ≅
      U.mapHomologicalComplex (.up ℤ) ⋙ roosF ⋙ f.mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
    Functor.isoWhiskerRight s f.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (U.mapHomologicalComplex (.up ℤ) ⋙ roosF) f.mapDerivedCategoryFactors
  let e₂ : DerivedCategory.Q ⋙ ((G).mapDerivedCategory ⋙ (U.mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ C)
    ⥤ C).rightDerivedFunctor)) ≅
      gc ⋙ U.mapHomologicalComplex (.up ℤ) ⋙ roosF ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight (G).mapDerivedCategoryFactors ((U.mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤
      C) ⥤ C).rightDerivedFunctor)) ≪≫
      Functor.isoWhiskerLeft gc s
  let middle : U.mapHomologicalComplex (.up ℤ) ⋙ roosF ⋙ f.mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q ≅
      gc ⋙ U.mapHomologicalComplex (.up ℤ) ⋙ roosF ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft (U.mapHomologicalComplex (.up ℤ))
      (Functor.isoWhiskerRight fComparison.kappa DerivedCategory.Q) ≪≫
      Functor.isoWhiskerRight coefficient.symm (roosF ⋙ DerivedCategory.Q)
  obtain ⟨a, ha⟩ := descendPasted DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) _ _ _ _ e₁ e₂ middle
  let t := T
  let e₃ : DerivedCategory.Q ⋙
      ((U ⋙ (Functor.whiskeringRight ℕᵒᵖ C B).obj T).mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤
        B).rightDerivedFunctor) ≅
      (U ⋙ (Functor.whiskeringRight ℕᵒᵖ C B).obj T).mapHomologicalComplex (.up ℤ) ⋙ roosF ⋙
        DerivedCategory.Q :=
    Functor.isoWhiskerRight ((U ⋙ (Functor.whiskeringRight ℕᵒᵖ C B).obj
      T)).mapDerivedCategoryFactors
      ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor) ≪≫
      Functor.isoWhiskerLeft ((U ⋙ (Functor.whiskeringRight ℕᵒᵖ C B).obj T).mapHomologicalComplex
        (.up ℤ)) eta
  let e₄ : DerivedCategory.Q ⋙ ((U.mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤
    C).rightDerivedFunctor) ⋙ t.mapDerivedCategory) ≅
      (U ⋙ (Functor.whiskeringRight ℕᵒᵖ C B).obj T).mapHomologicalComplex (.up ℤ) ⋙ roosF ⋙
        DerivedCategory.Q :=
    Functor.isoWhiskerRight s t.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (U.mapHomologicalComplex (.up ℤ) ⋙ roosF)
        t.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerLeft (U.mapHomologicalComplex (.up ℤ))
        (Functor.isoWhiskerRight tComparison.kappa DerivedCategory.Q)
  obtain ⟨zeta, hz⟩ := descendPasted DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) _ _ _ _ e₃ e₄ (Iso.refl _)
  have hs (M) : s.hom.app M = (systemModel U theta M).hom := by
    dsimp only [s, systemModel, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.mapIso_hom, Iso.app_hom]
  refine ⟨a, zeta, ?_, ?_⟩
  · intro M
    have hh := ha M
    simpa only [e₁, e₂, middle, f, gc, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map,
      Functor.comp_obj, hs, Category.assoc] using hh
  · intro M
    have h₄ : e₄.hom.app M =
        T.mapDerivedCategory.map (s.hom.app M) ≫
          T.mapDerivedCategoryFactors.hom.app
            (roosF.obj ((U.mapHomologicalComplex (.up ℤ)).obj M)) ≫
          DerivedCategory.Q.map (tComparison.kappa.hom.app
            ((U.mapHomologicalComplex (.up ℤ)).obj M)) := by rfl
    have h₃ : e₃.hom.app M =
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map
          ((U ⋙ (Functor.whiskeringRight ℕᵒᵖ C B).obj T).mapDerivedCategoryFactors.hom.app M) ≫
          eta.hom.app
            (((U ⋙ (Functor.whiskeringRight ℕᵒᵖ C B).obj T).mapHomologicalComplex (.up ℤ)).obj M)
        := by rfl
    have hh := hz M
    rw [h₄, h₃, hs] at hh
    simp only [Iso.refl_hom, NatTrans.id_app, Category.comp_id, Category.assoc] at hh
    set_option backward.isDefEq.respectTransparency false in
      exact hh
end

/-- The realization comparison uses the recorded localization factor and one fixed theta.
Source: blueprint proof (3), refinement step 6
(blueprint: lem-trf-point-system-normalized-comparison-data). -/
def systemRealization
    (theta : DerivedCategory.Q ⋙ LA D l E ≅ roosF ⋙ DerivedCategory.Q)
    (M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ) :
    (L D l E).obj (DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj (roosF.obj ((X D l E).obj M)) :=
  systemModel (U D l E) theta M

/-- Abelian structure of the existing completed-module category.
Source: Stacks 03CW (blueprint: lem-trf-point-system-normalized-comparison-data). -/
@[reducible] instance ambientAbelian : Abelian (A D l E) := inferInstance

/-- Standard localization of completed-module towers, at their original universe.
Source: Stacks 0941 (blueprint: lem-trf-point-system-normalized-comparison-data). -/
instance ambientTowerDerived : HasDerivedCategory (ℕᵒᵖ ⥤ A D l E) :=
  coefficientConstantTowerDerived l E (Spec (.of D.k))

/-- Simultaneous resolutions of completed-module towers.
Source: Stacks 0941 (blueprint: lem-trf-point-system-normalized-comparison-data). -/
instance ambientTowerKInjectives : Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A D l E) :=
  coefficientConstantTowersKInjectives l E (Spec (.of D.k))

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The unchanged strict augmentation normalization, with its proposition named to keep
structure-generated declarations small.
Source: Stacks 0941 (blueprint: lem-trf-point-system-normalized-comparison-data). -/
def ModelNormalization
    {C : Type a} [Category.{b} C] [Abelian C]
    [HasCountableProducts C] [HasLimitsOfShape ℕᵒᵖ C]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wTC} (ℕᵒᵖ ⥤ C)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ C)]
    [(lim : (ℕᵒᵖ ⥤ C) ⥤ C).Additive]
    (theta : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor ≅
      roosF ⋙ DerivedCategory.Q) : Prop :=
  ∀ (I : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) [I.IsKInjective]
    (_hI : ∀ p : ℤ, Injective (I.X p)),
    ∃ iota : ((lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ)).obj I ⟶
      roosF.obj I,
      QuasiIso iota ∧
      (∀ p : ℤ, iota.f (p + 1) ≫ (roosχ I p).hom =
        biprod.lift 0 ((Pi.lift (fun n : ℕ ↦
          (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I)).f (p + 1))) ∧
      (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctorUnitQ I ≫
        theta.hom.app I = DerivedCategory.Q.map iota

attribute [local irreducible] ModelNormalization

/-- The recorded comparison equation, named without changing its content.
Source: blueprint proof (3)
(blueprint: lem-trf-point-system-normalized-comparison-data). -/
def DataCoefficientSections (r : ℕ)
    (coefficient : (G D l E r).mapHomologicalComplex (.up ℤ) ⋙ X D l E ≅
      X D l E ⋙ ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
        (F D l E r)).mapHomologicalComplex (.up ℤ)) : Prop :=
  ∀ (M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ)
      (i : ℤ) (n : ℕ) (V : (Spec (.of D.k)).ProEt)
      (x : ((((G D l E r).mapHomologicalComplex (.up ℤ) ⋙ X D l E).obj M).X i).obj
        (op n) |>.val.obj (op V)),
      HEq (((((coefficient.hom.app M).f i).app (op n)).val.app (op V)) x) x

/-- The recorded comparison equation, named without changing its content.
Source: blueprint proof (3)
(blueprint: lem-trf-point-system-normalized-comparison-data). -/
def DataCoefficientProjection (r : ℕ) : Prop :=
  ∀ n : ℕ,
    inverseImageCompletedCoefficientMap l E (PointSystemTransport.pointPower D r).hom ≫
        limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n) =
      (isoSectionwiseInverseImage (PointSystemTransport.pointPower D r).hom
        RingCat.{max u (t + 1)}).map
          (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n)) ≫
        inverseImageFiniteCoefficientMap l E (PointSystemTransport.pointPower D r).hom n

/-- The recorded comparison equation, named without changing its content.
Source: blueprint proof (3)
(blueprint: lem-trf-point-system-normalized-comparison-data). -/
def DataFiniteTensorUnit (r : ℕ) : Prop :=
  ∀ (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ),
    IsIso (inverseImageFiniteComparisonComplex l E
      (PointSystemTransport.pointPower D r).hom n K)

attribute [local irreducible] systemModel

section GenericData
variable {S C B : Type*} [Category* S] [Category* C] [Category* B]
  [Abelian S] [Abelian C] [Abelian B]
  [HasCountableProducts C] [HasCountableProducts B]
  [HasLimitsOfShape ℕᵒᵖ C] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory S] [HasDerivedCategory C] [HasDerivedCategory B]
  [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ C)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
  [(lim : (ℕᵒᵖ ⥤ C) ⥤ C).Additive] [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive]
  (U : S ⥤ (ℕᵒᵖ ⥤ C)) [U.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (G : S ⥤ S) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (T : C ⥤ B) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  (sections_property : (G.mapHomologicalComplex (.up ℤ) ⋙ U.mapHomologicalComplex (.up ℤ) ≅
    U.mapHomologicalComplex (.up ℤ) ⋙ ((Functor.whiskeringRight ℕᵒᵖ C C).obj
      F).mapHomologicalComplex (.up ℤ)) → Prop)
  (projection_property tensor_unit_property : Prop)

/-- The simultaneous comparison bundle, parametrized before specializing the coefficient site.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-normalized-comparison-data). -/
structure DataCore where
  coefficient : G.mapHomologicalComplex (.up ℤ) ⋙ U.mapHomologicalComplex (.up ℤ) ≅
    U.mapHomologicalComplex (.up ℤ) ⋙ ((Functor.whiskeringRight ℕᵒᵖ C C).obj
      F).mapHomologicalComplex (.up ℤ)
  coefficient_sections : sections_property coefficient
  coefficient_projection : projection_property
  finite_tensor_unit : tensor_unit_property
  theta : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor ≅ roosF ⋙ DerivedCategory.Q
  theta_normalized : ModelNormalization theta
  eta : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor ≅ roosF ⋙ DerivedCategory.Q
  eta_normalized : ModelNormalization eta
  inverseImage : Comparison F theta theta
  sections : Comparison T theta eta
  a : (U.mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor) ⋙ F.mapDerivedCategory ≅
    G.mapDerivedCategory ⋙ (U.mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor)
  zeta : (U ⋙ (Functor.whiskeringRight ℕᵒᵖ C B).obj T).mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤
    B).rightDerivedFunctor ≅
    (U.mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor) ⋙ T.mapDerivedCategory
  a_model : ∀ M : CochainComplex S ℤ,
    a.hom.app (DerivedCategory.Q.obj M) ≫
      (U.mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor).map
        (G.mapDerivedCategoryFactors.hom.app M) ≫
      (systemModel U theta ((G.mapHomologicalComplex (.up ℤ)).obj M)).hom =
    F.mapDerivedCategory.map ((systemModel U theta M).hom) ≫
      F.mapDerivedCategoryFactors.hom.app (roosF.obj ((U.mapHomologicalComplex (.up ℤ)).obj M)) ≫
      DerivedCategory.Q.map (inverseImage.kappa.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj M)) ≫
      DerivedCategory.Q.map (roosF.map (coefficient.inv.app M))
  zeta_model : ∀ M : CochainComplex S ℤ,
    zeta.hom.app (DerivedCategory.Q.obj M) ≫
      T.mapDerivedCategory.map ((systemModel U theta M).hom) ≫
      T.mapDerivedCategoryFactors.hom.app (roosF.obj ((U.mapHomologicalComplex (.up ℤ)).obj M)) ≫
      DerivedCategory.Q.map (sections.kappa.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj M)) =
    (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map
      ((U ⋙ (Functor.whiskeringRight ℕᵒᵖ C B).obj T).mapDerivedCategoryFactors.hom.app M) ≫
      eta.hom.app (((U ⋙ (Functor.whiskeringRight ℕᵒᵖ C B).obj T).mapHomologicalComplex (.up
        ℤ)).obj M)
  signed_differential : ∀ (V : CochainComplex (ℕᵒᵖ ⥤ C) ℤ) (p : ℤ),
    (signedCoordinates V p).inv ≫ (roosF.obj V).d (p + 1) (p + 1 + 1) ≫
      (signedCoordinates V (p + 1)).hom =
    biprod.desc
      (biprod.lift ((roosP V).d (p + 1) (p + 1 + 1)) ((roosU V).f (p + 1)))
      (biprod.lift 0 (-((roosP V).d p (p + 1))))

private theorem dataCore_nonempty
    (coefficient : G.mapHomologicalComplex (.up ℤ) ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      U.mapHomologicalComplex (.up ℤ) ⋙
        ((Functor.whiskeringRight ℕᵒᵖ C C).obj F).mapHomologicalComplex (.up ℤ))
    (hc : sections_property coefficient) (hp : projection_property)
    (ht : tensor_unit_property)
    (theta : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctor ≅
      roosF ⋙ DerivedCategory.Q)
    (eta : DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor ≅
      roosF ⋙ DerivedCategory.Q)
    (htheta : ∀ I : CochainComplex (ℕᵒᵖ ⥤ C) ℤ,
      (lim : (ℕᵒᵖ ⥤ C) ⥤ C).rightDerivedFunctorUnitQ I ≫ theta.hom.app I =
        DerivedCategory.Q.map (ordinaryInclusion I))
    (heta : ∀ I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
      (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctorUnitQ I ≫ eta.hom.app I =
        DerivedCategory.Q.map (ordinaryInclusion I))
    (hF : ∀ M : ℕ → C, IsIso (piComparison F M))
    (hT : ∀ M : ℕ → C, IsIso (piComparison T M)) :
    Nonempty (DataCore U G F T sections_property projection_property tensor_unit_property) := by
  obtain ⟨fc⟩ := makeComparison F theta theta htheta htheta hF
  obtain ⟨tc⟩ := makeComparison T theta eta htheta heta hT
  obtain ⟨a, zeta, ha, hz⟩ :=
    realizationDescentGeneric U G F T theta eta coefficient fc tc
  refine ⟨{
    coefficient := coefficient
    coefficient_sections := hc
    coefficient_projection := hp
    finite_tensor_unit := ht
    theta := theta
    theta_normalized := ?_
    eta := eta
    eta_normalized := ?_
    inverseImage := fc
    sections := tc
    a := a
    zeta := zeta
    a_model := ha
    zeta_model := hz
    signed_differential := signedDifferential }⟩
  · unfold ModelNormalization
    exact normalizedCoordinates theta htheta
  · unfold ModelNormalization
    exact normalizedCoordinates eta heta
end GenericData

/-- Specialization of the simultaneous bundle to the actual point coefficient systems.
All fields retain their original equations.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-normalized-comparison-data). -/
abbrev Data (r : ℕ) :=
  DataCore (U D l E) (G D l E r) (F D l E r) (T D l E)
    (DataCoefficientSections D l E r) (DataCoefficientProjection D l E r)
    (DataFiniteTensorUnit D l E r)

attribute [local semireducible] ModelNormalization

attribute [local semireducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctorUnitQ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem pushforward_restrict
    {C D : Type*} [Category* C] [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    {A B : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (p : A ⟶ B) (phi : B ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R) :
    SheafOfModules.pushforward.{u} phi ⋙ SheafOfModules.restrictScalars p =
      SheafOfModules.pushforward (p ≫ phi) := by rfl

private def rho (n : ℕ) :
    SheafOfModules.derivedChangeRingIndependentCoefficients
      (ProEt.topology (Spec (.of D.k)))
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) ⟶
    ((Prod.sectR n (Spec (.of D.k)).ProEt).sheafPushforwardContinuous RingCat
      (ProEt.topology (Spec (.of D.k)))
      (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))).obj
      (PointSystemTransport.sequenceRing D l E) :=
  (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n)) ≫
    eqToHom (coefficientSequenceEvaluationRing_eq l E (Spec (.of D.k)) n).symm

private theorem uLevel (n : ℕ) :
    U D l E ⋙ (evaluation ℕᵒᵖ (A D l E)).obj (op n) =
      SheafOfModules.pushforward (F := Prod.sectR n (Spec (.of D.k)).ProEt)
        (rho D l E n) := by
  rw [coefficientSequenceRestriction_evaluation]
  have hp : (sheafCompose (ProEt.topology (Spec (.of D.k)))
      (forget₂ CommRingCat RingCat)).map
        (completedIntegralCommRingProjectionUnrestricted l E (Spec (.of D.k)) n) =
      limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n) := by
    ext V x
    rfl
  change SheafOfModules.pushforward _ ⋙ SheafOfModules.restrictScalars _ = _
  rw [hp]
  exact pushforward_restrict _ _

private theorem sites (r n : ℕ) :
    Prod.sectR n (Spec (.of D.k)).ProEt ⋙ PointSystemTransport.reindex D r =
      proEtaleIsoPostcompose (PointSystemTransport.pointPower D r).hom ⋙
        Prod.sectR n (Spec (.of D.k)).ProEt := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)


private theorem inverseSquare {C : Type*} [Category* C]
    {A B A' B' : C} (c : A ⟶ A') (d : B ⟶ B') [IsIso c] [IsIso d]
    (p : A ⟶ B) (q : A' ⟶ B') (h : c ≫ q = p ≫ d) :
    inv c ≫ p = q ≫ inv d := by
  apply (cancel_epi c).mp
  rw [IsIso.hom_inv_id_assoc, ← Category.assoc, h]
  simp

private theorem rhoSquare (r n : ℕ) :
    rho D l E n ≫
      ((Prod.sectR n (Spec (.of D.k)).ProEt).sheafPushforwardContinuous RingCat
        (ProEt.topology (Spec (.of D.k)))
        (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))).map
          (PointSystemTransport.coefficient D l E r) =
      (inv (pointRestrictionCoefficientMap l E
        (PointSystemTransport.pointPower D r).hom none)) ≫
      ((proEtaleIsoPostcompose (PointSystemTransport.pointPower D
        r).hom).sheafPushforwardContinuous RingCat _ _).map (rho D l E n) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  have hc := (PointSystemTransport.coefficient_existsUnique D l E r).exists.choose_spec n V.unop
  have hs := (PointSystemTransport.coefficient_squares D l E r n).2
  have hf (i : ℕ) :
      (eqToHom (coefficientSequenceEvaluationRing_eq l E (Spec (.of D.k)) i).symm).hom.app V =
        𝟙 _ := by
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl
  simp only [rho, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app]
  rw [hf]
  simp only [Category.comp_id]
  erw [eq_of_heq hc]
  have hi :
      inv (inverseImageCompletedCoefficientMap l E (PointSystemTransport.pointPower D r).hom) ≫
        (isoSectionwiseInverseImage (PointSystemTransport.pointPower D r).hom RingCat).map
          (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n)) =
      (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n)) ≫
        inv (inverseImageFiniteCoefficientMap l E (PointSystemTransport.pointPower D r).hom n) := by
    exact inverseSquare _ _ _ _ hs
  have hiV := (congrArg (fun f ↦ f.hom.app V) hi).symm
  have hf' :
      (eqToHom (coefficientSequenceEvaluationRing_eq l E (Spec (.of D.k)) n).symm).hom.app
        (op ((proEtaleIsoPostcompose (PointSystemTransport.pointPower D r).hom).obj V.unop)) =
        𝟙 _ := by
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl
  rw [hf']
  erw [Category.comp_id]
  exact hiV
private instance sectReindexContinuous (r n : ℕ) :
    (Prod.sectR n (Spec (.of D.k)).ProEt ⋙ PointSystemTransport.reindex D r).IsContinuous
      (ProEt.topology (Spec (.of D.k)))
      (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k)))) :=
  Functor.isContinuous_comp _ _ _
    (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k)))) _
private instance reindexSectContinuous (r n : ℕ) :
    (proEtaleIsoPostcompose (PointSystemTransport.pointPower D r).hom ⋙
      Prod.sectR n (Spec (.of D.k)).ProEt).IsContinuous
      (ProEt.topology (Spec (.of D.k)))
      (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k)))) :=
  Functor.isContinuous_comp _ _ _ (ProEt.topology (Spec (.of D.k))) _
section
variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  (K : GrothendieckTopology (ℕ × C)) (g : C ⥤ C) (n : ℕ)
  [g.IsContinuous J J]
  [((𝟭 ℕ).prod g).IsContinuous K K]
  [(Prod.sectR n C).IsContinuous J K]
  (R : Sheaf J RingCat.{u}) (S : Sheaf K RingCat.{u})
  (rho : R ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat J K).obj S)
  (c : R ⟶ (g.sheafPushforwardContinuous RingCat J J).obj R)
  (d : S ⟶ (((𝟭 ℕ).prod g).sheafPushforwardContinuous RingCat K K).obj S)
  (h : rho ≫ ((Prod.sectR n C).sheafPushforwardContinuous RingCat J K).map d =
    c ≫ (g.sheafPushforwardContinuous RingCat J J).map rho)
  (V : SheafOfModules.{u} S ⥤ SheafOfModules.{u} R)
  (he : V = SheafOfModules.pushforward rho)
private instance genericSectReindexContinuous :
    (Prod.sectR n C ⋙ (𝟭 ℕ).prod g).IsContinuous J K :=
  Functor.isContinuous_comp _ _ _ K _
private instance genericReindexSectContinuous :
    (g ⋙ Prod.sectR n C).IsContinuous J K :=
  Functor.isContinuous_comp _ _ _ J _
private def genericCoefficientLevel :
    SheafOfModules.pushforward d ⋙ V ≅ V ⋙ SheafOfModules.pushforward c :=
  Functor.isoWhiskerLeft (SheafOfModules.pushforward d) (eqToIso he) ≪≫
    SheafOfModules.pushforwardComp rho d ≪≫
    SheafOfModules.pushforwardCongr h ≪≫
    (SheafOfModules.pushforwardComp c rho).symm ≪≫
    Functor.isoWhiskerRight (eqToIso he).symm (SheafOfModules.pushforward c)
private theorem genericCoefficientLevel_sections
    (M : SheafOfModules.{u} S) (W : Cᵒᵖ)
    (x : ((SheafOfModules.pushforward d ⋙ V).obj M).val.obj W) :
    HEq (((genericCoefficientLevel J K g n R S rho c d h V he).hom.app M).val.app W x) x := by
  subst V
  dsimp only [genericCoefficientLevel, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rfl
end
private instance productReindexContinuous (r : ℕ) :
    ((𝟭 ℕ).prod (proEtaleIsoPostcompose (PointSystemTransport.pointPower D r).hom)).IsContinuous
      (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))
      (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k)))) := by
  change (PointSystemTransport.reindex D r).IsContinuous _ _
  infer_instance

private def coefficientLevel (r n : ℕ) :
    G D l E r ⋙ U D l E ⋙ (evaluation ℕᵒᵖ (A D l E)).obj (op n) ≅
      U D l E ⋙ (evaluation ℕᵒᵖ (A D l E)).obj (op n) ⋙ F D l E r :=
  genericCoefficientLevel
    (ProEt.topology (Spec (.of D.k)))
    (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))
    (proEtaleIsoPostcompose (PointSystemTransport.pointPower D r).hom) n
    _ _ (rho D l E n)
    (inv (pointRestrictionCoefficientMap l E (PointSystemTransport.pointPower D r).hom none))
    (PointSystemTransport.coefficient D l E r) (rhoSquare D l E r n)
    (U D l E ⋙ (evaluation ℕᵒᵖ (A D l E)).obj (op n)) (uLevel D l E n)

private theorem coefficientLevel_sections (r n : ℕ)
    (M : coefficientSequenceModules l E (Spec (.of D.k)))
    (V : (Spec (.of D.k)).ProEtᵒᵖ)
    (x : (((G D l E r ⋙ U D l E).obj M).obj (op n)).val.obj V) :
    HEq (((coefficientLevel D l E r n).hom.app M).val.app V x) x := by
  exact genericCoefficientLevel_sections
    (ProEt.topology (Spec (.of D.k)))
    (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))
    (proEtaleIsoPostcompose (PointSystemTransport.pointPower D r).hom) n
    _ _ (rho D l E n)
    (inv (pointRestrictionCoefficientMap l E (PointSystemTransport.pointPower D r).hom none))
    (PointSystemTransport.coefficient D l E r) (rhoSquare D l E r n)
    (U D l E ⋙ (evaluation ℕᵒᵖ (A D l E)).obj (op n)) (uLevel D l E n) M V x

private theorem heqApply {α β γ δ : Sort u} {f : α → β} {g : γ → δ}
    (hβ : β = δ) (hf : HEq f g) {x : α} {y : γ} (hx : HEq x y) :
    HEq (f x) (g y) := by
  subst δ
  exact heq_of_eq (congr_heq hf hx)

private theorem sectionsSquare
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N M' N' : SheafOfModules.{u} R}
    (a : M ≅ M') (b : N ≅ N') (f : M ⟶ N) (g : M' ⟶ N')
    (ha : ∀ V x, HEq (a.hom.val.app V x) x)
    (hb : ∀ V x, HEq (b.hom.val.app V x) x)
    (hfg : ∀ V, HEq (fun x ↦ f.val.app V x) (fun x ↦ g.val.app V x)) :
    f ≫ b.hom = a.hom ≫ g := by
  ext V x
  change b.hom.val.app V (f.val.app V x) = g.val.app V (a.hom.val.app V x)
  exact eq_of_heq ((hb V _).trans (heqApply (type_eq_of_heq (hb V (f.val.app V x))).symm
    (hfg V) (ha V x).symm))

attribute [local irreducible] coefficientLevel
section
variable {S C : Type*} [Category* S] [Category* C]
  (H K : S ⥤ (ℕᵒᵖ ⥤ C))
  (e : ∀ n : ℕᵒᵖ, H ⋙ (evaluation ℕᵒᵖ C).obj n ≅
    K ⋙ (evaluation ℕᵒᵖ C).obj n)
private def towerOfLevelIsos
    (he : ∀ (M : S) (m n : ℕᵒᵖ) (f : m ⟶ n),
      (H.obj M).map f ≫ (e n).hom.app M = (e m).hom.app M ≫ (K.obj M).map f) : H ≅ K :=
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents (fun n ↦ (e n).app M) (fun f ↦ he M _ _ f))
    (fun f ↦ NatTrans.ext (funext (fun n ↦ (e n).hom.naturality f)))
end

private def coefficientTower (r : ℕ) :
    G D l E r ⋙ U D l E ≅
      U D l E ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj (F D l E r) := by
  let hU := (coefficientSequenceRestriction_exists l E (Spec (.of D.k))).exists.choose_spec
  apply towerOfLevelIsos (G D l E r ⋙ U D l E)
    (U D l E ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj (F D l E r))
    (fun n ↦ coefficientLevel D l E r n.unop)
  intro M m n f
  apply sectionsSquare
    ((coefficientLevel D l E r m.unop).app M)
    ((coefficientLevel D l E r n.unop).app M)
  · exact fun V x ↦ coefficientLevel_sections D l E r m.unop M V x
  · exact fun V x ↦ coefficientLevel_sections D l E r n.unop M V x
  · intro V
    have h₁ := hU.2.1 ((G D l E r).obj M) m.unop n.unop (leOfHom f.unop) V
    have h₂ := hU.2.1 M m.unop n.unop (leOfHom f.unop)
      (op ((proEtaleIsoPostcompose (PointSystemTransport.pointPower D r).hom).obj V.unop))
    have hp : HEq
        (fun x : ((G D l E r).obj M).val.obj (op (m.unop, V.unop)) ↦
          ((G D l E r).obj M).val.map
            (Prod.mkHom (homOfLE (leOfHom f.unop)) (𝟙 V.unop)).op x)
        (fun x : M.val.obj (op (m.unop,
            (proEtaleIsoPostcompose (PointSystemTransport.pointPower D r).hom).obj V.unop)) ↦
          M.val.map (Prod.mkHom (homOfLE (leOfHom f.unop))
            (𝟙 ((proEtaleIsoPostcompose
              (PointSystemTransport.pointPower D r).hom).obj V.unop))).op x) := by rfl
    exact h₁.trans (hp.trans h₂.symm)

private theorem coefficientTower_sections (r n : ℕ)
    (M : coefficientSequenceModules l E (Spec (.of D.k)))
    (V : (Spec (.of D.k)).ProEtᵒᵖ)
    (x : (((G D l E r ⋙ U D l E).obj M).obj (op n)).val.obj V) :
    HEq ((((coefficientTower D l E r).hom.app M).app (op n)).val.app V x) x := by
  exact coefficientLevel_sections D l E r n M V x
attribute [local irreducible] coefficientTower

section
variable {S C : Type*} [Category* S] [Category* C] [Preadditive S] [Preadditive C]
  (G : S ⥤ S) [G.Additive] (U : S ⥤ C) [U.Additive]
  (F : C ⥤ C) [F.Additive]
private def complexCoefficient (e : G ⋙ U ≅ U ⋙ F) :
    G.mapHomologicalComplex (.up ℤ) ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      U.mapHomologicalComplex (.up ℤ) ⋙ F.mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex e (.up ℤ)
end

private def coefficientComplex (r : ℕ) :
    (G D l E r).mapHomologicalComplex (.up ℤ) ⋙ X D l E ≅
      X D l E ⋙ ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
        (F D l E r)).mapHomologicalComplex (.up ℤ) :=
  complexCoefficient (G D l E r) (U D l E)
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (F D l E r)) (coefficientTower D l E r)

private theorem coefficientComplex_sections (r : ℕ)
    (M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ)
    (i : ℤ) (n : ℕ) (V : (Spec (.of D.k)).ProEt)
    (x : ((((G D l E r).mapHomologicalComplex (.up ℤ) ⋙ X D l E).obj M).X i).obj
      (op n) |>.val.obj (op V)) :
    HEq ((((((coefficientComplex D l E r).hom.app M).f i).app (op n)).val.app (op V)) x) x := by
  exact coefficientTower_sections D l E r n (M.X i) (op V) x

attribute [local irreducible] coefficientComplex

private theorem actualNormalization :
    ∃ theta : DerivedCategory.Q ⋙ LA D l E ≅ roosF ⋙ DerivedCategory.Q,
      ∀ I : CochainComplex (ℕᵒᵖ ⥤ A D l E) ℤ,
        (lim : (ℕᵒᵖ ⥤ A D l E) ⥤ A D l E).rightDerivedFunctorUnitQ I ≫
            theta.hom.app I =
          DerivedCategory.Q.map ((ordinaryLimitIso (A := A D l E)).hom.app I ≫ roosι I) := by
  let : IsGrothendieckAbelian.{max u (t + 1)} (A D l E) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1, t, u}
      (ProEt.topology (Spec (.of D.k)))
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))).1
  let : IsGrothendieckAbelian.{max u (t + 1)} (ℕᵒᵖ ⥤ A D l E) := by
    have := diagrams_isGrothendieckAbelian (A D l E) (AsSmall.{max u (t + 1)} ℕᵒᵖ)
    exact IsGrothendieckAbelian.of_equivalence
      (Equivalence.congrLeft (AsSmall.equiv (C := ℕᵒᵖ)).symm)
  have : HasExactLimitsOfShape (Discrete ℕ) (A D l E) := (exact_products D l E).2.2.2.2.2.2.1
  exact normalizedRoos
private theorem scalarNormalization :
    ∃ eta : DerivedCategory.Q ⋙ LR.{t,u} l E ≅ roosF ⋙ DerivedCategory.Q,
      ∀ I : CochainComplex
        (ℕᵒᵖ ⥤ ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t,u} l E none)) ℤ,
        (lim : (ℕᵒᵖ ⥤ ModuleCat.{max u (t + 1)}
          (pointRestrictionScalars.{t,u} l E none)) ⥤ _).rightDerivedFunctorUnitQ I ≫
            eta.hom.app I =
          DerivedCategory.Q.map ((ordinaryLimitIso).hom.app I ≫ roosι I) := by
  let R := pointRestrictionScalars.{t,u} l E none
  let B := ModuleCat.{max u (t + 1)} R
  let : HasFilteredColimitsOfSize.{max u (t + 1), max u (t + 1)}
      (ℕᵒᵖ ⥤ B) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{max u (t + 1), max u (t + 1)}
      (ℕᵒᵖ ⥤ B) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : IsGrothendieckAbelian.{max u (t + 1)} (ℕᵒᵖ ⥤ B) := {}
  exact normalizedRoos

/-- Existence of simultaneous canonical coefficient-system and normalized Roos comparison
data, for unrestricted unbounded strict systems and unrestricted ambient realizations.
Source: literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-d-weil/
prop-trf-rational-frobenius-integral-model.proof.md, proof (3), agent refinement
(blueprint: lem-trf-point-system-normalized-comparison-data).

Proof, following the seven steps of the node:
1. The completed coefficient projection identity identifies U G with F on actual strict
systems. Finite j sends x to x tensor 1, with inverse x tensor a to c_n inverse(a)x.
The balancing relation and the coefficient reduction square prove compatibility with
all original quotient-linear transitions; differentials give the stated chain iso.
2. Inverse image is the site reindexing equivalence, with transported completed action,
so is additive and exact. Products are sectionwise; at (V,v) their comparison evaluates
the original tuple at (V,h^r v). This also fixes each product projection.
3. Point sections are exact by lem-weil-point-proetale-sections-exact. Restrict scalars
through constant sections; this changes no underlying kernels, cokernels or products.
Evaluation at (s,id) gives its product comparison. Products of R-modules are exact by
coordinatewise choice. The definition of system sections is exactly T^Tow U.
4. Product uniqueness makes the comparisons commute with 1-s and with differentials.
Apply the same product comparison to both Roos coordinates, with zero off-diagonal
entries. The inverse product comparison gives a natural chain inverse.
5. In the second coordinate chart the identity chain map is J(b,a)=(a,-b), with inverse
(x,y) to (-y,x). Direct multiplication gives d(x,y)=(dx,(1-s)x-dy). It sends (0,gamma)
to (gamma,0) and conjugates each diagonal comparison to the same two product maps.
6. Use the normalized total-limit isomorphism with its unit to fix theta and eta.
The canonical additive Roos comparison and ordinary limit cone comparison commute with
that unit by their projection formulas. Descend the theta-conjugated comparison through
ordinary derived localization, then paste with the coefficient isomorphism from step 1.
The resulting a and zeta have exactly the stated representative equations on complexes.
7. On every K-injective the derived-functor unit is invertible. Invert it and the
localized resolution arrows to define dI and dJ. Unit naturality and comparison
naturality prove the formula for every pair of resolutions. The strict augmentation
formula for the canonical additive Roos comparison preserves its zero shifted coordinate.
No boundedness, constructibility, normalization or completeness of an input is used. -/
theorem point_system_normalized_comparison_data (_hl : l ≠ D.p) (r : ℕ) (_hr : 1 ≤ r) :
    Nonempty (Data D l E r) := by
  classical
  obtain ⟨theta, htheta⟩ := actualNormalization D l E
  obtain ⟨eta, heta⟩ := scalarNormalization.{t, u} l E
  exact dataCore_nonempty (U D l E) (G D l E r) (F D l E r) (T D l E)
    (DataCoefficientSections D l E r) (DataCoefficientProjection D l E r)
    (DataFiniteTensorUnit D l E r)
    (coefficientComplex D l E r) (coefficientComplex_sections D l E r)
    (fun n ↦ (PointSystemTransport.coefficient_squares D l E r n).2)
    (PointSystemTransport.finiteComparison_isIso D l E r)
    theta eta htheta heta ((exact_products D l E).2.2.2.2.1 r)
    (exact_products D l E).2.2.2.2.2.1

end WeilConjectures.PointSystemNormalizedComparison
