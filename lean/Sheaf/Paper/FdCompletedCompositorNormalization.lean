/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q93
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.FdPullbackComparison
public import Sheaf.Paper.IntegralInverseImageComparisonComposition
public import Sheaf.Paper.PbcActualRingedExchange
public import Sheaf.Paper.IntegralPullbackStrictRoosNormalization
public import Sheaf.CategoryTheory.StrictRoosComparison
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.CompletedPullbackAdjunction
public import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization
import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus

/-! # Normalization of the completed pullback compositor

Source: main-20261015, sec-fourier-transform/sk-def-trace/def-fd-trace-function.md,
final sentence, extracted whole-tower comparison argument; Stacks 099N and 0D6D
(blueprint: lem-fd-pbc-completed-compositor-normalization).

The coefficient restriction, ordinary pullbacks, completion units, strict towers,
Roos coordinates and constructible compositors are the published constructions.
The auxiliary records spell out the identifications in the assertion, including
both cone coordinates. They are conclusions of the theorem, not its hypotheses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.pbcIntegralDatum AlgebraicGeometry.Scheme.completedAdicChangeData

universe u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The normalized Roos comparison, with its formula for every injective-term
K-injective tower resolution. Source: Stacks 0941, used in the extracted argument
(blueprint: lem-fd-pbc-completed-compositor-normalization). -/
structure FdCompletedRoosNormalization (X : Scheme.{u}) where
  rho : IntegralPullbackStrictRoos.kappaType X
    (IntegralPullbackStrictRoos.R l E X)
  inclusion : IntegralPullbackStrictRoos.inclusionType X
    (IntegralPullbackStrictRoos.R l E X)
  coordinates : IntegralPullbackStrictRoos.IsUnitNormalized X
    (IntegralPullbackStrictRoos.R l E X) rho inclusion
  resolution : ∀ (C I : IntegralPullbackStrictRoos.towerComplexes X
      (IntegralPullbackStrictRoos.R l E X))
    (q : C ⟶ I) [QuasiIso q] [I.IsKInjective]
    (_hI : ∀ i : ℤ, Injective (I.X i)),
    ∃ (epsilon : DerivedCategory.Q.obj
        (((completedTowerLimit X (IntegralPullbackStrictRoos.R l E X)).mapHomologicalComplex
          (.up ℤ)).obj I) ≅ DerivedCategory.Q.obj (roosF.obj I))
      (delta : DerivedCategory.Q.obj
        (((completedTowerLimit X (IntegralPullbackStrictRoos.R l E X)).mapHomologicalComplex
          (.up ℤ)).obj I) ≅
        (completedRlim X (IntegralPullbackStrictRoos.R l E X)).obj
          (DerivedCategory.Q.obj C)),
      epsilon.hom = DerivedCategory.Q.map (inclusion.app I) ∧
      delta.hom ≫ (completedRlim X (IntegralPullbackStrictRoos.R l E X)).map
          (DerivedCategory.Q.map q) =
        OrderedExchange.limitComplexUnit X (IntegralPullbackStrictRoos.R l E X) I ∧
      rho.hom.app C = DerivedCategory.Q.map (roosF.map q) ≫ epsilon.inv ≫ delta.hom


/-- The product map obtained from every finite-quotient comparison. Its source
is the transported framework product, rather than a replacement product.
Source: strict Roos naturality in Stacks 0941
(blueprint: lem-fd-pbc-completed-compositor-normalization). -/
def fdCompletedConeProduct {X Y : Scheme.{u}} (h : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (q : (integralOperationsPullbackTowerFunctor l E h).obj P ⋙
        (fdCoefficientTransport l E X).mapHomologicalComplex (.up ℤ) ≅
      ((IntegralPullbackStrictRoos.cxT l E h).obj
        (((fdCoefficientTransport l E Y).mapHomologicalComplex (.up ℤ)).obj P)).asFunctor) :=
  Pi.lift (fun n : ℕ ↦
    ((fdCoefficientTransport l E X).mapHomologicalComplex (.up ℤ)).map
      (Pi.π (fun m : ℕ ↦
        ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op m)) n) ≫
      q.hom.app (op n))


/-- The two ambient pullback presentations and their specified whole-cone comparison.
The ordinary comparison is fixed on tensor-unit sections and then localized on
K-flat representatives; the completed comparison is fixed by the strict Roos map.
Source: trace-definition extraction, Stacks 099N and 0D6D
(blueprint: lem-fd-pbc-completed-compositor-normalization). -/
structure FdCompletedPullbackNormalization {X Y : Scheme.{u}}
    (h : X ⟶ Y) [IsIso h]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (rho : FdCompletedRoosNormalization l E X) where
  ordinaryModules : inverseImageIntegralModules l E h ⋙ fdCoefficientTransport l E X ≅
    fdCoefficientTransport l E Y ⋙ pbcActualModulePull h (pbcIntegralDatum l E)
  ordinarySections : ∀ (M : integralTowerModules l E Y) (U : X.ProEt)
    (x : M.val.obj (op ((proEtaleIsoPostcompose h).obj U)))
    (x' : ((fdCoefficientTransport l E Y).obj M).val.obj
      (op ((proEtaleIsoPostcompose h).obj U))), HEq x' x →
    HEq ((ordinaryModules.inv.app M).val.app (op U)
      (((pbcActualModulePull h (pbcIntegralDatum l E)).obj
        ((fdCoefficientTransport l E Y).obj M)).val.map
          (proEtaleIsoCommaArrow h U).op
          (pbcActualModuleUnitSection h (pbcIntegralDatum l E)
            ((fdCoefficientTransport l E Y).obj M)
            ((proEtaleIsoPostcompose h).obj U) x'))) x
  ordinary : inverseImageIntegralDerived l E h ⋙ integralDetailedTransport X l E ≅
    integralDetailedTransport Y l E ⋙ pbcActualDerivedPull h (pbcIntegralDatum l E)
  ordinaryComputes : ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
    ∃ f : ((fdCoefficientTransport l E X).mapHomologicalComplex (.up ℤ)).obj
        (((inverseImageIntegralModules l E h).mapHomologicalComplex (.up ℤ)).obj P.obj) ⟶
      ((pbcActualModulePull h (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ)).obj
        (((fdCoefficientTransport l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj),
    (∀ i : ℤ, f.f i = ordinaryModules.hom.app (P.obj.X i)) ∧
    HEq (ordinary.hom.app (DerivedCategory.Q.obj P.obj) ≫
        (pbcActualDerivedPull h (pbcIntegralDatum l E)).map
          ((fdCoefficientTransportFactors l E Y).hom.app P.obj) ≫
        pbcActualPullComplexCounit h (pbcIntegralDatum l E)
          (((fdCoefficientTransport l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj))
      ((integralDetailedTransport X l E).map
        ((inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.app P.obj) ≫
      (fdCoefficientTransportFactors l E X).hom.app
        (((inverseImageIntegralModules l E h).mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
      DerivedCategory.Q.map f)
  strict : pbcActualStrictCompletedPull (pbcIntegralDatum l E) h ≅
    pbcActualCompletedPull h (pbcIntegralDatum l E)
  strictUnit : ∀ K, (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h).app K ≫
    strict.hom.app K = (pbcActualCompletedPullUnit h (pbcIntegralDatum l E)).app K
  comparison : integralDerivedPullback l E h ⋙ integralDetailedTransport X l E ≅
    integralDetailedTransport Y l E ⋙ pbcActualCompletedPull h (pbcIntegralDatum l E)
  tower : ∀ P : CochainComplex (integralTowerModules l E Y) ℤ,
    (integralOperationsPullbackTowerFunctor l E h).obj P ⋙
        (fdCoefficientTransport l E X).mapHomologicalComplex (.up ℤ) ≅
      ((IntegralPullbackStrictRoos.cxT l E h).obj
        (((fdCoefficientTransport l E Y).mapHomologicalComplex (.up ℤ)).obj P)).asFunctor
  towerGenerators : ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (n : ℕ) (i : ℤ) (V : Y.ProEt) (x : (P.X i).val.obj (op V))
    (x' : ((fdCoefficientTransport l E Y).obj (P.X i)).val.obj (op V)), HEq x' x →
    HEq ((((tower P).inv.app (op n)).f i).val.app
        (op ((proEtaleBaseChange h).obj V))
      (pbcActualModuleUnitSection h (pbcIntegralDatum l E)
        (((completedReductionModuleTowerFunctor Y (pbcIntegralDatum l E)).obj
          ((fdCoefficientTransport l E Y).obj (P.X i))).obj (op n)) V
        (((((completedReductionModuleUnit (pbcIntegralDatum l E) Y).app
          ((fdCoefficientTransport l E Y).obj (P.X i))).app (op n)).val.app (op V)) x')))
      (integralOperationsPullbackGenerator l E h n
        (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
        (coefficientIntegralScalarUnitSection l E Y n (P.X i) (op V) x))
  cone : ∀ P : CochainComplex (integralTowerModules l E Y) ℤ,
    ((fdCoefficientTransport l E X).mapHomologicalComplex (.up ℤ)).obj
        ((integralOperationsPullbackComplexFunctor l E h).obj P) ≅
      roosF.obj ((IntegralPullbackStrictRoos.cxT l E h).obj
        (((fdCoefficientTransport l E Y).mapHomologicalComplex (.up ℤ)).obj P))
  coneCoordinates : ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (p : ℤ),
    HEq ((cone P).hom.f (p + 1) ≫
        (roosχ ((IntegralPullbackStrictRoos.cxT l E h).obj
          (((fdCoefficientTransport l E Y).mapHomologicalComplex (.up ℤ)).obj P)) p).hom)
      (biprod.lift
        ((fdCoefficientTransport l E X).map
          ((CochainComplex.mappingCocone.snd
            (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P))).v
                (p + 1) p (by omega)) ≫ (fdCompletedConeProduct l E h P (tower P)).f p)
        ((fdCoefficientTransport l E X).map
          ((CochainComplex.mappingCocone.fst
            (scalarRoosBoundary
              ((integralOperationsPullbackTowerFunctor l E h).obj P))).f (p + 1)) ≫
          (fdCompletedConeProduct l E h P (tower P)).f (p + 1)))
  realization : ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
    HEq (comparison.hom.app (DerivedCategory.Q.obj P.obj) ≫
        strict.inv.app ((integralDetailedTransport Y l E).obj
          (DerivedCategory.Q.obj P.obj)) ≫
        (completedTowerRlim (pbcIntegralDatum l E) X).map
          ((completedTowerPullback h (pbcIntegralDatum l E)).map
            ((completedReductionTower Y (pbcIntegralDatum l E)).map
              ((fdCoefficientTransportFactors l E Y).hom.app P.obj))) ≫
        (completedTowerRlim (pbcIntegralDatum l E) X).map
          (IntegralPullbackStrictRoos.towerCounit l E h
            (((fdCoefficientTransport l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj)))
      ((integralDetailedTransport X l E).map
        ((integralDerivedPullbackComparison l E h).hom.app P) ≫
      (fdCoefficientTransportFactors l E X).hom.app
        ((integralOperationsPullbackComplexFunctor l E h).obj P.obj) ≫
      DerivedCategory.Q.map (cone P.obj).hom ≫
      rho.rho.hom.app ((IntegralPullbackStrictRoos.cxT l E h).obj
        (((fdCoefficientTransport l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj)))
  augmentation : ∀ K : DerivedCategory (integralTowerModules l E Y),
    (integralDetailedTransport X l E).map
        (inverseImagePullbackComparisonDerived l E h hX hY K) ≫
        comparison.hom.app K = ordinary.hom.app K ≫
      (pbcActualCompletedPullUnit h (pbcIntegralDatum l E)).app
        ((integralDetailedTransport Y l E).obj K)
  frameworkComplete : ∀ (K : DerivedCategory (integralTowerModules l E Y)),
    IsDerivedCompleteUnrestricted l E Y K →
      IsIso (inverseImagePullbackComparisonDerived l E h hX hY K)
  pbcComplete : ∀ (K : DerivedCategory (integralTowerModules l E Y)),
    IsDerivedCompleteUnrestricted l E Y K →
      IsIso ((pbcActualCompletedPullUnit h (pbcIntegralDatum l E)).app
        ((integralDetailedTransport Y l E).obj K))


/-- Completed pullback as a functor of the actual full complete subcategories.
Source: Stacks 099N, completion-induced adjunction
(blueprint: lem-fd-pbc-completed-compositor-normalization). -/
def fdCompletedPull {X Y : Scheme.{u}} (h : X ⟶ Y) :=
  ObjectProperty.lift (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E))
    (ObjectProperty.ι (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)) ⋙
      pbcActualCompletedPull h (pbcIntegralDatum l E))
    (fun K ↦ pbcActualCompletedPull_isComplete h (pbcIntegralDatum l E) K.obj)

/-- Restrict the actual derived direct image, with its proved preservation of
completeness. The functor's maps are the actual ambient maps.
Source: Stacks 099N
(blueprint: lem-fd-pbc-completed-compositor-normalization). -/
def fdCompletedDirect {X Y : Scheme.{u}} (h : X ⟶ Y)
    (preserves : ∀ K : ObjectProperty.FullSubcategory
      (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E)),
      PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)
        ((pbcActualDerivedPush h (pbcIntegralDatum l E)).obj K.obj)) :=
  ObjectProperty.lift (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E))
    (ObjectProperty.ι (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E)) ⋙
      pbcActualDerivedPush h (pbcIntegralDatum l E)) preserves

/-- The actual completion-induced adjunction is specified by its Hom transpose,
using the ordinary adjunction and the actual completion unit. It is not an
unconstrained adjunction on the same functors.
Source: Stacks 099N, extracted argument step 3
(blueprint: lem-fd-pbc-completed-compositor-normalization). -/
structure FdCompletedAdjunction {X Y : Scheme.{u}} (h : X ⟶ Y) where
  preserves : ∀ K : ObjectProperty.FullSubcategory
      (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E)),
    PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)
      ((pbcActualDerivedPush h (pbcIntegralDatum l E)).obj K.obj)
  adjunction : fdCompletedPull l E h ⊣ fdCompletedDirect l E h preserves
  transpose : ∀ K L (f : (fdCompletedPull l E h).obj K ⟶ L),
    (adjunction.homEquiv K L f).hom =
      (pbcActualDerivedAdjunction h (pbcIntegralDatum l E)).homEquiv K.obj L.obj
        ((pbcActualCompletedPullUnit h (pbcIntegralDatum l E)).app K.obj ≫ f.hom)

/-- The specified completed compositor is the adjunction conjugate of the
specified ordinary derived direct-image compositor, on the actual complete
subcategories and for the completion-induced Hom bijections.
Source: Stacks 099N and 0D6D, extracted argument step 3
(blueprint: lem-fd-pbc-completed-compositor-normalization). -/
def FdCompletedConjugate {U V T : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ T)
    (ah : FdCompletedAdjunction l E h) (ak : FdCompletedAdjunction l E k)
    (ahk : FdCompletedAdjunction l E (h ≫ k)) : Prop :=
  ∃ d : fdCompletedDirect l E h ah.preserves ⋙ fdCompletedDirect l E k ak.preserves ≅
      fdCompletedDirect l E (h ≫ k) ahk.preserves,
    (∀ K, (d.hom.app K).hom =
      (pbcActualDerivedDirectCompIso h k (pbcIntegralDatum l E)).hom.app K.obj) ∧
    ∀ K, HEq
      (((conjugateIsoEquiv (ak.adjunction.comp ah.adjunction)
        ahk.adjunction).symm d).hom.app K).hom
      ((pbcActualCompletedPullCompIso h k (pbcIntegralDatum l E)).inv.app K)

/-- The normalized strict Roos comparison intertwines both actual completion
units and hence the specified identity and composition comparisons.

Source: main-20261015, sec-fourier-transform/sk-def-trace/def-fd-trace-function.md,
final sentence; extracted whole-tower argument, Stacks 099N and 0D6D
(blueprint: lem-fd-pbc-completed-compositor-normalization).

Proof:
1. Identify coefficients through all finite quotient projections. The
constant/completed equivalence identifies quotient towers, transitions, derived
limits and units. Exact countable products give the normalized strict Roos
comparison. On an injective-term K-injective resolution its formula is
H(q), followed by the inverse of the inclusion (0,z), then derived limit.
It therefore sends the quotient augmentation (0,theta) to the actual strict
augmentation. This proves the ambient augmentation equation without cancelling
or inverting a completion unit.
2. For an isomorphism the sectionwise inverse image is an exact equivalence,
preserves limits and has the projection-normalized completed coefficient map.
The isomorphism-derived-pullback normalization identifies kappa with inverse
image of the actual completion unit. It is invertible on complete inputs.
The same holds for the PBC unit by the preceding equation. Reindexing preserves
completeness. The stratified-perfect characterization identifies the common
constructible categories, which are preserved by these pullbacks.
3. Use the ordinary derived adjunction and the completion reflection to obtain
the induced Hom bijection. Conjugate the fixed direct-image composition through
these bijections. The actual adjunction triangles give its unit equation;
naturality rewrites it in the displayed orientation. The identity triangle
gives the identity unit equation, again without cancelling any incomplete unit.
4. On a flat-term K-flat representative the ordinary compositor is the class
of the termwise module-pullback compositor. Its finite reductions preserve the
tensor generators with scalar 1 and all quotient transitions. Thus the ordinary
map used by conjugation is precisely the fixed finite termwise compositor,
as also computed by the ringed derived monoidal comparison.
5. For the framework realization write R for reduction, L for realization and
e for the whole-system counit. The triangle e(R K) R(u K)=1 is an equality of
entire quotient diagrams. Applying the two pullbacks and L identifies the
counit-built eta after the two augmentations with the twice-pulled quotient
augmentation. Both Roos coordinates are fixed, with shifted coordinate zero.
The termwise composition equation and c-s=eta-inverse L(c) yield the framework
unit-normalized compositor equation.
6. The identical whole-system triangle with no reindexing proves the framework
identity normalization, with the same zero-shifted-coordinate augmentation.
7. On a complete constructible K precompose the desired comparison equation
with its invertible kappa-s for the composite. Both sides become the PBC unit
normalization, using naturality and the ambient augmentation equation. Cancel
only this complete-input isomorphism. The identity follows in the same way.
Restore the fixed coefficient restrictions; fullness gives exactly the two
integral equations displayed below. -/
theorem fdCompletedCompositorNormalization
    (Omega : Type w) [Field Omega] [Algebra ℚ_[l] Omega] [IsAlgClosure ℚ_[l] Omega]
    (E0 : Padic.FiniteCoefficientFields l Omega)
    (D : IntegralComparisonSystem.{u} l)
    {U V T : Scheme.{u}} [IsNoetherian U] [IsNoetherian V] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim V ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iU : Fact (∀ x : U, IsUnit (l : U.presheaf.stalk x))]
    [iV : Fact (∀ x : V, IsUnit (l : V.presheaf.stalk x))]
    [iT : Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]
    (h : U ⟶ V) (k : V ⟶ T) [IsIso h] [IsIso k] :
    ∃ (rU : FdCompletedRoosNormalization l (pbcFiniteField.{u} l Omega E0) U)
      (rV : FdCompletedRoosNormalization l (pbcFiniteField.{u} l Omega E0) V)
      (rT : FdCompletedRoosNormalization l (pbcFiniteField.{u} l Omega E0) T)
      (bh : FdCompletedPullbackNormalization l (pbcFiniteField.{u} l Omega E0)
        h iU.out iV.out rU)
      (bk : FdCompletedPullbackNormalization l (pbcFiniteField.{u} l Omega E0)
        k iV.out iT.out rV)
      (bhk : FdCompletedPullbackNormalization l (pbcFiniteField.{u} l Omega E0)
        (h ≫ k) iU.out iT.out rU)
      (b1 : FdCompletedPullbackNormalization l (pbcFiniteField.{u} l Omega E0)
        (𝟙 T) iT.out iT.out rT)
      (ah : FdCompletedAdjunction l (pbcFiniteField.{u} l Omega E0) h)
      (ak : FdCompletedAdjunction l (pbcFiniteField.{u} l Omega E0) k)
      (ahk : FdCompletedAdjunction l (pbcFiniteField.{u} l Omega E0) (h ≫ k)),
      FdCompletedConjugate l (pbcFiniteField.{u} l Omega E0) h k ah ak ahk ∧
      ∀ K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Omega E0) T,
      ∃ hK : PbcIsIntrinsicallyComplete T (pbcStageDatum.{u} l Omega E0)
        ((integralDetailedTransport T l (pbcFiniteField.{u} l Omega E0)).obj K.obj),
        (integralDetailedTransport U l (pbcFiniteField.{u} l Omega E0)).map
            ((integralInverseImageDerivedComposition l (pbcFiniteField.{u} l Omega E0)
              h k).inv.app K.obj) ≫
            bh.ordinary.hom.app
              ((inverseImageIntegralDerived l (pbcFiniteField.{u} l Omega E0) k).obj K.obj) ≫
            (pbcActualDerivedPull h (pbcStageDatum.{u} l Omega E0)).map
              (bk.ordinary.hom.app K.obj) =
          bhk.ordinary.hom.app K.obj ≫
            (pbcActualDerivedPullCompIso h k (pbcStageDatum.{u} l Omega E0)).hom.app
              ((integralDetailedTransport T l (pbcFiniteField.{u} l Omega E0)).obj K.obj) ∧
        HEq
          ((integralDetailedTransport U l (pbcFiniteField.{u} l Omega E0)).map
            (inverseImagePullbackComparisonDerived l (pbcFiniteField.{u} l Omega E0)
              (h ≫ k) iU.out iT.out K.obj ≫
              (integralComparisonComposition l (pbcFiniteField.{u} l Omega E0) D h k K).hom))
          ((integralDetailedTransport U l (pbcFiniteField.{u} l Omega E0)).map
            ((integralInverseImageDerivedComposition l (pbcFiniteField.{u} l Omega E0)
              h k).inv.app K.obj ≫
              inverseImagePullbackComparisonDerived l (pbcFiniteField.{u} l Omega E0)
                h iU.out iV.out
                ((inverseImageIntegralDerived l (pbcFiniteField.{u} l Omega E0) k).obj
                  K.obj) ≫
              (integralDerivedPullback l (pbcFiniteField.{u} l Omega E0) h).map
                (inverseImagePullbackComparisonDerived l (pbcFiniteField.{u} l Omega E0)
                  k iV.out iT.out K.obj))) ∧
        (pbcActualCompletedPullUnit (h ≫ k) (pbcStageDatum.{u} l Omega E0)).app
            ((integralDetailedTransport T l (pbcFiniteField.{u} l Omega E0)).obj K.obj) ≫
            (pbcActualCompletedPullCompIso h k (pbcStageDatum.{u} l Omega E0)).inv.app
              ⟨_, hK⟩ =
          (pbcActualDerivedPullCompIso h k (pbcStageDatum.{u} l Omega E0)).hom.app
            ((integralDetailedTransport T l (pbcFiniteField.{u} l Omega E0)).obj K.obj) ≫
          (pbcActualCompletedPullUnit h (pbcStageDatum.{u} l Omega E0)).app
            ((pbcActualDerivedPull k (pbcStageDatum.{u} l Omega E0)).obj
              ((integralDetailedTransport T l (pbcFiniteField.{u} l Omega E0)).obj K.obj)) ≫
          (pbcActualCompletedPull h (pbcStageDatum.{u} l Omega E0)).map
            ((pbcActualCompletedPullUnit k (pbcStageDatum.{u} l Omega E0)).app
              ((integralDetailedTransport T l (pbcFiniteField.{u} l Omega E0)).obj K.obj)) ∧
        bhk.comparison.hom.app K.obj ≫
            (pbcActualCompletedPullCompIso h k (pbcStageDatum.{u} l Omega E0)).inv.app
              ⟨_, hK⟩ =
          (integralDetailedTransport U l (pbcFiniteField.{u} l Omega E0)).map
            (integralComparisonComposition l (pbcFiniteField.{u} l Omega E0) D h k K).hom ≫
          bh.comparison.hom.app
            ((integralDerivedPullback l (pbcFiniteField.{u} l Omega E0) k).obj K.obj) ≫
          (pbcActualCompletedPull h (pbcStageDatum.{u} l Omega E0)).map
            (bk.comparison.hom.app K.obj) ∧
        (integralDetailedTransport T l (pbcFiniteField.{u} l Omega E0)).map
            (inverseImagePullbackComparisonDerived l (pbcFiniteField.{u} l Omega E0)
              (𝟙 T) iT.out iT.out K.obj ≫
              (integralComparisonUnit l (pbcFiniteField.{u} l Omega E0) D T K).hom) =
          b1.ordinary.hom.app K.obj ≫
            (pbcActualDerivedPullIdIso (pbcStageDatum.{u} l Omega E0) T).hom.app
              ((integralDetailedTransport T l (pbcFiniteField.{u} l Omega E0)).obj K.obj) ∧
        (pbcActualCompletedPullUnit (𝟙 T) (pbcStageDatum.{u} l Omega E0)).app
            ((integralDetailedTransport T l (pbcFiniteField.{u} l Omega E0)).obj K.obj) ≫
            (pbcActualCompletedPullIdIso (pbcStageDatum.{u} l Omega E0) T).hom.app
              ⟨_, hK⟩ =
          (pbcActualDerivedPullIdIso (pbcStageDatum.{u} l Omega E0) T).hom.app
            ((integralDetailedTransport T l (pbcFiniteField.{u} l Omega E0)).obj K.obj) ∧
        b1.comparison.hom.app K.obj ≫
            (pbcActualCompletedPullIdIso (pbcStageDatum.{u} l Omega E0) T).hom.app
              ⟨_, hK⟩ =
          (integralDetailedTransport T l (pbcFiniteField.{u} l Omega E0)).map
            (integralComparisonUnit l (pbcFiniteField.{u} l Omega E0) D T K).hom := by
  sorry

end WeilConjectures
