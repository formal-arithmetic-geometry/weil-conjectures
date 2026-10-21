/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Sheaf.AlgebraicGeometry.FiniteOpenClosedRecollement
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian

import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlat
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.Paper.PbcRationalTransport
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.PbcScalarExtension
import Sheaf.Paper.PbcDescentFunctors
import Sheaf.Paper.PbcVerdierAxioms
import Sheaf.AlgebraicGeometry.FrobeniusDetailed
import Sheaf.CategoryTheory.MateIsoAlongEquivalences
import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.Paper.SfCommonStageDirectImage
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# The canonical open-closed triangle at all coefficient stages

Source: Weil blueprint, sec-smooth-purity, prop-sf-open-closed-triangle-all-stages,
order 1851 (current main: order 2195)
(blueprint: prop-sf-open-closed-triangle-all-stages).

The integral presentation uses the actual closed inverse-image/direct-image unit.
Its kernel is the open term, with its kernel inclusion as counit. This fixes the
maps before passage to complexes, completion, scalar localization, or common stages.

## Main statements

* `sfOpenClosedTriangle_finite`: canonical finite-coefficient triangle and uniqueness.
* `sfOpenClosedTriangle_integral_rational`: normalized integral and rational triangles.
* `sfOpenClosedTriangle_qbar`: the common-stage triangle.
* `sfOpenClosedTriangle_rational_weil`, `sfOpenClosedTriangle_qbar_weil`: all three
  arrows are equivariant for the recorded fixed-pair Weil structures.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u v w w₁
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical inverse-image coefficient map, adjoint to the completed structural
map. Source: blueprint proof step 3; Stacks 098T
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfRecollementCoefficientMap {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm
    (sfCompletedCoefficientMap l E f)

/-- The actual completed coefficient comparison is invertible.
Source: blueprint proof step 3; Stacks 098T
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: the normalized structural map has precisely the constant finite quotient
coordinates. Profinite coefficient inverse image identifies its adjunct with the
canonical limit comparison, which is an isomorphism. -/
@[instance] theorem sfRecollementCoefficientMap_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (sfRecollementCoefficientMap l E f) := by
  sorry

/-- The normalized ordinary integral module adjunction.
Source: blueprint proof steps 3 and 7; Stacks 03D2, 07A6
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfRecollementModuleAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleRingModuleAdjunction f (completedIntegralCommRingSheafUnrestricted l E Y)
    (completedIntegralCommRingSheafUnrestricted l E X)
    (asIso (sfRecollementCoefficientMap l E f))

/-- The closed term on module sheaves, before taking its derived functor.
Source: blueprint proof step 7; Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfRecollementModuleClosed {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  proEtaleRingModulePullback i (completedIntegralCommRingSheafUnrestricted l E X)
      (completedIntegralCommRingSheafUnrestricted l E Z)
      (asIso (sfRecollementCoefficientMap l E i)) ⋙
    proEtaleRingModuleDirectImage i (completedIntegralCommRingSheafUnrestricted l E X)
      (completedIntegralCommRingSheafUnrestricted l E Z)
      (asIso (sfRecollementCoefficientMap l E i))

/-- The closed unit, on actual completed-coefficient module sheaves.
Source: blueprint proof step 7; Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfRecollementModuleUnit {Z X : Scheme.{u}} (i : Z ⟶ X) :
    𝟭 (scalarReductionSource.{u, u} l E X) ⟶ sfRecollementModuleClosed l E i :=
  (sfRecollementModuleAdjunction l E i).unit

/-- The open term is the kernel of the closed unit. The ringed localization sequence
identifies this exact kernel, with its inclusion, with j!j* and its counit.
Source: blueprint proof steps 1 and 7; Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfRecollementModuleOpen {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  kernel (sfRecollementModuleUnit l E i)

/-- The specified open counit in the kernel presentation.
Source: blueprint proof step 7; Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfRecollementModuleCounit {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  kernel.ι (sfRecollementModuleUnit l E i)

/-- Exactness and additivity of both localization terms.
Source: blueprint proof steps 1, 3--7; Stacks 09AH, 09BM
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: profinite coefficients identify ordinary inverse image with restriction.
Ringed open-closed localization identifies the kernel term with open extension of
restriction and the closed term with closed direct image of restriction. All four
module functors are exact and additive; these properties pass to their composites
and across the kernel identification. -/
theorem sfRecollementModule_exact {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] :
    (sfRecollementModuleOpen l E i).Additive ∧
    PreservesFiniteLimits (sfRecollementModuleOpen l E i) ∧
    PreservesFiniteColimits (sfRecollementModuleOpen l E i) ∧
    (sfRecollementModuleClosed l E i).Additive ∧
    PreservesFiniteLimits (sfRecollementModuleClosed l E i) ∧
    PreservesFiniteColimits (sfRecollementModuleClosed l E i) := by
  sorry

/-- Exact open functor's additive structure. Source: Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
instance sfRecollementModuleOpen_additive {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] : (sfRecollementModuleOpen l E i).Additive :=
  (sfRecollementModule_exact l E i).1

/-- Exact open functor's left exactness. Source: Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
instance sfRecollementModuleOpen_limits {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] :
    PreservesFiniteLimits (sfRecollementModuleOpen l E i) :=
  (sfRecollementModule_exact l E i).2.1

/-- Exact open functor's right exactness. Source: Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
instance sfRecollementModuleOpen_colimits {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] :
    PreservesFiniteColimits (sfRecollementModuleOpen l E i) :=
  (sfRecollementModule_exact l E i).2.2.1

/-- Exact closed functor's additive structure. Source: Stacks 09BM
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
instance sfRecollementModuleClosed_additive {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] : (sfRecollementModuleClosed l E i).Additive :=
  (sfRecollementModule_exact l E i).2.2.2.1

/-- Exact closed functor's left exactness. Source: Stacks 09BM
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
instance sfRecollementModuleClosed_limits {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] :
    PreservesFiniteLimits (sfRecollementModuleClosed l E i) :=
  (sfRecollementModule_exact l E i).2.2.2.2.1

/-- Exact closed functor's right exactness. Source: Stacks 09BM
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
instance sfRecollementModuleClosed_colimits {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] :
    PreservesFiniteColimits (sfRecollementModuleClosed l E i) :=
  (sfRecollementModule_exact l E i).2.2.2.2.2

/-- The two functorial vertices and the prescribed first two arrows of a recollement
triangle. This is only presentation data, without an existence or vanishing assertion.
Source: blueprint displayed open-closed triangle
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
structure SfRecollementPresentation (C : Type w) [Category.{w₁} C] where
  openTerm : C ⥤ C
  closedTerm : C ⥤ C
  counit : openTerm ⟶ 𝟭 C
  unit : 𝟭 C ⟶ closedTerm

/-- Distinguished completion, all integer-shift Hom vanishing, uniqueness of the third
arrow, and its naturality for every morphism. Source: blueprint statement, order 1851
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfRecollementConclusion {C : Type w} [Category.{w₁} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [shiftAdditive : ∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (P : SfRecollementPresentation C) : Prop :=
  (∀ K : C, ∃! δ : P.closedTerm.obj K ⟶ (P.openTerm.obj K)⟦(1 : ℤ)⟧,
    Triangle.mk (P.counit.app K) (P.unit.app K) δ ∈ distTriang C) ∧
  (∀ (K : C) (m : ℤ), Subsingleton ((P.openTerm.obj K)⟦m⟧ ⟶ P.closedTerm.obj K)) ∧
  ∀ (K L : C) (f : K ⟶ L)
    (δ : P.closedTerm.obj K ⟶ (P.openTerm.obj K)⟦(1 : ℤ)⟧)
    (δ' : P.closedTerm.obj L ⟶ (P.openTerm.obj L)⟦(1 : ℤ)⟧),
    Triangle.mk (P.counit.app K) (P.unit.app K) δ ∈ distTriang C →
    Triangle.mk (P.counit.app L) (P.unit.app L) δ' ∈ distTriang C →
    P.closedTerm.map f ≫ δ' = δ ≫ (shiftFunctor C (1 : ℤ)).map (P.openTerm.map f)

/-- The finite presentation uses precisely the dependency's two adjunction maps.
Source: blueprint finite-stage paragraph; Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfFiniteRecollementPresentation {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A] :
    SfRecollementPresentation (proEtaleDerivedCategory X A) where
  openTerm := sfIntrinsicDerivedPullback A j ⋙ sfIntrinsicDerivedOpen A j
  closedTerm := sfIntrinsicDerivedPullback A i ⋙ proEtaleConstantDerivedDirectImage i A
  counit := (exceptionalOpenAdjunction j A).counit
  unit := (finiteRecollementDerivedAdjunction i A).unit

/-- The conclusion on a full constructible subcategory of an ambient derived category.
Distinguishedness is tested in the ambient category, as in the recorded finite
recollement definition; the outer vertices are required to remain constructible.
Source: blueprint statement (blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfRecollementConclusionOn {C : Type w} [Category.{w₁} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (P : SfRecollementPresentation C) (S : ObjectProperty C) : Prop :=
  (∀ (K : C), S K → S (P.openTerm.obj K) ∧ S (P.closedTerm.obj K) ∧
    (∃! δ : P.closedTerm.obj K ⟶ (P.openTerm.obj K)⟦(1 : ℤ)⟧,
      Triangle.mk (P.counit.app K) (P.unit.app K) δ ∈ distTriang C) ∧
    ∀ m : ℤ, Subsingleton ((P.openTerm.obj K)⟦m⟧ ⟶ P.closedTerm.obj K)) ∧
  ∀ (K L : C), S K → S L → ∀ (f : K ⟶ L)
    (δ : P.closedTerm.obj K ⟶ (P.openTerm.obj K)⟦(1 : ℤ)⟧)
    (δ' : P.closedTerm.obj L ⟶ (P.openTerm.obj L)⟦(1 : ℤ)⟧),
    Triangle.mk (P.counit.app K) (P.unit.app K) δ ∈ distTriang C →
    Triangle.mk (P.counit.app L) (P.unit.app L) δ' ∈ distTriang C →
    P.closedTerm.map f ≫ δ' = δ ≫ (shiftFunctor C (1 : ℤ)).map (P.openTerm.map f)

/-- Positive-level specialization with the recorded finiteness proof supplied
internally, so finiteness is not an extra theorem hypothesis.
Source: blueprint finite-stage paragraph
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfFiniteRecollementAt {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] (n : ℕ) (hn : 1 ≤ n) :
    SfRecollementPresentation (proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  sfFiniteRecollementPresentation i j (Padic.coefficientExtensionRing l E n)

/-- At positive finite coefficients the specified maps have unique distinguished
completion; the vertices remain constructible, Hom vanishing includes every integer
shift, and the triangle is natural. Source: blueprint proof steps 1--2, 8--9; Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: X is Noetherian, so the complementary open is quasi-compact. Finite locally
closed partitions restrict to U,Z and extend by zero to X. The exact ringed sheaf
sequence applied termwise gives the distinguished triangle by the complex short-exact
sequence triangle lemma. Exact functors give the stated derived operations and maps.
The open adjunction and j*i*=0 give Hom(j!N[m],i*M)=0 for arbitrary N,M. TR3 compares
completions; Hom exactness factors the difference of third components through a map
j!N[1] to i*M, which vanishes. The same argument for a map K to L proves naturality. -/
theorem sfOpenClosedTriangle_finite
    (k : Type u) [Field k] (_hk : IsUnit (l : k))
    {Z U X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    (_hij : Set.range j.base = (Set.range i.base)ᶜ)
    (n : ℕ) (hn : 1 ≤ n) :
    SfRecollementConclusionOn
      (sfFiniteRecollementAt l E i j n hn)
      (intrinsicFiniteTorsionConstructible l E n hn X) := by
  sorry

/-- The Noetherian structure supplied by the finite-type structure map over a field.
Source: blueprint proof step 1; Stacks 01T6
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: a field is Noetherian; the structure morphism is locally of finite type,
so its source is locally Noetherian. Quasi-compactness over the compact spectrum
of the field makes the source compact, giving the Noetherian structure. -/
theorem sfRecollementNoetherian (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] :
    IsNoetherian X := by
  sorry

/-- The open complement has its inherited finite-type structure over k and is a
quasi-compact open immersion. Source: blueprint proof step 1; Stacks 01T6
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: X is Noetherian by finite type over the field. Every open subset of each
Noetherian affine is quasi-compact and a finite union of principal opens. Their
coordinate rings are finitely generated by adjoining inverses. These covers give
finite type over k; Noetherian quasi-compactness also gives quasi-compactness of j. -/
theorem sfRecollementOpenFiniteType (k : Type u) [Field k]
    {U X : Scheme.{u}} [X.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))] :
    LocallyOfFiniteType (U ↘ Spec (.of k)) ∧
      QuasiCompact (U ↘ Spec (.of k)) ∧ QuasiCompact j := by
  sorry

/-- A normalized integral presentation uses the exact sheaf kernel and closed term,
with their actual sheaf maps on every representative complex. This pins down the
arrows, not just the isomorphism classes of the three vertices.
Source: blueprint proof steps 3--7 (blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfIntegralRecollementNormalization {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (hX : IsNoetherian X)
    (P : SfRecollementPresentation (sfIntegralConstructibleCategory l E X)) : Prop :=
  letI := hX
  ∃ (a : (sfIntegralConstructible l E X).ι ⋙
        (sfRecollementModuleOpen l E i).mapDerivedCategory ≅
      P.openTerm ⋙ (sfIntegralConstructible l E X).ι)
    (c : (sfIntegralConstructible l E X).ι ⋙
        (sfRecollementModuleClosed l E i).mapDerivedCategory ≅
      P.closedTerm ⋙ (sfIntegralConstructible l E X).ι),
    ∀ (B : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ)
      (hB : sfIntegralConstructible l E X (DerivedCategory.Q.obj B)),
      a.hom.app ⟨DerivedCategory.Q.obj B, hB⟩ ≫
          (P.counit.app ⟨DerivedCategory.Q.obj B, hB⟩).hom =
        (sfRecollementModuleOpen l E i).mapDerivedCategoryFactors.hom.app B ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (F := sfRecollementModuleOpen l E i)
              (G := 𝟭 (scalarReductionSource.{u, u} l E X))
              (sfRecollementModuleCounit l E i) (.up ℤ)).app B) ∧
      (P.unit.app ⟨DerivedCategory.Q.obj B, hB⟩).hom ≫
          c.inv.app ⟨DerivedCategory.Q.obj B, hB⟩ ≫
          (sfRecollementModuleClosed l E i).mapDerivedCategoryFactors.hom.app B =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (F := 𝟭 (scalarReductionSource.{u, u} l E X))
            (G := sfRecollementModuleClosed l E i)
            (sfRecollementModuleUnit l E i) (.up ℤ)).app B)

/-- Rational presentations are obtained from exactly the integral functors and maps
by the recorded raw localization. The two comparison squares retain the prescribed
counit and unit. Source: blueprint proof step 10
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfRationalRecollementNormalization (X : Scheme.{u})
    (P : SfRecollementPresentation (sfIntegralConstructibleCategory l E X))
    (Q : SfRecollementPresentation (sfRationalConstructibleCategory l E X)) : Prop :=
  (∀ K, Q.openTerm.obj K = ⟨P.openTerm.obj K.obj⟩ ∧
    Q.closedTerm.obj K = ⟨P.closedTerm.obj K.obj⟩) ∧
  ∃ (a : sfRationalConstructibleLocalization l E X ⋙ Q.openTerm ≅
      P.openTerm ⋙ sfRationalConstructibleLocalization l E X)
    (c : sfRationalConstructibleLocalization l E X ⋙ Q.closedTerm ≅
      P.closedTerm ⋙ sfRationalConstructibleLocalization l E X),
    (∀ K, a.hom.app K ≫
        (sfRationalConstructibleLocalization l E X).map (P.counit.app K) =
      Q.counit.app ((sfRationalConstructibleLocalization l E X).obj K)) ∧
    ∀ K, Q.unit.app ((sfRationalConstructibleLocalization l E X).obj K) ≫ c.hom.app K =
      (sfRationalConstructibleLocalization l E X).map (P.unit.app K)

/-- Identification of the integral kernel presentation with the recorded completed
operations. Constructibility of the restricted pullback is included in the witness.
The closed term is the recorded integral direct image of the completed pullback: a
vertex of the specified Roos triangle of the finite-image tower, R lim Res_n Ri_{*,n}.
Exact countable products supply the derived-category products of that tower.
Source: blueprint proof steps 3--7
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfIntegralRecollementVertices
    (k : Type u) [Field k] (hk : IsUnit (l : k))
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))]
    (P : SfRecollementPresentation (sfIntegralConstructibleCategory l E X)) : Prop :=
  letI : LocallyOfFiniteType (U ↘ Spec (.of k)) := (sfRecollementOpenFiniteType k j).1
  letI : QuasiCompact (U ↘ Spec (.of k)) := (sfRecollementOpenFiniteType k j).2.1
  letI : QuasiCompact j := (sfRecollementOpenFiniteType k j).2.2
  (∀ K : sfIntegralConstructibleCategory l E X,
    ∃ h : sfIntegralConstructible l E U ((integralDerivedPullback l E j).obj K.obj),
      Nonempty (P.openTerm.obj K ≅ sfIntegralCompactSupportValue l E k hk
        (Compactification.ofIsOpenImmersion j) ⟨_, h⟩)) ∧
  letI : HasCountableProducts (DerivedCategory (scalarReductionSource.{u, u} l E X)) :=
    integralOperationsDerivedCountableProducts l E X
  ∀ K : sfIntegralConstructibleCategory l E X,
    ∃ L : SfIntegralDirectImage l E i ((integralDerivedPullback l E i).obj K.obj),
      Nonempty ((P.closedTerm.obj K).obj ≅ L.obj)

/-- Integral and rational localization triangles, with their actual operation vertices
and specified maps. The Noetherian and induced finite-type hypotheses here are the
properties inherited by the three schemes in the statement.
Source: blueprint proof steps 3--10
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: identify immersion inverse images of completed coefficients with the actual
coefficient sheaves. Exact immersion restriction preserves countable products, hence
Roos triangles, and is the completed pullback. Open extension is the kernel of the
map j* to i*i*j*, so preserves products too. The slice tensor identity on K-flat
complexes identifies its reductions with finite extension, compatibly with transitions.
It is therefore complete with constructible reductions in one common interval, and
is the specified compact-support value. Closed exact direct image commutes with the
reduction tower and has the specified finite reductions. The termwise ringed sheaf
sequence gives the integral triangle in the full triangulated subcategory. The open
adjunction and disjoint support give cross-object vanishing. TR3 and Hom exactness
prove uniqueness and naturality as at finite coefficients. Localize the integral
linear functors and maps: localization is exact, and Hom groups tensor with E, so
vanishing persists. Apply the same TR3 argument to arbitrary rational morphisms. -/
theorem sfOpenClosedTriangle_integral_rational
    (k : Type u) [Field k] (hk : IsUnit (l : k))
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))]
    (_hij : Set.range j.base = (Set.range i.base)ᶜ) :
    ∃ (P : SfRecollementPresentation (sfIntegralConstructibleCategory l E X))
      (Q : SfRecollementPresentation (sfRationalConstructibleCategory l E X)),
      SfIntegralRecollementNormalization l E i (sfRecollementNoetherian k X) P ∧
      SfIntegralRecollementVertices l E k hk i j P ∧
      SfRecollementConclusion P ∧
      SfRationalRecollementNormalization l E X P Q ∧ SfRecollementConclusion Q := by
  sorry

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The common-stage presentation is the descent of the actual rational presentations.
Naturality covers every common-stage representative, rather than only maps from one
fixed coefficient field. The comparison squares specify the descended counit and unit.
Source: blueprint proof step 11
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfCommonStageRecollementNormalization (X : Scheme.{u})
    (Q : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
      SfRecollementPresentation (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X L))
    (R : SfRecollementPresentation (generalAlgebraicallyClosedConstructibleCategory l Ω X)) :
    Prop :=
  (∀ K, R.openTerm.obj K = ⟨K.stage, (Q K.stage).openTerm.obj K.obj⟩ ∧
    R.closedTerm.obj K = ⟨K.stage, (Q K.stage).closedTerm.obj K.obj⟩) ∧
  ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
    ∃ (a : GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) L ⋙
          R.openTerm ≅ (Q L).openTerm ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion L)
      (c : GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) L ⋙
          R.closedTerm ≅ (Q L).closedTerm ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion L),
      (∀ K, a.hom.app K ≫ (GeneralAlgebraicallyClosedCoefficients.inclusion L).map
          ((Q L).counit.app K) =
        R.counit.app ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K)) ∧
      ∀ K, R.unit.app ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K) ≫
          c.hom.app K = (GeneralAlgebraicallyClosedCoefficients.inclusion L).map ((Q L).unit.app K)

/-- The algebraically closed coefficient localization triangle, with all finite-stage
operations retained through the recorded common-stage inclusions.
Source: blueprint proof step 11
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: apply the integral/rational construction at every finite coefficient field.
Tensor balancing and scalar-extension compatibility identify the counit and unit
across each field inclusion. Descend the exact functors and these transformations.
An object and each finite diagram of morphisms have a common coefficient stage.
Exactness of the stage inclusions carries the rational triangle to the common-stage
category. The Hom groups are filtered colimits of the vanishing stage groups.
TR3 and Hom exactness prove uniqueness and naturality for every common-stage map. -/
theorem sfOpenClosedTriangle_qbar
    (k : Type u) [Field k] (hk : IsUnit (l : k))
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))]
    (_hij : Set.range j.base = (Set.range i.base)ᶜ) :
    ∃ (P : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
        SfRecollementPresentation (sfIntegralConstructibleCategory l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X))
      (Q : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
        SfRecollementPresentation (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X L)),
      (∀ L, SfIntegralRecollementNormalization l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) i
          (sfRecollementNoetherian k X) (P L) ∧
        SfIntegralRecollementVertices l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) k hk i j (P L) ∧
        SfRecollementConclusion (shiftAdditive := fun n => inferInstance) (P L) ∧
        SfRationalRecollementNormalization l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X (P L) (Q L) ∧
        SfRecollementConclusion (Q L)) ∧
      ∃ R : SfRecollementPresentation (generalAlgebraicallyClosedConstructibleCategory l Ω X),
        SfCommonStageRecollementNormalization l Ω X Q R ∧ SfRecollementConclusion R := by
  sorry

/-- Exactness for the shift structure on the specified geometric Frobenius functor.
The shift structure is included as data because its interface was not previously
exported by the recorded pullback module. Source: blueprint proof steps 12 and 16
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfRecollementFrobeniusExact
    {C : Type w} [Category.{w₁} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (G : C ⥤ C) (s : G.CommShift ℤ) : Prop :=
  letI := s
  G.IsTriangulated

/-- All three arrows are morphisms of the recorded fixed pairs. The outer Weil
isomorphisms are uniquely characterized by the first two commuting squares; the third
uses the induced shift of the open Weil structure.
Source: blueprint statement and proof steps 12--16
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfRecollementWeilEquivariant
    {C : Type w} [Category.{w₁} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : SfRecollementPresentation C) (G : C ⥤ C) (s : G.CommShift ℤ) : Prop :=
  letI := s
  ∀ K : CategoryTheory.Endofunctor.IsoAlgebra G,
    ∃! ac : (G.obj (P.openTerm.obj K.carrier) ≅ P.openTerm.obj K.carrier) ×
        (G.obj (P.closedTerm.obj K.carrier) ≅ P.closedTerm.obj K.carrier),
      (G.map (P.counit.app K.carrier) ≫ K.str.hom =
        ac.1.hom ≫ P.counit.app K.carrier) ∧
      (G.map (P.unit.app K.carrier) ≫ ac.2.hom =
        K.str.hom ≫ P.unit.app K.carrier) ∧
      ∀ δ : P.closedTerm.obj K.carrier ⟶ (P.openTerm.obj K.carrier)⟦(1 : ℤ)⟧,
        Triangle.mk (P.counit.app K.carrier) (P.unit.app K.carrier) δ ∈ distTriang C →
        G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app (P.openTerm.obj K.carrier) ≫
            (shiftFunctor C (1 : ℤ)).map ac.1.hom = ac.2.hom ≫ δ

/-- Finite-type geometric fibres inherit the Noetherian structure used by the
integral presentation. Source: blueprint proof steps 1 and 12; Stacks 01T6
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: finite type is stable under the base change defining the geometric fibre;
a finite-type scheme over the closure field is Noetherian. -/
theorem sfRecollementGeometricNoetherian (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    IsNoetherian (D.geometricFiber X₀).left := by
  sorry

/-- Weil equivariance at a rational coefficient stage, for the prescribed open and
closed terms and every connecting arrow supplied by the localization triangle.
The geometric map is the actual base change of the closed immersion over k₀;
no k-linearity hypothesis is imposed on the semilinear geometric Frobenius.
Source: blueprint proof steps 12--16
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: geometric Frobenius is semilinear on the closure and commutes with the
base-changed closed immersion and its open complement. The inverse automorphism
squares give inverse pullback, closed-image and open-extension comparisons. Their
mates are isomorphisms. The tensor-unit normalizations identify the ordinary maps
with the specified completed maps, and mate pasting makes the counit and unit
squares commute. Combine these comparisons with the middle Weil isomorphism to
obtain the two outer Weil isomorphisms. Pullback of the distinguished triangle is
distinguished. The two squares identify its first two arrows with the original
ones, so uniqueness forces its connecting arrow to be the original one. Shifted
Hom vanishing gives uniqueness of the outer structures with those squares. -/
theorem sfOpenClosedTriangle_rational_weil
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X₀ Z₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (i₀ : Z₀ ⟶ X₀) [IsClosedImmersion i₀.left]
    (i : (D.geometricFiber Z₀).left ⟶ (D.geometricFiber X₀).left)
    [IsClosedImmersion i]
    (_hi : i = ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map i₀).left)
    (P : SfRecollementPresentation
      (sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left))
    (Q : SfRecollementPresentation
      (sfRationalConstructibleCategory l E (D.geometricFiber X₀).left))
    (_hP : SfIntegralRecollementNormalization l E i (sfRecollementGeometricNoetherian D X₀) P)
    (_hQ : SfRationalRecollementNormalization l E (D.geometricFiber X₀).left P Q) :
    ∃ s : (sfWeilFrobeniusPullback D l hl X₀ E).CommShift ℤ,
      SfRecollementFrobeniusExact (sfWeilFrobeniusPullback D l hl X₀ E) s ∧
      SfRecollementWeilEquivariant Q (sfWeilFrobeniusPullback D l hl X₀ E) s := by
  sorry

/-- Weil equivariance after common-stage descent. This uses precisely the recorded
algebraically closed Weil category of fixed pairs, not a derived category of pairs.
Source: blueprint proof steps 11--16
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: the Frobenius comparisons and their mate unit/counit equations commute with
finite scalar extension. Descend them to common stages, where geometric Frobenius
is the recorded common-stage pullback. Each finite diagram, including the Weil
isomorphism, has a common coefficient stage; its inverse is represented after a
further extension. The rational argument gives the outer Weil structures and the
first two commuting squares there. Exact stage inclusion transports the triangle.
Uniqueness of its third arrow gives the final equivariance equation independently
of the representing stage. Shifted Hom vanishing gives uniqueness of the outer
structures characterized by the first two squares. -/
theorem sfOpenClosedTriangle_qbar_weil
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X₀ Z₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (i₀ : Z₀ ⟶ X₀) [IsClosedImmersion i₀.left]
    (i : (D.geometricFiber Z₀).left ⟶ (D.geometricFiber X₀).left)
    [IsClosedImmersion i]
    (_hi : i = ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map i₀).left)
    (P : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
      SfRecollementPresentation (sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (D.geometricFiber X₀).left))
    (Q : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
      SfRecollementPresentation
        (GeneralAlgebraicallyClosedCoefficients.Stage l Ω (D.geometricFiber X₀).left L))
    (_hPQ : ∀ L, SfIntegralRecollementNormalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) i
        (sfRecollementGeometricNoetherian D X₀) (P L) ∧
      SfRationalRecollementNormalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
        (D.geometricFiber X₀).left (P L) (Q L))
    (R : SfRecollementPresentation
      (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left))
    (_hR : SfCommonStageRecollementNormalization l Ω (D.geometricFiber X₀).left Q R) :
    ∃ s : (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).CommShift ℤ,
      SfRecollementFrobeniusExact (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω) s ∧
      SfRecollementWeilEquivariant R (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω) s := by
  sorry

end WeilConjectures
