/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Paper.FdCoefficientComparisonSystem
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.SfWeilSheafComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
import Sheaf.Paper.FiniteStagePairCategory
import Sheaf.Paper.PbcCommonStageCones
import WeilConjectures.Algebra.Homology.RoosComplex
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.IntegralOperationsWellDefined
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.IntegralPullbackComparisonRealization
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.IntrinsicQbarCategory
import Sheaf.Paper.PbcQbarCompletedPullback
import Sheaf.Paper.PbcRationalCategory
import Sheaf.Paper.PbcScalarExtension
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.SfScalarExtensionComposition

/-! # Canonical coefficient comparison and Frobenius pairs

Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final sentence
(blueprint: lem-fd-rational-coefficient-category-comparison).

The data use the recorded raw categories and operations. No completion of their
object sets and no arbitrary replacement comparison is introduced.

## Main definitions and statement

* `FdComparisonSchemeCoherence`: canonical identity, composition and scalar equations.
* `FdFrobeniusComparison`: finite and common-stage Weil-pair equivalences.
* `rationalCoefficientCategoryComparison`: existence of the coherent comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Avoid generating unused auxiliary lemmas for these large comparison structures.
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

open AlgebraicallyClosedCoefficients (Coefficient)

variable (l : ℕ) [Fact l.Prime]

variable (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Identity normalization and composition compatibility, with the source comparisons
fixed by the entire quotient-diagram realization. The target comparisons are the
actual unit-normalized completed PBC pullback comparisons.
Source: trace-definition final sentence, proof step 8
(blueprint: lem-fd-rational-coefficient-category-comparison). -/
def FdComparisonSchemeCoherence (S : FdCoefficientComparisonSystem.{u} l Ω) : Prop :=
  (∀ (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (E : Padic.FiniteCoefficientFields l Ω),
    ∃ su : constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) (𝟙 T) ≅ 𝟭 _,
    ∃ pu : fdPbcIntegralPull l Ω (𝟙 T) E ≅ 𝟭 _,
      (∀ K, (su.hom.app K).hom =
        (integralComparisonUnit l (pbcFiniteField.{u} l Ω E) S.realization T K).hom) ∧
      (∀ K, HEq (pu.hom.app K).hom
        ((pbcActualCompletedPullIdIso (pbcStageDatum.{u} l Ω E) T).hom.app
          ⟨K.obj, K.property.1⟩)) ∧
      (∀ K, ((S.pullback (Iso.refl T)).finite E).integral.hom.app K ≫
          ((S.coefficients T).stage E).integral.functor.map (su.hom.app K) =
        pu.hom.app (((S.coefficients T).stage E).integral.functor.obj K))) ∧
  (∀ (U V T : Scheme.{u}) [IsNoetherian U] [IsNoetherian V] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim V ≤ n)]
    [Fact (∀ t : V, IsUnit (l : V.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (h : U ≅ V) (k : V ≅ T) (E : Padic.FiniteCoefficientFields l Ω),
    ∃ sc : constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) (h.hom ≫ k.hom) ≅
        constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) k.hom ⋙
          constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) h.hom,
    ∃ pc : fdPbcIntegralPull l Ω (h.hom ≫ k.hom) E ≅
        fdPbcIntegralPull l Ω k.hom E ⋙ fdPbcIntegralPull l Ω h.hom E,
      (∀ K, (sc.hom.app K).hom =
        (integralComparisonComposition l (pbcFiniteField.{u} l Ω E) S.realization
          h.hom k.hom K).hom) ∧
      (∀ K, HEq (pc.hom.app K).hom
        ((pbcActualCompletedPullCompIso h.hom k.hom
          (pbcStageDatum.{u} l Ω E)).inv.app ⟨K.obj, K.property.1⟩)) ∧
      (∀ K, ((S.pullback (h ≪≫ k)).finite E).integral.hom.app K ≫
          ((S.coefficients U).stage E).integral.functor.map (sc.hom.app K) =
        pc.hom.app (((S.coefficients T).stage E).integral.functor.obj K) ≫
          (fdPbcIntegralPull l Ω h.hom E).map
            (((S.pullback k).finite E).integral.hom.app K) ≫
          ((S.pullback h).finite E).integral.hom.app
            ((constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) k.hom).obj K))) ∧
  (∀ {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (h : U ≅ T) (E L : Padic.FiniteCoefficientFields l Ω) (e : E ≤ L)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
    (integralPullbackScalarComparison l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e)
      h.hom K).hom.hom =
    (integralComparisonScalar l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
      (pbcFiniteFieldInclusion l Ω e)
      S.realization h.hom K).hom)

/-- Specialization to geometric Frobenius, including finite-stage and algebraically
closed fixed-pair categories and their actual intertwining morphisms.
Source: trace-definition final sentence, proof steps 10--11
(blueprint: lem-fd-rational-coefficient-category-comparison). -/
structure FdFrobeniusComparison (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (S : FdCoefficientComparisonSystem.{u} l Ω)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] where
  [noetherian : IsNoetherian (D.geometricFiber X₀).left]
  [dimension : Fact (∃ n : ℕ, topologicalKrullDim (D.geometricFiber X₀).left ≤ n)]
  [invertible : Fact (∀ x : (D.geometricFiber X₀).left,
    IsUnit (l : (D.geometricFiber X₀).left.presheaf.stalk x))]
  common : sfCommonStageWeilComplex D l hl X₀ Ω ≌
    CategoryTheory.Endofunctor.IsoAlgebra
      (pbcQbarCompletedPull l Ω (D.geometricFrobenius X₀).hom)
  common_functor : HEq common.functor
    (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
      (S.pullback (D.geometricFrobenius X₀)).pair)
  finite : ∀ E : Padic.FiniteCoefficientFields l Ω,
    sfWeilComplex D l hl X₀ (pbcFiniteField.{u} l Ω E) ≌
      CategoryTheory.Endofunctor.IsoAlgebra
        ((pbcQbarPullFamily l Ω (D.geometricFrobenius X₀).hom).Φ E)
  finite_functors : ∀ E, HEq (finite E).functor
    (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
      ((S.pullback (D.geometricFrobenius X₀)).finite E).rational)

/-- The framework and PBC rational coefficient systems agree canonically, with their
specified scalar and scheme-isomorphism transitions and their Weil fixed pairs.
Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final sentence
(blueprint: lem-fd-rational-coefficient-category-comparison).

Proof (the eleven steps of the DAG node):
1. Apply integralStratifiedPerfectDetailed to identify the two full integral categories
through integralDetailedTransport, fixed by all quotient projections. Their inherited
triangles and shifts agree by integralStratifiedPerfectClosure.
2. On the raw localized Hom groups send f tensor a to f tensor a. Balancing, addition,
identity and composition agree on pure tensors and hence on their sums. The inverse has
these same formulas. ScalarLocalization.exists_triangulated_scalarLocalization identifies
both sets of triangles with images of the common integral triangles, giving exactness.
3. For an inclusion E into L, use the generator-normalized ordinary tensor transport.
Compose with completedScalarChainComparison: its quotient coordinates are the actual
quotient maps and its shifted coordinate is zero. finiteFreeCompletedScalarComparison
makes its restriction invertible on complete objects. Rationalize its inverse to obtain j.
4. Expand both scalar associators as balanced tensor associativity conjugated by chi.
Naturality cancels adjacent chi/inverse factors. Both remaining maps send a triple tensor
to its product. Identity extensions give multiplication by one; four fields give the
same product along either route. This gives units, the cocycle, and shift compatibility.
5. At a common stage apply J and conjugate by j at source and target. The scalar cocycle
shows that this commutes with transport. It and its inverse respect eventual equality,
addition, identities and composition, so descend to inverse Hom-colimit maps.
6. Every target pair comes from its same-stage integral inverse image. Finite inclusions
are respected by the unit equation. Enlarge a representative's stage to contain a given
scalar in Omega; finite-stage linearity proves Omega-linearity. Common-stage shifts and
image triangles give exactness of the descended equivalence in both directions.
7. Use a flat-term K-flat representative P for each complete object. Both pullbacks use
one strict tower Res_n h_n^*(P tensor A_(n+1)), including its transitions. The displayed
chain's quotient-unit coordinates and zero shifted coordinate identify the identity of
that whole tower. The normalized Roos comparison and exact countable products identify
its product-cone and K-injective derived-limit realizations. Independence of resolutions
is integralOperationsWellDefined; integralOperations_preserve_constructible restricts it.
8. For identities and composites, use the simultaneous quotient diagrams and whole-system
counits of integralPullbackComparisonRealization. Both paths apply the same module
pullback composition and quotient actions, so agree before realization. Scalar change
cancels the same chi as in step 4. The normalized unit, composition and scalar equations
therefore hold on the integral categories, not merely on individual reductions.
9. Rationalize these equations on pure tensors and extend additively. The mixed scalar
square lets the comparison pass both conjugating beta factors in a common-stage arrow.
They cancel with their inverses, giving the descended natural isomorphism and coherence.
10. A finite-type geometric fibre is finite type over k, hence noetherian of finite
dimension; l is a unit because l differs from the characteristic p. Geometric Frobenius
is the displayed scheme automorphism, so step 9 applies, without k-linearity.
11. Send (K,theta) to (J K,b_K inverse followed by J theta). Naturality of b takes the
intertwining equation to the target intertwining equation. Full faithfulness lifts it
back and lifts the inverse structure map. Essential surjectivity of J then supplies all
fixed pairs. The functor is exactly IsoAlgebra.mapOfNatIso with the reverse comparison;
its underlying arrow map is J, at finite stages as well as at the common-stage level. -/
theorem rationalCoefficientCategoryComparison (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    ∃ S : FdCoefficientComparisonSystem.{u} l Ω,
      FdComparisonSchemeCoherence l Ω S ∧
      ∀ (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
        [IsSeparated X₀.hom], Nonempty (FdFrobeniusComparison l Ω D hl S X₀) := by
  sorry

end WeilConjectures
