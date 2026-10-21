/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FdCoefficientComparison
public import Sheaf.Paper.IntegralPullbackComparisonRealization
import Sheaf.Paper.FiniteFreeConstructibleScalarTransport
import Sheaf.Paper.QuotientScalarComparisonDescent
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.Paper.CompletedScalarShift
import Sheaf.Paper.ScalarCompletionAssociator
import Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer
import Sheaf.CategoryTheory.SemilinearScalarLocalization

/-! # Coherence of the completion-inverse scalar comparisons

Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final coefficient-category sentence; extracted comparison
argument, steps 3--4 (blueprint: lem-fd-completion-inverse-scalar-coherence).

The integral and rational identities are inputs. The conclusion retains the ordinary
transport, the quotient-normalized integral lift, and its rationalized inverse.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w v u' v'

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The inverse cocycle and both four-field contractions, written in the existing
stage-system language. This is a predicate on the specified comparisons, not new scalar data.
Source: trace-definition final sentence, comparison proof steps 5 and 8
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
def FdInverseScalarCoherence
    {I : Type w} [Preorder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)]
    {D : I → Type u'} [∀ i, Category.{v'} (D i)]
    {S : StageSystem C} {P : StageSystem D} (F : S.Morphism P) : Prop :=
    (∀ {E L M : I}
    (h : E ≤ L) (k : L ≤ M)
    (K : C E),
    (F.β k).inv.app ((S.T h).obj K) ≫
      (P.T k).map ((F.β h).inv.app K) ≫
      (P.assoc h k).hom.app ((F.Φ E).obj K) =
    (F.Φ M).map
      ((S.assoc h k).hom.app K) ≫
      (F.β (h.trans k)).inv.app K) ∧
    (∀ {E L M N : I}
    (h : E ≤ L) (k : L ≤ M) (m : M ≤ N)
    (K : C E),
    ((F.β m).inv.app ((S.T k).obj
      ((S.T h).obj K)) ≫
      (P.T m).map
        ((F.β k).inv.app ((S.T h).obj K)) ≫
      (P.T m).map
        ((P.T k).map
        ((F.β h).inv.app K)) ≫
      (P.T m).map
        ((P.assoc h k).hom.app ((F.Φ E).obj K)) ≫
      (P.assoc (h.trans k) m).hom.app ((F.Φ E).obj K) =
      (F.Φ N).map
        ((S.T m).map
          ((S.assoc h k).hom.app K) ≫
          (S.assoc (h.trans k) m).hom.app K) ≫
      (F.β ((h.trans k).trans m)).inv.app K) ∧
    ((F.β m).inv.app ((S.T k).obj
      ((S.T h).obj K)) ≫
      (P.T m).map
        ((F.β k).inv.app ((S.T h).obj K)) ≫
      (P.T m).map
        ((P.T k).map
        ((F.β h).inv.app K)) ≫
      (P.assoc k m).hom.app
        ((P.T h).obj ((F.Φ E).obj K)) ≫
      (P.assoc h (k.trans m)).hom.app ((F.Φ E).obj K) =
      (F.Φ N).map
        ((S.T m).map
          ((S.assoc h k).hom.app K) ≫
          (S.assoc (h.trans k) m).hom.app K) ≫
      (F.β ((h.trans k).trans m)).inv.app K))

/-- The quotient-normalized integral comparison retained by the scalar-coherence theorem.
This records exactly the tensor transport and chi lift of the coefficient datum, without
its downstream rational or pair-category conclusions.
Source: trace-definition final sentence, comparison steps 1--3
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
structure FdCompletionIntegralComparison
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E) where
  ordinary : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      FdOrdinaryScalarTransport l Ω T h
  comparison : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι ⋙
          integralDetailedTransport T l (pbcFiniteField.{u} l Ω E) ⋙
            pbcAmbientScalarExtension l Ω T h ≅
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω T E L h ⋙
          (sfIntegralConstructible l (pbcFiniteField.{u} l Ω L) T).ι ⋙
            integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)
  chi : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (P : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E) T).FullSubcategory)
    (hP : sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T
      (DerivedCategory.Q.obj P.obj)),
    HEq ((comparison h).hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
      (integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)).map
        ((integralScalarExtensionComparison l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).hom.app P) ≫
      (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω L) T).hom.app
        ((integralScalarComplexFunctor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).obj P.obj))
      ((pbcAmbientScalarExtension l Ω T h).map
        ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) T).hom.app P.obj) ≫
      pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
        (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapHomologicalComplex
          (.up ℤ)).obj P.obj) ≫
      DerivedCategory.Q.map ((ordinary h).completion l Ω P.obj))
  integral : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      (stage E).integral.functor ⋙ pbcIntegralScalarExtension l Ω T dT.out iT.out h ≅
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω T E L h ⋙
          (stage L).integral.functor
  restriction : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
      HEq ((integral h).hom.app K).hom ((comparison h).hom.app K)

/-- Coherence data for the specified integral comparison and its rationalized inverse.
The stage-system components are identified with the supplied raw identity equivalences;
only presentation transport is expressed by heterogeneous equality.
Source: trace-definition final sentence, comparison steps 1--8
(blueprint: lem-fd-completion-inverse-scalar-coherence). -/
structure FdCompletionScalarComparison
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E) where
  integral : FdCompletionIntegralComparison l Ω T stage
  family : StageSystem.Morphism
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (pbcScalarSystem l Ω T dT.out iT.out)
  finite_functor : ∀ E, HEq (family.Φ E) (stage E).rational.functor
  [finite_shift : ∀ E, (family.Φ E).CommShift ℤ]
  finite_shift_normalization : ∀ E (n : ℤ),
    HEq ((family.Φ E).commShiftIso n) ((stage E).rational.functor.commShiftIso n)
  scalar_lift : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
    (K' : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
    HEq K' ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K) →
    HEq ((family.β h).hom.app K')
      ((pbcScalarIntegralComparison l Ω T dT.out iT.out h).hom.app
          ((stage E).integral.functor.obj K) ≫
        (pbcStageLocalization l Ω T L).map ((integral.integral h).hom.app K))
  scalar_shift : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
    NatTrans.CommShift (family.β h).hom ℤ ∧ NatTrans.CommShift (family.β h).inv ℤ
  exact : ∀ E, (family.Φ E).IsTriangulated
  unit : ∀ (E : Padic.FiniteCoefficientFields l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
    HEq ((family.β (le_refl E)).inv.app K)
      ((family.Φ E).map
        ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω T E).hom.app K))
  coherence : FdInverseScalarCoherence family

/-- The specified completion map restricts to an integral isomorphism, and its inverse
rationalizes to an exact scalar comparison satisfying shifts, units, the cocycle and
four-field compatibility, including repeated fields.
Source: blueprint main-20261015, trace-definition final sentence, expanded comparison
argument (blueprint: lem-fd-completion-inverse-scalar-coherence).

Proof, following the eight steps of the DAG node:
1. The stratified-perfect characterization identifies the integral categories after the
quotient-normalized coefficient transport. Finite-free scalar transport preserves them.
Completeness makes the specified ambient chi invertible, so it and its inverse restrict.
2. On a flat-term K-flat representative the ordinary transport fixes every tensor
factor. Chi has the actual quotient coordinates and zero shifted-product coordinate.
Quotient-scalar descent makes this normalization independent of the representative;
its countable-product exactness hypothesis holds on the small pro-etale site.
3. Ordinary derived tensor is exact. The cone shift comparison is (x,y) ↦ (x,(-1)^m y);
it fixes (c(z),0). Thus chi and its inverse commute with the specified shifts, and the
completed restriction is exact for those shifts and the inherited triangles.
4. The scalar-completion associator equation identifies the completed associator with
ordinary tensor balancing conjugated by these same chi maps. This is precisely the
normalization of the integral pullback realization and the chosen framework associator.
5. Naturality of chi moves its inner component across the outer scalar functor.
Multiplying by the inverse comparison on both sides and cancelling gives the inverse
cocycle with the stated arrow directions.
6. For equal fields ordinary multiplication identifies the tensor unit and chi is the
completeness unit. Its inverse is the normalized unit. The two associator unit equations
therefore give both comparison unit squares, also when all fields coincide.
7. Raw semilinear scalar localization sends these maps and their inverses to the
specified rational comparisons: the source uniformizer is invertible in the final
field. It preserves composition, whiskering, shifts and the integral-lift equation.
The identity raw equivalences preserve each scalar and integral tensor factor.
8. For four nested fields expand the three successive inverse comparisons. Twice use
the cocycle and naturality; the two contractions become j_30 followed by J_3 of the
two framework associator composites. The framework pentagon equates them, and the
PBC pentagon identifies the corresponding contractions on that side. Unit substitutions
cover every repeated-field degeneracy. -/
theorem fdCompletionInverseScalarCoherence
    (_D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ _D.p)
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E) :
    Nonempty (FdCompletionScalarComparison l Ω T stage) := by
  sorry

end WeilConjectures
