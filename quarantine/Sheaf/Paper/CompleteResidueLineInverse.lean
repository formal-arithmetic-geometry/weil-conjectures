module

public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Noetherian

import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.AdicResidueLissePerfectLift
import Sheaf.Paper.AdicPerfectModelCompleteReduction
import WeilConjectures.RingTheory.PseudoCoherentBoundedFiniteFreeModel
import WeilConjectures.RingTheory.MinimalFreeModel
import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LineEvaluationInversePair
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
import Sheaf.Algebra.Homology.LineUnboundedDerivedTensor
import Sheaf.Paper.ProEtaleLisseOrigin
import Sheaf.Paper.IntegralLineTensorComparison
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.SixFunctors.ConstructibleTensorCompletion

/-! # A complete complex with shifted rank-one residue has a tensor inverse

Source: Bhatt--Scholze, Lemma 6.6.8, pp. 52--53, specialized to a shifted residue line;
Stacks Project, Tags 0BCC, 0B8Q, 099Y and 06YU.
(blueprint: lem-pur-complete-residue-line-inverse).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.IntegralOnSlice.abSheafify
  WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Canonical sheafification at the module universe fixed by this statement.
Source: Stacks Tag 03DA (blueprint: lem-pur-complete-residue-line-inverse). -/
instance completeResidueAbSheafify (X : Scheme.{u}) :
    HasSheafify (IntegralOnSlice.topology X none) AddCommGrpCat.{u + 1} :=
  IntegralOnSlice.abSheafify.{u, u} X none

/-- The existing locally bijective criterion at the same fixed universe.
Source: Stacks Tag 03DA (blueprint: lem-pur-complete-residue-line-inverse). -/
instance completeResidueAbLocallyBijective (X : Scheme.{u}) :
    (IntegralOnSlice.topology X none).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  IntegralOnSlice.abLocallyBijective.{u, u} X none

/-- The rank-one etale local models in the residue-line statement, with no chosen basis.
Source: Bhatt--Scholze, Lemma 6.6.8, shifted-line specialization
(blueprint: lem-pur-complete-residue-line-inverse). -/
def completeResidueEtaleLine (X : Scheme.{u}) (A : Type u) [CommRing A]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) : Prop :=
  ∃ c : X.Cover etalePrecoverage, ∀ i : c.I₀,
    Nonempty (L.over (c.etalePrecoverageToEtale i) ≅
      (constantSheaf (X.smallEtaleTopology.over (c.etalePrecoverageToEtale i))
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
          (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- The existing comparison inverse image, followed by its intrinsic scalar realization.
Index n denotes the positive exponent n+1. Source: Stacks Tags 099R and 00YV
(blueprint: lem-pur-complete-residue-line-inverse). -/
def completeResidueEtalePullback (n : ℕ) :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  ProEtale.finiteCoefficientIntrinsicComparison X (Padic.coefficientExtensionRing l E (n + 1))

/-- The completed ring as a degree-zero derived object, using the recorded unit.
Source: Bhatt--Scholze, Section 6.5
(blueprint: lem-pur-complete-residue-line-inverse). -/
abbrev completeResidueUnit : IntegralOnSlice.D.{u, u} l E X none :=
  (DerivedCategory.singleFunctor _ 0).obj
    (SheafOfModules.unit (IntegralOnSlice.rings.{u, u} l E X none))

/-- The ambient internal-Hom dual, without applying completion to Hom.
Source: Stacks Tag 08J7 (blueprint: lem-pur-complete-residue-line-inverse). -/
def completeResidueDual (M : IntegralOnSlice.D.{u, u} l E X none) :
    IntegralOnSlice.D.{u, u} l E X none :=
  (IntegralOnSlice.hom.{u, u} l E X none).obj (op M, completeResidueUnit l E X)

/-- Ordinary tensor, from the normalized K-flat ringed-site tensor-Hom model.
Source: Stacks Tag 06YU (blueprint: lem-pur-complete-residue-line-inverse). -/
def completeResidueTensor (M N : IntegralOnSlice.D.{u, u} l E X none) :
    IntegralOnSlice.D.{u, u} l E X none :=
  (IntegralOnSlice.duality.{u, u} l E X none).closed.tensor.obj (M, N)

/-- Evaluation with the dual on the left, as the recorded tensor-Hom counit.
Source: Stacks Tags 0B8Q and 08J7
(blueprint: lem-pur-complete-residue-line-inverse). -/
def completeResidueEvaluation (M : IntegralOnSlice.D.{u, u} l E X none) :
    completeResidueTensor l E X (completeResidueDual l E X M) M ⟶
      completeResidueUnit l E X :=
  (IntegralOnSlice.duality.{u, u} l E X none).closed.evaluation M (completeResidueUnit l E X)

/-- Evaluation with the dual on the right, using the same Koszul symmetry.
Source: Stacks Tags 0B8Q and 06YU
(blueprint: lem-pur-complete-residue-line-inverse). -/
def completeResidueEvaluationReverse (M : IntegralOnSlice.D.{u, u} l E X none) :
    completeResidueTensor l E X M (completeResidueDual l E X M) ⟶
      completeResidueUnit l E X :=
  ((IntegralOnSlice.duality.{u, u} l E X none).symmetric.braiding
    M (completeResidueDual l E X M)).hom ≫ completeResidueEvaluation l E X M

/-- A complete object whose residue is a shifted etale line is a shifted integral line,
with its specified two-sided evaluation inverse and uniform finite-level bounds.

Source: Bhatt--Scholze, Lemma 6.6.8, pp. 52--53, specialized to a shifted residue line
(blueprint: lem-pur-complete-residue-line-inverse).

Proof:
1. The constant/completed comparison identifies quotient-tower completeness with local
adic completeness. Apply lem-sfb-adic-residue-lisse-perfect-lift to obtain local bounded
finite-projective R-models; the residue has sole Betti number one in degree -m.
2. Use lem-sfb-adic-perfect-model-complete-reduction and the pseudo-coherent finite-free
and minimal-model lemmas: the minimal representative has only R in degree -m.
3. Define the global line as H^(-m)(M). Exact restriction detects all other cohomology
as zero. Smart truncations give M isomorphic to this line shifted by m.
4. The line-evaluation inverse-pair theorem and unbounded line-tensor theorem identify
RHom(M,B) with the dual line shifted by -m. Their evaluations, with the usual shift
and symmetry signs, are isomorphisms in both orders.
5. Reducing either flat line gives finite locally constant rank-one sheaves. The
pro-etale locally-constant origin theorem descends them to the etale site.
6. The completed perfect-model theorem makes B complete. Apply the integral line-tensor
comparison to B and each line, then commute shifts with the Roos construction, proving
completeness of M and its dual.
7. Each reduction is a shifted flat constructible line; its cohomological and Tor
bounds are [-m,-m] for M and [m,m] for its dual, independently of the level. These
are exactly finiteTorConstructibleIntegral's defining conditions. On the empty scheme
all objects vanish and the same statements and intervals apply.
8. Noetherian implies quasi-compact and quasi-separated. The constructible ordinary/
completed tensor comparison is therefore invertible in both orders and its source
is complete. Transport the specified evaluations through these comparisons to obtain
the evaluations for the specified quotient-tower completed tensor. -/
theorem completeResidueLineInverse [IsNoetherian X]
    (_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (M : IntegralOnSlice.D.{u, u} l E X none)
    (_hM : IntegralOnSlice.IsComplete.{u, u} l E X none M) (m : ℤ)
    (L : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E 1))))
    (_hL : completeResidueEtaleLine X (Padic.coefficientExtensionRing l E 1) L)
    (_hres : Nonempty ((scalarReductionDerivedExtension l E X 0).obj M ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        ((completeResidueEtalePullback l E X 0).obj L))⟦m⟧)) :
    ∃ T : IntegralOnSlice.Mod.{u, u} l E X none,
      T.IsFiniteLocallyFreeOfRank 1 ∧
      Nonempty (M ≅ ((DerivedCategory.singleFunctor _ 0).obj T)⟦m⟧) ∧
      (∀ n : ℕ, ∃ Ln : Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))),
        completeResidueEtaleLine X (Padic.coefficientExtensionRing l E (n + 1)) Ln ∧
        Nonempty ((scalarReductionExtension l E X n).obj T ≅
          (completeResidueEtalePullback l E X n).obj Ln)) ∧
      finiteTorConstructibleIntegral l E X M ∧
      finiteTorConstructibleIntegral l E X (completeResidueDual l E X M) ∧
      IsIso (completeResidueEvaluation l E X M) ∧
      IsIso (completeResidueEvaluationReverse l E X M) ∧
      (∀ n : ℕ,
        proEtaleCohomologicalSupport ((scalarReductionDerivedExtension l E X n).obj M) ⊆
          Set.Icc (-m) (-m) ∧
        HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension l E X n).obj M) (-m) (-m) ∧
        proEtaleCohomologicalSupport ((scalarReductionDerivedExtension l E X n).obj
          (completeResidueDual l E X M)) ⊆ Set.Icc m m ∧
        HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension l E X n).obj (completeResidueDual l E X M))
          m m) ∧
      IntegralOnSlice.IsComplete.{u, u} l E X none
        (completeResidueTensor l E X M (completeResidueDual l E X M)) ∧
      IntegralOnSlice.IsComplete.{u, u} l E X none
        (completeResidueTensor l E X (completeResidueDual l E X M) M) ∧
      IsIso ((IntegralOnSlice.completionUnit.{u, u} l E X none).app
        (completeResidueTensor l E X M (completeResidueDual l E X M))) ∧
      IsIso ((IntegralOnSlice.completionUnit.{u, u} l E X none).app
        (completeResidueTensor l E X (completeResidueDual l E X M) M)) ∧
      ∃ (e : (IntegralOnSlice.completedTensor.{u, u} l E X none).obj
            (M, completeResidueDual l E X M) ≅ completeResidueUnit l E X)
        (e' : (IntegralOnSlice.completedTensor.{u, u} l E X none).obj
            (completeResidueDual l E X M, M) ≅ completeResidueUnit l E X),
        (IntegralOnSlice.completionUnit.{u, u} l E X none).app
            (completeResidueTensor l E X M (completeResidueDual l E X M)) ≫ e.hom =
          completeResidueEvaluationReverse l E X M ∧
        (IntegralOnSlice.completionUnit.{u, u} l E X none).app
            (completeResidueTensor l E X (completeResidueDual l E X M) M) ≫ e'.hom =
          completeResidueEvaluation l E X M := by
  sorry

end WeilConjectures
