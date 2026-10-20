/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients

import Sheaf.Paper.SmoothPurityCoefficientTowers
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Algebra.Homology.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.SequentialTowerEvaluationFull
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Sheaf.AlgebraicGeometry.ProEtaleReplete
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Reconstruction of a normalized smooth-purity coefficient tower

Source: blueprint main-20261015, sec-smooth-purity,
`sk-lem-sp-tower/_section.md`; Stacks Project, Tags 0940 and 099P
(blueprint: sk-lem-sp-tower).

The natural index n denotes positive exponent n+1. A Roos triangle specifies the
actual derived inverse limit and its projections. The comparison at each finite level
is the tensor-restriction adjoint of that projection, in the finite-coefficient category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The small pro-etale site fits in the actual coefficient universe.
Source: blueprint, coefficient setup (blueprint: sk-lem-sp-tower). -/
instance (priority := 4000) spReconstructionSiteSmall : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The canonical completed-coefficient projection to the ell-power quotient.
The comparison is uniquely fixed on constant scalars by the coefficient-tower node.
Source: blueprint, coefficient setup (blueprint: sk-lem-sp-tower). -/
def spCompletedEllProjection (n : ℕ) :
    WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E T ⟶
      spCoefficientRing l E T n :=
  (sp_completed_coefficient_limit l E T).exists.choose.hom ≫
    limit.π (spCoefficientRings l E T) (op n)

/-- The same projection retaining the existing commutative ring structures.
Source: blueprint, coefficient setup (blueprint: sk-lem-sp-tower). -/
def spCompletedEllCommProjection (n : ℕ) :
    WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T ⟶
      (spCoefficientCommRings l E T).obj (op n) :=
  (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).preimage
      (spCompletedEllProjection l E T n)

/-- Exact restriction from the actual ell-power quotient to completed coefficients.
Source: blueprint, restriction in proof step 2 (blueprint: sk-lem-sp-tower). -/
abbrev spCompletedEllRestriction (n : ℕ) :=
  restrictScalars.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (spCompletedEllCommProjection l E T n))

variable (D : SpCoefficientTowersAbelian l E T)

/-- The given tower's level as a module over the completed ring, without changing its
underlying sheaf or transition. Source: blueprint, proof step 2
(blueprint: sk-lem-sp-tower). -/
def spCompletedEvaluation (n : ℕ) : spCoefficientTowers l E T ⥤
    WeilConjectures.scalarReductionSource.{u, u} l E T :=
  spCoefficientEvaluation l E T D.equivalence n ⋙ spCompletedEllRestriction l E T n

/-- Exactness is inherited from exact level evaluation and scalar restriction.
Source: blueprint, proof step 2 (blueprint: sk-lem-sp-tower).
Proof: addition and kernels are componentwise. Sheafified cokernels are unchanged by
restriction of the scalar action. Compose with the exact evaluation supplied by D. -/
theorem spCompletedEvaluation_exact (n : ℕ) :
    (spCompletedEvaluation l E T D n).Additive ∧
      PreservesFiniteLimits (spCompletedEvaluation l E T D n) ∧
      PreservesFiniteColimits (spCompletedEvaluation l E T D n) := by
  sorry

/-- Additivity of the actual completed-coefficient evaluation.
Source: blueprint, proof step 2 (blueprint: sk-lem-sp-tower). -/
instance spCompletedEvaluationAdditive (n : ℕ) :
    (spCompletedEvaluation l E T D n).Additive :=
  (spCompletedEvaluation_exact l E T D n).1

/-- Preservation of finite limits by the actual evaluation.
Source: blueprint, proof step 2 (blueprint: sk-lem-sp-tower). -/
instance spCompletedEvaluationLimits (n : ℕ) :
    PreservesFiniteLimits (spCompletedEvaluation l E T D n) :=
  (spCompletedEvaluation_exact l E T D n).2.1

/-- Preservation of finite colimits by the actual evaluation.
Source: blueprint, proof step 2 (blueprint: sk-lem-sp-tower). -/
instance spCompletedEvaluationColimits (n : ℕ) :
    PreservesFiniteColimits (spCompletedEvaluation l E T D n) :=
  (spCompletedEvaluation_exact l E T D n).2.2

/-- The unique ordinary transition, fixed on every section by the original strict
semilinear tower. Source: blueprint, proof step 2 (blueprint: sk-lem-sp-tower).
Proof: the completed projections commute with quotient transitions by the limit-cone
condition. Thus the original semilinear transition becomes completed-ring linear.
It commutes with sheaf restrictions and tower morphisms. Equality on all sections
determines each component uniquely. -/
theorem spCompletedTransition_existsUnique (n : ℕ) :
    ∃! τ : spCompletedEvaluation l E T D (n + 1) ⟶ spCompletedEvaluation l E T D n,
      ∀ (M : spCoefficientTowers l E T) (U : T.ProEtᵒᵖ)
        (x : ((spCompletedEvaluation l E T D (n + 1)).obj M).val.obj U),
        (τ.app M).val.app U x =
          (((D.equivalence.functor.obj M).transition (Nat.le_succ n)).val.app U) x := by
  sorry

/-- The original transition with its restricted scalar action, selected only from
its sectionwise unique characterization. Source: blueprint, proof step 2
(blueprint: sk-lem-sp-tower). -/
def spCompletedTransition (n : ℕ) :
    spCompletedEvaluation l E T D (n + 1) ⟶ spCompletedEvaluation l E T D n :=
  (spCompletedTransition_existsUnique l E T D n).exists.choose

/-- Derived level evaluation followed by exact completed-coefficient restriction.
Source: blueprint, proof step 2 (blueprint: sk-lem-sp-tower). -/
def spDerivedCompletedEvaluation (n : ℕ) : spDerivedCoefficientTowers l E T D ⥤
    DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T) :=
  spDerivedCoefficientEvaluation l E T D n ⋙
    (spCompletedEllRestriction l E T n).mapDerivedCategory

/-- The canonical comparison between derived and termwise completed evaluation.
Source: blueprint, proof step 2 (blueprint: sk-lem-sp-tower). -/
def spCompletedEvaluationFactors (n : ℕ) :
    @DerivedCategory.Q (spCoefficientTowers l E T) _ _ D.hasDerived ⋙
        spDerivedCompletedEvaluation l E T D n ≅
      (spCompletedEvaluation l E T D n).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  letI := D.hasDerived
  letI := D.equivalenceAdditive
  letI := D.evaluationLimits n
  letI := D.evaluationColimits n
  letI : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    Functor.additive_of_preserves_binary_products _
  Functor.isoWhiskerRight (spCoefficientEvaluation l E T D.equivalence n).mapDerivedCategoryFactors
      (spCompletedEllRestriction l E T n).mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft
      ((spCoefficientEvaluation l E T D.equivalence n).mapHomologicalComplex (.up ℤ))
      (spCompletedEllRestriction l E T n).mapDerivedCategoryFactors

/-- The unique derived transition induced by the actual ordinary transition.
Source: blueprint, proof step 2 (blueprint: sk-lem-sp-tower).
Proof: the ordinary square is natural and therefore descends through localization,
since both evaluation functors preserve quasi-isomorphisms. The displayed comparison
formula fixes the transition on every localized complex. Essential surjectivity of
the localization and naturality then prove uniqueness on the whole derived category. -/
theorem spDerivedCompletedTransition_existsUnique (n : ℕ) :
    ∃! τ : spDerivedCompletedEvaluation l E T D (n + 1) ⟶
        spDerivedCompletedEvaluation l E T D n,
      ∀ P : CochainComplex (spCoefficientTowers l E T) ℤ,
        τ.app (@DerivedCategory.Q (spCoefficientTowers l E T) _ _ D.hasDerived |>.obj P) ≫
            (spCompletedEvaluationFactors l E T D n).hom.app P =
          (spCompletedEvaluationFactors l E T D (n + 1)).hom.app P ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex (spCompletedTransition l E T D n)
                (.up ℤ)).app P) := by
  sorry

/-- The canonical derived transition; it retains the strict tower's specified maps.
Source: blueprint, proof step 2 (blueprint: sk-lem-sp-tower). -/
def spDerivedCompletedTransition (n : ℕ) :
    spDerivedCompletedEvaluation l E T D (n + 1) ⟶
      spDerivedCompletedEvaluation l E T D n :=
  (spDerivedCompletedTransition_existsUnique l E T D n).exists.choose

/-- The natural reduction map, as the normalized derived tensor-restriction adjunct
of the given limit projection, in the finite-coefficient derived category.
Source: blueprint, displayed map and proof step 8 (blueprint: sk-lem-sp-tower). -/
def spTowerReconstructionMap (C : spDerivedCoefficientTowers l E T D)
    (M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
    [HasProduct (fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C)]
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C) (n : ℕ) :
    (D.scalar (spCompletedEllCommProjection l E T n)).model.T.obj M ⟶
      (spDerivedCoefficientEvaluation l E T D n).obj C :=
  ((D.scalar (spCompletedEllCommProjection l E T n)).adjunction.homEquiv M
    ((spDerivedCoefficientEvaluation l E T D n).obj C)).symm
    (p ≫ Pi.π (fun k : ℕ ↦ (spDerivedCompletedEvaluation l E T D k).obj C) n)

/-- A normalized constructible finite-Tor tower is reconstructed by its derived inverse
limit. The limit belongs to the recorded integral bounded constructible category, and
its canonical ell-power reductions are isomorphisms in the finite-coefficient categories.
The Roos presentation binds the limit and its projections, rather than adding a
condition on the tower. Source: blueprint main-20261015, sk-lem-sp-tower, order 1823;
Stacks Tags 0940 and 099P (blueprint: sk-lem-sp-tower).

Proof, following the twelve DAG steps:
1. Put O = O_E, R = O_(E,T), B_n = (O/ell^n)_T. The coefficient-tower definition
identifies R with the limit of B_n. The DVR theorem gives ell = unit times pi^e,
e >= 1, and cofinal ell- and pi-power ideals. Constant-completion flatness identifies
R/ell^m with B_m and makes multiplication by ell^m injective. Thus [R -> R], with
map ell^m in degrees [-1,0], is a finite free K-flat resolution of B_m. The analogous
pi-power resolution also exists. Each O/pi^s is finite by its residue-field filtration.
2. Take common cohomological and Tor bounds for the given tower, enlarging them to
one interval [a,b]. Resolve its levels successively by flat-term K-flat complexes,
representing the actual transitions by roofs and then chain maps. Their composites
retain every transition. Sequential evaluation fullness lifts the compatible finite
level identifications to an isomorphism of strict completed-ring derived towers.
It is existence, not uniqueness, of that lift which is needed; all projections agree.
3. Pro-etale repleteness implies exact countable products of modules: successively
replace one target coordinate by its source in a countable product of epimorphisms
and apply repleteness to the resulting surjective tower. Kernels commute with products.
Consequently products and the Roos model are computed termwise. Removing a finite
prefix preserves the model: its 1-shift matrix is triangular with identity diagonal,
and finite elimination splits off its contractible cone, preserving tail projections.
4. For n >= m the augmentation [B_n -> B_n] -> B_m, with map ell^m, has fiber
B_m[1]. Multiplication by ell^(n-m) identifies its degree -1 kernel with B_m.
The transition from n' to n on this fiber is multiplication by ell^(n'-n), including
n = m, where the kernel identification is the identity.
5. Tensor the fiber triangles with the K-flat level representatives Q_n. The middle
tower is Q_n tensor_R [R -> R]; the right tower is Q_n tensor_(B_n) B_m. The left
tower is the shifted right tower with transitions multiplied by ell^(n'-n).
Normalization identifies the actual reduction maps of the right tower with Q_m;
the strict cocycle makes this a map to the constant Q_m tower, not unrelated isomorphisms.
6. Every m consecutive transitions on the left tower are zero. Its shift is nilpotent,
so a finite geometric sum inverts 1-shift and its derived limit vanishes. Exactness
identifies the middle and right limits. The constant Q_m tower has limit Q_m because
finite partial sums split its product difference map and its kernel is the diagonal.
7. Tensor with the two-term finite free resolution commutes with the termwise products
and cones of the Roos model, with the usual differential signs. K-flat resolution of
the limit shows that this computes its derived tensor with B_m. All comparisons
preserve the m-th projection, so the resulting isomorphism is projection-induced.
8. Ordinary tensor-restriction adjunction sends f to c tensor x maps to c f(x).
Restriction is exact and detects acyclic cones. The derived adjunction therefore
identifies the preceding isomorphism with spTowerReconstructionMap in D(B_m), where
it is consequently an isomorphism. The maps [R -> R] for k <= m are (ell^(m-k),1);
together with the original transition cocycle they retain quotient compatibility.
9. For completeness use [R -> R] with map pi^j. Each Q_n is termwise killed by pi^(en).
For j >= en its tensor is Q_n plus Q_n[1], with identity transitions on the first
summand and pi on the second. The second tower is nilpotent and has zero derived
limit, while the first is constant. The canonical completion map for each row is
therefore an isomorphism. The cutoff is allowed to depend on n.
10. The two derived limits commute by expanding their two Roos cones: the four
components have the same doubly indexed products. Swap the two Roos degrees with
sign (-1)^(pq); the differentials agree since the two shifts commute. There are only
four summands per total degree. Finite-free tensor commutes with these products,
so the resulting limit comparison is the completion unit itself. Constant-completion
equivalence identifies Koszul and quotient completion, respecting that unit.
11. Products commute with cohomology and the levels have support in [a,b]. The long
exact sequence of the Roos triangle gives support of the limit in [a,b+1]. No
quasi-compactness of T, or an unjustified sharper bound, is asserted.
12. For j >= 1 choose N with eN >= j. The quotient O/pi^j is a quotient of O/ell^N.
K-flat scalar associativity identifies the uniformizer reduction of the limit with
C_N tensor_(B_N) (O/pi^j)_T. Finite-coefficient scalar extension preserves
constructibility and the common Tor interval [a,b], with no flatness or finite
projective-dimension assumption on that quotient. Testing Tor amplitude with the
quotient ring itself gives the same cohomological interval for all j. Together with
derived completeness these are precisely sfIntegralConstructible. No invertibility
of ell on T is used, and ell is never identified with the uniformizer. -/
theorem spTower_reconstruction (C : spDerivedCoefficientTowers l E T D)
    (hC : spConstructibleTorTowers l E T D C)
    (hnorm : IsSpNormalizedTower l E T D C)
    (M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
    [HasProduct (fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C)]
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C)
    (δ : (∏ᶜ fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C) ⟶ M⟦(1 : ℤ)⟧)
    (hlim : IsDerivedLimitTriangle
      (fun n : ℕ ↦ (spDerivedCompletedTransition l E T D n).app C) M p δ) :
    WeilConjectures.sfIntegralConstructible l E T M ∧
      ∀ n : ℕ, IsIso (spTowerReconstructionMap l E T D C M p n) := by
  sorry

end AlgebraicGeometry.ProEtale
