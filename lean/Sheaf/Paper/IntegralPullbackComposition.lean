/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q143
-/
module

public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.IntegralOperationsPreserveConstructible
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.Paper.FiniteSystemPullbackCoherence
import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.Paper.SemilinearDerivedSections

/-!
# Composition of completed integral derived pullbacks

Source: Stacks Project, Tags 099N(2),(5) and 0D6D; Bhatt--Scholze,
Lemmas 3.5.5 and 3.5.7
(blueprint: lem-pod-integral-pullback-composition).

All categories use modules over the completed integral coefficient sheaf. The
positive exponent is n+1. The reduction comparison is the actual projection-adjoint
map, expressed in the published finite ring-sheaf presentation. Quantification over
all good representatives makes the reduction clause independent of choices.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical reduction rho of integral pullback, computed using any good resolution.
The first factor is the actual projection-adjoint map, whose invertibility is precisely
part (1) of integralOperations_preserve_constructible. The other factors only change
finite pullback presentation and identify the reduction of the representative with
that of K through the universal reduction counit.
Source: Stacks Tag 099N(5); Bhatt--Scholze, Lemma 6.5.9(5)
(blueprint: lem-pod-integral-pullback-composition). -/
def integralPullbackReductionIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj) (n : ℕ) :
    (scalarReductionDerivedExtension l E X n).obj
        ((constructibleIntegralPullback l E f).obj K).obj ≅
      (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f).obj
        ((scalarReductionDerivedExtension l E Y n).obj K.obj) :=
  letI := ((integralOperations_preserve_constructible l E f).1 K.obj K.property).2 P e n
  asIso (integralPullbackFiniteComparison l E f K.obj P e n) ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (integralFinitePullbackModel l E f n)
        (ComplexShape.up ℤ)).app ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj)) ≪≫
    ((proEtaleConstantRingPullback
      (Padic.coefficientExtensionRing l E (n + 1)) f).mapDerivedCategoryFactors.app
        ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj)).symm ≪≫
    (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f).mapIso
      ((coefficientFiniteReductionModel l E Y P.obj P.property.1 n).symm ≪≫
        (scalarReductionDerivedExtension l E Y n).mapIso e)

/-- A family of composition comparisons on the actual full constructible categories.
The type includes every composable pair of morphisms of schemes with l invertible.
Source: Stacks Tags 099N and 0D6D
(blueprint: lem-pod-integral-pullback-composition). -/
abbrev IntegralPullbackCompositionFamily :=
  ∀ {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V),
    constructibleIntegralPullback l E (h ≫ k) ≅
      constructibleIntegralPullback l E k ⋙ constructibleIntegralPullback l E h

/-- Integral pullback has natural composition isomorphisms, with their specified
finite reductions and associative composition law.

Source: Stacks Tags 099N(2),(5), 0D6D, 0941; Bhatt--Scholze, Lemmas 3.5.5 and 3.5.7
(blueprint: lem-pod-integral-pullback-composition).

Proof:
1. Use the reduction/total-limit adjunction of lem-coef-derived-system-evaluation-calculus
on strict varying-coefficient systems. Exact finite inverse image is supplied by
prop-weil-pbc-proetale-constant-exact; the simultaneous system model is
lem-coef-semilinear-derived-sections. Reductions of one flat-term K-flat resolution
remain K-flat (lem-pur-kflat-change-of-rings). Quotient tensor comparisons multiply
coefficients and obey the cocycle. Pullback preserves these comparisons by
lem-weil-pbc-ringed-topoi-derived-tensor-pullback. The integral construction and
lem-pur-integral-operations-well-defined identify its functor with total limit after
finite inverse image and reduction. Exact countable products and the natural Roos
triangle (lem-weil-proetale-countable-products-exact and
lem-weil-pbc-ringed-strict-tower-homotopy-limit) make this an identification on maps.
2. The system-adjunction counit gives beta_f: R F_f -> U_f R. Its evaluations are
the adjoints of the actual tower projections, hence the specified rho maps.
lem-coef-normalized-dvr-effectivity makes beta invertible on normalized systems.
lem-pur-integral-operations-preserve-constructible types every pullback value in
D^b_c. The triangle identity makes the adjunction unit eta invertible on these
values, giving full faithfulness of reduction on the objects used below.
3. Apply lem-weil-pbc-proetale-derived-pullback-composition on each finite quotient.
Its termwise tensor reassociation commutes with quotient maps, so it gives a coherent
system isomorphism a_hk. With B = U_h(beta_k) beta_h, set delta = B^{-1} a_hk beta_hk.
Lift delta by eta_target^{-1} L(delta) eta_source. All factors are invertible and
natural, giving c on the actual integral functors and their full subcategories.
4. Evaluate B R(c) = a_hk beta_hk at every positive exponent. This is exactly the
reduction equation below, after the canonical representative comparisons defining
integralPullbackReductionIso. No subsequence of exponents or unramifiedness is used.
5. Reduce both triple composites and identify their common target with U_j U_h U_k R.
Naturality of beta and the equation in step 4 give respectively
U_j(a_hk) a_j,hk beta_hkj and a_jh(U_k R) a_hj,k beta_hkj. Before localization both
finite composites are the same tensor reassociation: their forward maps insert
units, and their inverses multiply the three transported scalar factors. These
formulas commute with all quotient transitions. The simultaneous system model
therefore gives equality of system maps. Cancel the common invertible comparison
and use full faithfulness from step 2 to obtain the integral associativity equation.
The explicit eqToHom below only identifies the two parenthesizations of j >> h >> k. -/
theorem integralPullbackComposition :
    ∃ c : IntegralPullbackCompositionFamily l E,
      (∀ {V W Z : Scheme.{u}}
        [∀ v : V, Invertible (l : V.residueField v)]
        [∀ w : W, Invertible (l : W.residueField w)]
        [∀ z : Z, Invertible (l : Z.residueField z)]
        (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V)
        (P : (integralOperationsGoodComplex l E V).FullSubcategory)
        (e : DerivedCategory.Q.obj P.obj ≅ K.obj)
        (Q : (integralOperationsGoodComplex l E W).FullSubcategory)
        (d : DerivedCategory.Q.obj Q.obj ≅ ((constructibleIntegralPullback l E k).obj K).obj)
        (n : ℕ),
        (scalarReductionDerivedExtension l E Z n).map ((c h k).hom.app K).hom ≫
            (integralPullbackReductionIso l E h
              ((constructibleIntegralPullback l E k).obj K) Q d n).hom ≫
            (proEtaleConstantRingDerivedPullback
              (Padic.coefficientExtensionRing l E (n + 1)) h).map
                (integralPullbackReductionIso l E k K P e n).hom =
          (integralPullbackReductionIso l E (h ≫ k) K P e n).hom ≫
            (integralFiniteCanonicalPullbackComposition l E h k n).hom.app
              ((scalarReductionDerivedExtension l E V n).obj K.obj)) ∧
      (∀ {V W Z Y : Scheme.{u}}
        [∀ v : V, Invertible (l : V.residueField v)]
        [∀ w : W, Invertible (l : W.residueField w)]
        [∀ z : Z, Invertible (l : Z.residueField z)]
        [∀ y : Y, Invertible (l : Y.residueField y)]
        (j : Y ⟶ Z) (h : Z ⟶ W) (k : W ⟶ V)
        (K : sfIntegralConstructibleCategory l E V),
        (c j (h ≫ k)).hom.app K ≫
            (constructibleIntegralPullback l E j).map ((c h k).hom.app K) =
          eqToHom (congrArg
            (fun f : Y ⟶ V ↦ (constructibleIntegralPullback l E f).obj K)
            (Category.assoc j h k).symm) ≫
            (c (j ≫ h) k).hom.app K ≫
              (c j h).hom.app ((constructibleIntegralPullback l E k).obj K)) := by
  sorry

end WeilConjectures
