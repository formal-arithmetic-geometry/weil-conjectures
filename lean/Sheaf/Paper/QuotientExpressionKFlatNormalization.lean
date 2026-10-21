/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q95
-/
module

public import Sheaf.Paper.StrictQuotientExpressions
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap

/-! # Simultaneous K-flat normalization of strict quotient expressions

Source: Stacks Project, sites-cohomology.tex, Tags 0G7E, 07A2, 07A4 and 07A6;
quotient-expression refinement of integral coherence, proof step 1
(blueprint: lem-pur-quotient-expression-kflat-normalization).

All transitions belong to strict sequence complexes before localization. The
ordinary and derived adjoints below are adjoints of those actual maps. No assertion
that inverse image commutes with the completed coefficient limit is made.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures.StrictQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Simultaneous strict quotient normalization. Fin r is an arbitrary finite list,
including r=0. The isomorphisms kappa identify the generator towers with the specified
ordinary reductions, including every actual quotient transition. Generated records
only finite uses of the three named arrows, tensor, and the three degree-zero units.

Source: Stacks Project, Tags 0G7E, 07A2, 07A4 and 07A6
(blueprint: lem-pur-quotient-expression-kflat-normalization).

Proof:
1. Constant-ring inverse-image comparisons commute with quotients, because both
   maps agree on constant sections and hence after sheafification. Work on the
   compatible small representatives of def-weil-proetale-inverse-image.
2. For each P_i, lem-pur-kflat-change-of-rings preserves flat terms and K-flatness
   along R_Y to B_(Y,n); lem-pur-derived-change-of-rings computes its localization.
   The unit is K-flat, with one free term and zero terms in the other degrees.
3. Induct on Generated. The direct-sum total tensor case is exactly
   lem-pur-kflat-total-tensor-model, including unbounded inputs and flat total terms.
4. The pullback case follows from lem-weil-pbc-ringed-topoi-derived-tensor-pullback
   and the constant-ring comparisons. Termwise pullback computes derived pullback.
5. The generator transitions are id tensor q, and the units have transition q.
   Tensor transitions send u tensor v to t(u) tensor t(v). Pullback sends
   s tensor u to q(s) tensor g-inverse-image(t)(u). Balancing, restriction,
   and the signed total differentials commute with these formulas. Quotient
   identity and cocycle therefore hold before localization. Restricting along
   the completion projections makes a complex of strict R_W-towers.
6. Apply lem-pur-sheaf-ring-derived-coefficient-adjunction to the actual transition.
   Its ordinary adjoint sends z tensor a to a times t(z), and its localization,
   through the universal K-flat counit, is precisely the derived adjoint.
7. On a generator the ordinary adjoint sends (x tensor b) tensor a to
   x tensor q(b)a. Its inverse sends x tensor a to (x tensor 1) tensor a.
   The two composites are identities by balancing and q pi_m=pi_n.
   The unit case is multiplication with inverse a to 1 tensor a.
8. For tensor expressions use lem-pur-cochain-pullback-tensor-coherence at q:
   (u tensor v) tensor a maps to (u tensor a) tensor (v tensor 1).
   Compose with the two factor adjoints. Its pure-tensor formula is precisely
   the ordinary adjunct from step 6; its inverse contracts the two scalars.
   Localization gives the strong monoidal comparison followed by the two alphas.
9. For pullback use lem-sfb-kflat-scalar-comparison-normalization. Its insertion
   unit equation identifies the transported pullback of the factor adjoint with
   this ordinary adjunct, by uniqueness under the tensor/restriction adjunction.
   Localization is the canonical scalar-change comparison and g-inverse-image(alpha).
10. All these adjoints are chain isomorphisms. Step 6 gives AdjointModel for every
    normalized coefficient calculus. The universal Hom criterion gives
    IsNormalizedCoefficientSequence, exactly the normalization of
    def-coef-normalized-dvr-tower for the specified coherent strict system.
    Empty lists, zero inputs, empty schemes and m=n require no separate choices.
-/
theorem quotientExpressionKFlatNormalization
    {Z X Y : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (_hlZ : ∀ x : Z, IsUnit (l : Z.residueField x))
    (_hlX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hlY : ∀ x : Y, IsUnit (l : Y.residueField x))
    (r : ℕ) (P : Fin r → CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : ∀ i : Fin r, CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) (P i))
    (_hflat : ∀ (i : Fin r) (k : ℤ), SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) ((P i).X k)) :
    ∃ (N : Fin r → Complex l E Y)
      (κ : ∀ (i : Fin r) (n : ℕ), level l E (N i) n ≅
        ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj (P i)),
      (∀ (i : Fin r) {m n : ℕ} (hmn : n ≤ m),
        transition l E (N i) hmn ≫
            ((normalizedDVRModuleRes l E Y hmn).mapHomologicalComplex (.up ℤ)).map
              (κ i n).hom =
          (κ i m).hom ≫
            (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E Y hmn)
              (.up ℤ)).app (P i)) ∧
      (∀ (i : Fin r) (n : ℕ),
        ∃ e : (coefficientFiniteDerivedExtension l E Y n).obj
            (DerivedCategory.Q.obj (P i)) ≅ DerivedCategory.Q.obj (level l E (N i) n),
          e.hom = (coefficientFiniteReductionModel l E Y (P i) (hP i) n).hom ≫
            DerivedCategory.Q.map (κ i n).inv) ∧
      (∀ (W : Scheme.{t}) (K : Complex l E W), Generated l E h f N W K →
        (∀ n : ℕ, Good l E K n) ∧
        IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj K) ∧
        (∀ (S : CoefficientDerivedSystemTensors l E W)
          (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m),
          ∃ hK : CochainComplex.IsKFlatIndependentCoefficients
            (R := integralCoefficientCommRingSheaf l E W m) (level l E K m),
            AdjointModel l E K S D hmn hK)) ∧
      (∀ (W : Scheme.{t}) (U V : Complex l E W),
        Generated l E h f N W U → Generated l E h f N W V →
        TensorTransitions l E U V ∧
        (∀ (n : ℕ) (S : CoefficientDerivedSystemTensors l E W),
          ∃ (hU : Good l E U n) (hV : Good l E V n)
            (e : DerivedCategory.Q.obj (level l E (total l E U V) n) ≅
              (S.finiteClosed n).tensor.obj
                (DerivedCategory.Q.obj (level l E U n), DerivedCategory.Q.obj (level l E V n))),
            e.hom = DerivedCategory.Q.map (coefficientEvaluationTensorIso l E W n U V).hom ≫
              ((S.finiteTensorModel n).iso (Scheme.ProEt.topology W)
                (integralCoefficientCommRingSheaf l E W n) (S.finiteClosed n)
                (level l E U n) (level l E V n) hU.1 hV.1).hom) ∧
        (∀ (S : CoefficientDerivedSystemTensors l E W)
          (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m)
          (hUm : Good l E U m) (hVm : Good l E V m)
          (hUn : Good l E U n) (hVn : Good l E V n),
          TensorAdjointEquation l E U V S D hmn hUm hVm hUn hVn)) ∧
      (∀ {V W : Scheme.{t}} (g : V ⟶ W), AllowedArrow h f g →
        ∀ K : Complex l E W, Generated l E h f N W K →
          PullbackTransitions l E g K ∧
          (∀ n : ℕ, PullbackModel l E g K n ∧ PullbackComputes l E g K n) ∧
          (∀ (SW : CoefficientDerivedSystemTensors l E W)
            (DW : CoefficientFiniteQuotientCalculus l E W SW)
            (SV : CoefficientDerivedSystemTensors l E V)
            (DV : CoefficientFiniteQuotientCalculus l E V SV) {m n : ℕ} (hmn : n ≤ m),
            PullbackAdjointEquation l E g K SW DW SV DV hmn)) := by
  sorry

end WeilConjectures.StrictQuotient
