/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.Paper.CompletedBaseChangeMap
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.AmplificationProper
import Sheaf.Paper.CompletedPullbackReduction
import Sheaf.Paper.PerfectProjectionFormula
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.RingTheory.UniformPerfectQuotientBound
import Sheaf.AlgebraicGeometry.ProEtaleStalkConservative

/-! # Finite-reduction control for completed coefficient operations

Source: blueprint proper base change, constructible-preservation proof, steps 1, 3--5.
The conclusion records cohomology, before local models and etale witnesses are assembled.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- One cohomological window for the canonical reductions.
No local models or etale origins are asserted. Source: Stacks 09C7, 099N and 09AL
(blueprint: lem-weil-pbc-completed-constructible-reduction-control). -/
def PbcConstructibleReductionControl
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived T d) : Prop :=
  ∃ a b : ℤ, a ≤ b ∧
      (∀ (n : ℕ) (q : ℤ),
        @IsConstructibleProEtaleCoefficientModuleSheaf T (A ⧸ d.ideal ^ (n + 1)) _
          (d.quotientFinite n)
          ((pbcRestrict (pbcLevelConstantComparison T d n).hom).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((pbcCompletedReduction T d n).obj K)))) ∧
      (∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((pbcCompletedReduction T d n).obj K)))

/-- The canonical finite reductions of the four operations have
constructible cohomology in one common window.
Source: blueprint main-20261015, prop-weil-pbc-preservation-constructible.proof.md,
steps 1 and 3--5; Stacks 09C7, 099N, 09AL
(blueprint: lem-weil-pbc-completed-constructible-reduction-control).

Proof: take a common local term interval [d0,d1] of the input. Uniform perfect quotient
resolutions in [-r,0], sheafified by the flat constant-to-completed comparison, compute
the reductions locally in [d0-r,d1]. On each stratum its supplied covering detects
vanishing; every geometric point is on a stratum. The retained bounded-below etale
origins and geometric stalk conservativity turn these into global cohomological bounds.
The finite-lisse cohomology of the models gives constructibility.
Apply amplification_of_isProper with N and the fibre bound e, giving AMP(2e).
The perfect projection formula compares its reductions with finite direct image on
cohomology: quotient-linearity follows by locally lifting quotient scalars to the
completed ring and using annihilation to make the lifts irrelevant. Finite amplification
therefore gives constructibility and interval [d0-r,d1+2e]. Completed-pullback reduction
gives quotient-linear reduction comparisons; finite pullback
preserves constructibility and the interval. Apply these facts to K and then Rf_*K,
and repeat direct image for f-prime after pulling back K along g-prime. Transport the
finite-level bounds and constructibility through the quotient-linear comparisons.
No etale origin, normalization, or local model for an output is constructed here.
Zero objects, empty schemes and zero quotients obey the same vanishing containments. -/
theorem AdicCoefficientDatum.constructible_reduction_control
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    (hDimX : ∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (hDimY : ∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))
    (hDimX' : ∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))
    (hDimY' : ∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))
    [IsProper f] [IsProper f']
    (N : ℕ) (hN : 0 < N) (hAnn : (N : A ⧸ d.ideal) = 0)
    (hNX : IsUnit (N : Γ(X, ⊤))) (hNY : IsUnit (N : Γ(Y, ⊤)))
    (hNX' : IsUnit (N : Γ(X', ⊤))) (hNY' : IsUnit (N : Γ(Y', ⊤)))
    (e : ℕ)
    (hFibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (y : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (pullback f y : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (K : d.derived X) (hK : PbcIsBoundedConstructibleComplete X d K) :
    PbcConstructibleReductionControl Y d ((d.push f).obj K) ∧
      PbcConstructibleReductionControl Y' d
        ((d.completedPull g).obj ((d.push f).obj K)) ∧
      PbcConstructibleReductionControl X' d ((d.completedPull g').obj K) ∧
      PbcConstructibleReductionControl Y' d
        ((d.push f').obj ((d.completedPull g').obj K)) := by
  sorry

end AlgebraicGeometry.Scheme
