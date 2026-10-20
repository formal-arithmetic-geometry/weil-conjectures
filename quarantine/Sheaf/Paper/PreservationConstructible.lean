/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.Paper.CompletedTowerPullback
public import Sheaf.Paper.CompletedTowerDirectImage
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.PbcConstructibleReductionCriterion
import Sheaf.Paper.PbcConstructibleReductionPullback
import Sheaf.Paper.PbcConstructibleReductionDirectImage
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension

/-! # Constructible preservation over completed integral coefficients

Source: Weil blueprint, sec-proper-base-change/sk-thm-properbasechange, order 1355
(blueprint: prop-weil-pbc-preservation-constructible).
The four outputs use the actual completed coefficient ring, ordinary uncompleted
right derived direct image, and the strict-tower completed pullback.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- A common cohomological support bound for every positive canonical reduction.
This only asserts vanishing outside the closed interval, with no Tor-amplitude claim.
The original small-site quotient module retains its coefficient action.
Source: blueprint order 1355, final paragraph
(blueprint: prop-weil-pbc-preservation-constructible). -/
def pbcReductionsCohomologyIn (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (a b : ℤ) (K : PbcCompletedDerived T d) : Prop :=
  ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
    IsZero ((DerivedCategory.homologyFunctor
      (pbcModules T ((pbcAdicRings T d).obj (op n))) q).obj
        ((pbcCompletedReduction T d n).obj K))

private theorem pbc_fieldPoint_dimension
    {S T : Scheme.{u}} (f : S ⟶ T) [LocallyOfFiniteType f]
    {Ω : Type u} [Field Ω] (y : T)
    (t : CommRingCat.of (T.residueField y) ⟶ CommRingCat.of Ω) :
    topologicalKrullDim (pullback f (Spec.map t ≫ T.fromSpecResidueField y) : Scheme.{u}) =
      topologicalKrullDim (f.fiber y) := by
  calc
    _ = topologicalKrullDim
        (pullback (pullback.snd f (T.fromSpecResidueField y)) (Spec.map t) : Scheme.{u}) :=
      (IsHomeomorph.topologicalKrullDim_eq _
        (pullbackLeftPullbackSndIso f (T.fromSpecResidueField y)
          (Spec.map t)).hom.homeomorph.isHomeomorph).symm
    _ = _ := topologicalKrullDim_pullback_eq_of_field _ _

private theorem pbc_all_fieldPoint_bounds
    {S T : Scheme.{u}} (f : S ⟶ T) [LocallyOfFiniteType f] (e : ℕ)
    (h : ∀ y : T, topologicalKrullDim
      (pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (T.residueField y) (AlgebraicClosure (T.residueField y)))) ≫
          T.fromSpecResidueField y) : Scheme.{u}) ≤ (e : WithBot ℕ∞)) :
    ∀ (Ω : Type u) [Field Ω] (s : Spec (.of Ω) ⟶ T),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞) := by
  intro Ω _ s
  obtain ⟨⟨y, t⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω T).symm.surjective s
  change topologicalKrullDim
    (pullback f (Spec.map t ≫ T.fromSpecResidueField y) : Scheme.{u}) ≤ _
  rw [pbc_fieldPoint_dimension]
  simpa only [pbc_fieldPoint_dimension] using h y

/-- Simultaneous preservation and reduction support bounds for the four outputs.
Source: blueprint order 1355; Stacks 09C1, 09C7, 095U, 0GL0 and 09C2
(blueprint: prop-weil-pbc-preservation-constructible).

Proof:
1. Field extension preserves the dimension of finite-type fibres. Factor field-valued
points through their residue fields and paste the chosen Cartesian square to obtain
the field-valued fibre bound for both f and f'.
2. Apply the integral canonical-reduction criterion to the input. It supplies intrinsic
completeness and the homologyProperty clause of the existing uniform reduction profile.
3. Apply the single-map direct-image theorem to f and K. Apply the pullback theorem to
g' and K and to g and Rf_*K. Apply the direct-image theorem to f' and the first pullback.
The two direct images increase only the upper bound by 2e; pullbacks retain their input
intervals. The finite-level direct-image and pullback lemmas and the canonical reduction
comparisons prove these assertions with their actual quotient actions.
4. Apply the reverse integral criterion to all four complete outputs, using [a,b] for
the pullback of K and [a,b+2e] for the other three. Combine the four memberships and
four support bounds. Empty intervals and empty schemes obey the same arguments. -/
theorem pbc_preservation_constructible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (_square : ChosenCartesianSquare g' f' f g)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    (_hDimX : ∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (_hDimY : ∃ d : ℕ, topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
    (_hDimX' : ∃ d : ℕ, topologicalKrullDim X' ≤ (d : WithBot ℕ∞))
    (_hDimY' : ∃ d : ℕ, topologicalKrullDim Y' ≤ (d : WithBot ℕ∞))
    [IsProper f] [IsProper f']
    (N : ℕ) (_hN : 0 < N)
    (_hAnn : (N : Padic.coefficientExtensionRing l E 1) = 0)
    (_hInvertX : IsUnit (N : Γ(X, ⊤))) (_hInvertY : IsUnit (N : Γ(Y, ⊤)))
    (_hInvertX' : IsUnit (N : Γ(X', ⊤))) (_hInvertY' : IsUnit (N : Γ(Y', ⊤)))
    (e : ℕ)
    (_hFib : ∀ y : Y, topologicalKrullDim
      ((CategoryTheory.Limits.pullback f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y)) : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (a b : ℤ)
    (K : PbcCompletedDerived X (pbcIntegralDatum l E))
    (_hK : PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E) K)
    (_hInterval : pbcReductionsCohomologyIn X (pbcIntegralDatum l E) a b K) :
    PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)
      ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K) ∧
    PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l E)
      (completedPullbackObject g (pbcIntegralDatum l E)
        ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K)) ∧
    PbcIsBoundedConstructibleComplete X' (pbcIntegralDatum l E)
      (completedPullbackObject g' (pbcIntegralDatum l E) K) ∧
    PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l E)
      ((completedDerivedDirectImage f' (pbcIntegralDatum l E)).obj
        (completedPullbackObject g' (pbcIntegralDatum l E) K)) ∧
    pbcReductionsCohomologyIn X' (pbcIntegralDatum l E) a b
      (completedPullbackObject g' (pbcIntegralDatum l E) K) ∧
    pbcReductionsCohomologyIn Y (pbcIntegralDatum l E) a (b + 2 * (e : ℤ))
      ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K) ∧
    pbcReductionsCohomologyIn Y' (pbcIntegralDatum l E) a (b + 2 * (e : ℤ))
      (completedPullbackObject g (pbcIntegralDatum l E)
        ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K)) ∧
    pbcReductionsCohomologyIn Y' (pbcIntegralDatum l E) a (b + 2 * (e : ℤ))
      ((completedDerivedDirectImage f' (pbcIntegralDatum l E)).obj
        (completedPullbackObject g' (pbcIntegralDatum l E) K)) := by
  have hFib := pbc_all_fieldPoint_bounds f e _hFib
  have hsq : IsPullback g' f' f g :=
    IsPullback.of_iso_pullback _square.toCommSq _square.isoPullback
      _square.hom_fst _square.hom_snd
  have hFib' : ∀ (Ω : Type u) [Field Ω] (s : Spec (.of Ω) ⟶ Y'),
      topologicalKrullDim (pullback f' s : Scheme.{u}) ≤ (e : WithBot ℕ∞) := by
    intro Ω _ s
    have hs := (IsPullback.of_hasPullback f' s).paste_horiz hsq
    have he := hs.isoPullback
    rw [IsHomeomorph.topologicalKrullDim_eq _ he.hom.homeomorph.isHomeomorph]
    exact hFib Ω (s ≫ g)
  have hInput := (pbc_constructible_reduction_criterion l E X
    a b K _hInterval).mp _hK
  have hPush := pbc_constructible_reduction_directImage l E _hDimX _hDimY f N
    _hN _hAnn _hInvertX _hInvertY e hFib a b K hInput.1 hInput.2 _hInterval
  have hPull := pbc_constructible_reduction_pullback l E g'
    a b K hInput.1 hInput.2 _hInterval
  have hPullPush := pbc_constructible_reduction_pullback l E g
    a (b + 2 * (e : ℤ)) _ hPush.1 hPush.2.1 hPush.2.2
  have hPushPull := pbc_constructible_reduction_directImage l E _hDimX' _hDimY' f' N
    _hN _hAnn _hInvertX' _hInvertY' e hFib' a b _ hPull.1 hPull.2.1 hPull.2.2
  refine ⟨?_, ?_, ?_, ?_, hPull.2.2, hPush.2.2, hPullPush.2.2, hPushPull.2.2⟩
  · exact (pbc_constructible_reduction_criterion l E Y
      a (b + 2 * (e : ℤ)) _ hPush.2.2).mpr ⟨hPush.1, hPush.2.1⟩
  · exact (pbc_constructible_reduction_criterion l E Y'
      a (b + 2 * (e : ℤ)) _ hPullPush.2.2).mpr ⟨hPullPush.1, hPullPush.2.1⟩
  · exact (pbc_constructible_reduction_criterion l E X'
      a b _ hPull.2.2).mpr ⟨hPull.1, hPull.2.1⟩
  · exact (pbc_constructible_reduction_criterion l E Y'
      a (b + 2 * (e : ℤ)) _ hPushPull.2.2).mpr ⟨hPushPull.1, hPushPull.2.1⟩

end WeilConjectures
