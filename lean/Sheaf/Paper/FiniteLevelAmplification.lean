/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q08 and Q31
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.AlgebraicGeometry.FiniteLevelAmplification

/-!
# Finite-level amplification on arbitrary squares

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1350;
Stacks Project, Tags 095U, 0GL0, 09C1 and 09C7
(blueprint: def-weil-pbc-finite-level-amplification).

The published AMP declaration takes the scheme conventions of FIN as parameters.
This interface packages them existentially so TOW is a predicate on every square.
All finite coefficient categories, operations, constructibility and interval predicates
are the published ones; none is redefined here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- AMP(square;c), using the published predicate with its FIN conventions packaged
inside the property. The arithmetic hypotheses are supplied by the existing datum.
Both direct images, both exact triangulated pullbacks, all positive quotients and
every ordered cohomological interval are exactly those of the published predicate.
Source: blueprint order 1350 (blueprint: def-weil-pbc-finite-level-amplification). -/
def HasFiniteLevelAmplification {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (c : ℕ) : Prop :=
  ∃ (hY : IsNoetherian Y) (hY' : IsNoetherian Y')
    (hDimY : ∃ k : ℕ, topologicalKrullDim Y ≤ (k : WithBot ℕ∞))
    (hDimY' : ∃ k : ℕ, topologicalKrullDim Y' ≤ (k : WithBot ℕ∞))
    (hInvertY : ∀ (n : ℕ+) (a : A ⧸ d.ideal ^ (n : ℕ)) (y : Y),
      IsUnit (addOrderOf a : Y.presheaf.stalk y))
    (hInvertY' : ∀ (n : ℕ+) (a : A ⧸ d.ideal ^ (n : ℕ)) (y : Y'),
      IsUnit (addOrderOf a : Y'.presheaf.stalk y)),
    @AlgebraicGeometry.ProEtale.HasFiniteLevelAmplification X' X Y' Y g' f' f g sq
      A _ d.noetherian d.ideal d.finitelyGenerated
      (fun x ↦ isOfFinAddOrder_iff_nsmul_eq_zero.mpr (d.quotientTorsion x))
      (fun n ↦ (congrArg (fun k : ℕ ↦ Finite (A ⧸ d.ideal ^ k))
        (Nat.succ_pred_eq_of_pos n.property)).mp (d.quotientFinite (n : ℕ).pred))
      (fun n ↦ d.quotientPerfect n n.property) hY hY'
      hDimY hDimY' hInvertY hInvertY' c

end AlgebraicGeometry.Scheme
