module
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
import Sheaf.RingTheory.AdicCompletionNoetherian
set_option autoImplicit false
@[expose] public section
universe u
namespace RingTheory
/-! (blueprint: lem-weil-pbc-completion-dimension-eq) -/
/-- (blueprint: lem-weil-pbc-completion-dimension-eq) Equality of Krull dimensions for
maximal-ideal adic completion.
Proof: apply the flat height formula to the canonical flat map from A to its completion at
the maximal ideal. The completion is local with the extended maximal ideal, and its closed
fibre is the residue field A/m, hence has dimension zero. Localizing at the maximal ideals
does not change either local ring, so the formula gives equality. -/
 theorem completion_dimension_eq (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] :
    ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A) = ringKrullDim A := by
  sorry
end RingTheory
