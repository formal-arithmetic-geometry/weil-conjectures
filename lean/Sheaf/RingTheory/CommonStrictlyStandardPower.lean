module
public import Sheaf.RingTheory.StrictlyStandardElement
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Kaehler.Basic
import Sheaf.RingTheory.SmoothFreeDifferentialsStrictlyStandardPower
@[expose] public section
universe u v
namespace Algebra
/-- Source: Stacks Project, Lemma 07EZ(e), applied to finitely many elements.
(blueprint: lem-weil-pbc-common-strictly-standard-power).
Proof: for each element, finite free differentials are stably free (add the rank-zero
free module). Apply 07EZ(e) to obtain a positive threshold valid for every larger
exponent. Choose one plus the sum of all thresholds. Every threshold is bounded by
this sum, so all powers at that common positive exponent are strictly standard.
An empty index type has exponent one. Zero localizations have the empty basis and
are included in 07EZ(e). -/
theorem exists_common_strictlyStandard_power
    (R : Type u) (C : Type v) [CommRing R] [CommRing C] [Algebra R C]
    [FinitePresentation R C] {ι : Type} [Finite ι] (x : ι → C)
    (h : ∀ i, Smooth R (Localization.Away (x i)) ∧
      Module.Free (Localization.Away (x i))
        (KaehlerDifferential R (Localization.Away (x i)))) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ i, IsStrictlyStandardElement (R := R) (x i ^ c)  := by sorry
end Algebra
