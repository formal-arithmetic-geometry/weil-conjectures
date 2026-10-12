module
public import Sheaf.RingTheory.SingularIdeal
import Sheaf.RingTheory.SmoothOfLocalizationSpanUniverses
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Away.Basic
@[expose] public section
universe u v
namespace Algebra

/-- The localization smoothness argument from a radical-span relation.

This is the finite-cover reduction: a power of `f` lies in the span of smooth
principal-localization elements, so those elements generate the unit ideal after
localizing at `f`; smoothness is then local on that cover. The final span-locality
step is isolated in `smooth_of_localization_span_universes`.
(blueprint: lem-weil-pbc-singular-ideal-localization-smooth-radical-span).
The proof proceeds by the finite principal-cover argument described above. -/
theorem smooth_localization_span_from_radical
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    (f : A) (n : ℕ) (hn : f ^ n ∈ Ideal.span (smoothElements R A)) :
    Smooth R (Localization.Away f) := by sorry

/-- If an element belongs to the singular ideal, its principal localization is smooth.
This follows by `Ideal.mem_radical_iff` and the radical-span reduction above.
(blueprint: lem-weil-pbc-singular-ideal-localization-smooth). -/
theorem smooth_localization_of_mem_singularIdeal
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    (f : A) (hf : f ∈ singularIdeal R A) : Smooth R (Localization.Away f) := by
  have hpow : ∃ n : ℕ, f ^ n ∈ Ideal.span (smoothElements R A) :=
    Ideal.mem_radical_iff.mp hf
  obtain ⟨n, hn⟩ := hpow
  exact smooth_localization_span_from_radical R A f n hn

end Algebra
