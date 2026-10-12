module
public import Sheaf.RingTheory.SingularIdeal
@[expose] public section
universe u v
namespace Algebra
/-- If a set of elements with smooth principal localizations spans the target ideal,
then the target algebra is smooth, allowing different universes.

Proof source: the finite principal-cover criterion for smooth ring maps
(Mathlib's `RingHom.Smooth.ofLocalizationSpanTarget`), transported across the
localization algebra structures. The theorem is stated separately so the source
and target types may inhabit different universes.
(blueprint: lem-weil-pbc-smooth-of-localization-span-universes).
The proof applies the finite principal-cover criterion with transported algebra structures. -/
theorem smooth_of_localization_span_universes
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    (s : Set A) (hs : Ideal.span s = ⊤)
    (h : ∀ g : s, Smooth R (Localization.Away (g : A))) :
    Smooth R A := by sorry
end Algebra
