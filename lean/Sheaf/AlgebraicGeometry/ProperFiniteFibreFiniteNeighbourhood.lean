import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Proper morphisms with finite fibres are finite near a point

Source: Stacks Project, Tag 02OH (blueprint: thm-sc-proper-finite-fibre-finite-neighbourhood).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A proper morphism over a locally Noetherian scheme with finite fibre at a point
is finite after restricting to a neighbourhood of that point. Source: Stacks Project,
Tag 02OH (blueprint: thm-sc-proper-finite-fibre-finite-neighbourhood).

Proof: Properness gives finite type and universal closedness, so the finite fibre implies
quasi-finiteness along the fibre (pqf-lem-proper-basic and pqf-lem-locqf-fibre-discrete).
The quasi-finite locus is open (lem-sc-quasi-finite-points-open); properness makes the
image of its closed complement closed, yielding an open neighbourhood whose restriction
is quasi-finite. The restriction remains proper by lem-pc-proper-base-change, and hence
is finite by pqf-lem-qf-locqf-qc, pqf-lem-qf-finitefibres, and
thm-pqf-finite-iff-proper-finite-fibres.
-/
theorem exists_open_isFinite_restrict_of_isProper_of_finite_fibre
    {X S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S) [IsProper f] (s : S)
    (hs : (f ⁻¹' ({s} : Set S)).Finite) :
    ∃ U : S.Opens, s ∈ U ∧ IsFinite (f ∣_ U) := by
  sorry

end AlgebraicGeometry
