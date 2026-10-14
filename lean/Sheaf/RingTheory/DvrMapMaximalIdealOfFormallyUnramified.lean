module

public import Mathlib.RingTheory.Unramified.LocalRing

@[expose] public section

universe u
namespace RingTheory

/-- A formally unramified local algebra over a local ring maps the base maximal
ideal onto the maximal ideal of the target.

This is the local algebraic conclusion used after the ramification calculation
in the proof of the uniformizer-root compositum theorem.  It is strictly
smaller than that theorem: all DVR, fraction-field, and compositum hypotheses
have already been discharged, and only the formally-unramified structure is
assumed.

Source: Mathlib, `Algebra.FormallyUnramified.map_maximalIdeal`.
(blueprint: lem-sbc-dvr-uniformizer-root-compositum-maximal-ideal)
-/
theorem dvr_map_maximalIdeal_of_formallyUnramified
    (A T : Type u) [CommRing A] [CommRing T] [IsLocalRing A] [IsLocalRing T]
    [Algebra A T] [IsLocalHom (algebraMap A T)]
    [Algebra.FormallyUnramified A T] [Algebra.EssFiniteType A T] :
    (IsLocalRing.maximalIdeal A).map (algebraMap A T) =
      IsLocalRing.maximalIdeal T := by
  exact Algebra.FormallyUnramified.map_maximalIdeal

end RingTheory
