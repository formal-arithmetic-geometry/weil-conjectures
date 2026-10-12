module

public import Sheaf.RingTheory.EssentiallySmooth
import Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations
import Sheaf.RingTheory.SmoothAlgebraFilteredColimitDescent

@[expose] public section

universe u v w t

namespace Algebra

/-- A smooth algebra over an essentially smooth base is a localization of a smooth
algebra over the original ring. Source: Stacks Project, Algebra, Tags 00CR and 0CAQ;
agent-written reduction using Tags 00T3, 00TD, and 00DK.
(blueprint: lem-weil-pbc-smooth-over-essentially-smooth-base).

Proof: Write A as the localization of a smooth R-algebra C at S, using hA. Transport
Q and its A-algebra structure across this presentation. By 00CR, A is the filtered
colimit of C localized at s, for s in S. By 0CAQ, the smooth A-algebra Q descends
at some stage to a smooth C_s-algebra P, with Q isomorphic as an A-algebra to
A tensor over C_s with P. The map R to C_s is smooth (00T3), so P is smooth
over R by composition (00TD). The map C_s to A localizes at the image of S.
Base change (00DK) identifies P to Q with localization at the image of S in P.
The tensor balancing relation makes this map compatible with the R-structures.
Finally P is of finite type over R, hence small in universe u: a surjection from
polynomials in finitely many variables over R proves this. Transport P, its
submonoid, and its map to Q along a small model and lift to universe max u t.
These transports preserve smoothness, the localization property, and the scalar
tower. No localization of Q and no composition with a second localization is
asserted here. -/
theorem exists_smooth_localization_model
    (R : Type u) (A : Type v) (Q : Type w)
    [CommRing R] [CommRing A] [CommRing Q]
    [Algebra R A] [Algebra A Q] [Algebra R Q] [IsScalarTower R A Q]
    (hA : EssentiallySmooth R A) (hQ : Smooth A Q) :
    ∃ (P : Type (max u t)) (hP : CommRing P),
      letI : CommRing P := hP
      ∃ (hRP : Algebra R P),
        letI : Algebra R P := hRP
        ∃ (hPQ : Algebra P Q),
          letI : Algebra P Q := hPQ
          IsScalarTower R P Q ∧ Smooth R P ∧
            ∃ (S : Submonoid P), IsLocalization S Q := by
  sorry

end Algebra
