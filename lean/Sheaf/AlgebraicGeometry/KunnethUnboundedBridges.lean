module

public import Sheaf.AlgebraicGeometry.UnboundedCumulativeUniversalBaseChangeProperty
public import Sheaf.AlgebraicGeometry.CumulativeUniversalBaseChangeProperty

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Convert the unbounded cumulative hypotheses into the cumulative lower-degree hypothesis
and the failing universal degree needed by the cyclic witness theorem. The first component
is degreewise extraction from the canonical pullback presentation. The second is its
contrapositive at the new bound, using invariance of the degreewise map under a chosen
Cartesian identification.
Source: the definitions of `UnboundedCumulativeUniversalBaseChangeProperty` and
`UniversalBaseChangeProperty`; blueprint `def-kun-bc-property` and
`sbc-def-base-change-property` (blueprint: new-kunneth-unbounded-interface). -/
theorem cumulative_and_not_universal_of_unbounded
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(S, ⊤))) (q : ℕ)
    (hprev : UnboundedCumulativeUniversalBaseChangeProperty f n hn (q - 1))
    (hfail : ¬ UnboundedCumulativeUniversalBaseChangeProperty f n hn q) :
    CumulativeUniversalBaseChangeProperty f n hn hinv (q - 1) ∧
      ¬ UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f (q : ℤ) := by
  sorry

end AlgebraicGeometry.Etale
