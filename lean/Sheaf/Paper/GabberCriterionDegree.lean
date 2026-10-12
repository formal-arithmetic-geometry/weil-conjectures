module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.AlgebraicGeometry.EtaleMayerVietoris
import Sheaf.AlgebraicGeometry.ZariskiCohomologyLocallyZero
import Sheaf.Paper.StrictHenselianZariskiEtaleComparison
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The fixed-degree case of Gabber's criterion.

This is the induction step of the proof of Gabber's criterion: for a fixed positive
integer `q`, the hypotheses imply that the `q`-th cohomology group is subsingleton.
The proof follows the simultaneous induction on principal opens, using strict
henselian Zariski comparison, local vanishing, the degree-one kernel hypothesis,
and Mayer--Vietoris.  This intermediate statement is split from the parent theorem
so that the induction argument can be developed independently.
Source: Stacks Project, Etale Cohomology, Lemma 0GY0.
(blueprint: lem-weil-pbc-gabber-criterion-degree)

Proof: perform the simultaneous induction on principal opens from Lemma 0GY0;
strict henselian comparison gives local Zariski vanishing, the degree-one kernel
hypothesis gives addition closure in degree one, and Mayer--Vietoris gives it in
higher degrees.  The radical argument then forces the fixed class to vanish.
-/
theorem gabberCriterion_degree
    (R : Type u) [CommRing R]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsStrictlyHenselianLocalRing (Localization.AtPrime p))
    (F : Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hfg : ∀ (f g : R) (x : Sheaf.H
            (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen (f + g)))^*[AddCommGrpCat.{u + 1}]).obj F) 1),
      (AlgebraicGeometry.Etale.cohomologyMap
            (Scheme.homOfLE (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen_mul_le_right f (f + g)))
            (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen (f + g)))^*[AddCommGrpCat.{u + 1}]).obj F) 1 x) = 0 →
      (AlgebraicGeometry.Etale.cohomologyMap
            (Scheme.homOfLE (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen_mul_le_right g (f + g)))
            (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen (f + g)))^*[AddCommGrpCat.{u + 1}]).obj F) 1 x) = 0 →
        x = 0)
    (q : ℕ) (hq : 0 < q) : Subsingleton (Sheaf.H F q) := by
  sorry

end AlgebraicGeometry.Etale
