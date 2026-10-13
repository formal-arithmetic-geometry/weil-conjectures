module

public import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.ZariskisMainTheorem
public import Sheaf.RingTheory.QuasiFiniteAtPrime

@[expose] public section

universe u v

namespace Algebra

/-! The pointwise hypothesis conversion used with Mathlib's Zariski main theorem.

The former declaration in this module duplicated the conclusion of
`Algebra.ZariskisMainProperty.of_finiteType`. This declaration supplies only the
strictly separate conversion from the fibre formulation used by the Sheaf plan.
-/

/-- A quasi-finite fibre at a prime gives Mathlib's `QuasiFiniteAt` instance.
Source: Stacks Project, Algebra, Theorem Tag 00Q9, via the fibre-spectrum
homeomorphism and Mathlib's `QuasiFiniteAt.of_isOpen_singleton_fiber`.
-/
theorem zariskisMainProperty_of_isQuasiFiniteAtPrime
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S)
    (hq : IsQuasiFiniteAtPrime R S q) : QuasiFiniteAt R q.asIdeal := by
  let p := q.comap (algebraMap R S)
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  apply QuasiFiniteAt.of_isOpen_singleton_fiber q
  rw [← e.isOpen_image, Set.image_singleton]
  exact hq

-- The fibre homeomorphism identifies the singleton used above.
end Algebra
