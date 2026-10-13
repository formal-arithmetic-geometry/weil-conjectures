module
public import Mathlib.RingTheory.ZariskisMainTheorem
public import Sheaf.RingTheory.QuasiFiniteAtPrime
@[expose] public section
universe u v
namespace Algebra
/-- Compatibility conversion to Mathlib's Zariski main property. -/
theorem zariskisMainProperty_of_isQuasiFiniteAtPrime
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S)
    (hq : IsQuasiFiniteAtPrime R S q) : ZariskisMainProperty R q.asIdeal := by
  let p := q.comap (algebraMap R S)
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  have hq' : QuasiFiniteAt R q.asIdeal := by
    apply QuasiFiniteAt.of_isOpen_singleton_fiber q
    rw [← e.isOpen_image, Set.image_singleton]
    exact hq
  exact ZariskisMainProperty.of_finiteType q.asIdeal
end Algebra
