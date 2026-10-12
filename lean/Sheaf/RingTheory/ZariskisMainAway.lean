module

public import Mathlib.RingTheory.ZariskisMainTheorem
public import Sheaf.RingTheory.QuasiFiniteAtPrime

@[expose] public section

universe u v

namespace Algebra

/-! # Zariski's main theorem, integral closure localization
Source: literature/stacks-project/algebra.tex, Algebra, Theorem Tag 00Q9
(blueprint: lem-weil-pbc-integral-closure-zariski-main-away)
-/

/-- Zariski's main theorem for a finite type algebra, at a quasi-finite prime.
(blueprint: lem-weil-pbc-integral-closure-zariski-main-away)
Proof: the fibre-spectrum homeomorphism turns the open singleton in
`IsQuasiFiniteAtPrime` into the open singleton in the topological fibre of
`Spec S → Spec R`. Mathlib's `quasiFiniteAt_iff_isOpen_singleton_fiber` then
supplies `QuasiFiniteAt R q`. Apply `ZariskisMainProperty.of_finiteType`, whose
conclusion unfolds to the required integral element and bijective `awayMap`.
Source: Stacks Tag 00Q9, as formalized in Mathlib.RingTheory.ZariskisMainTheorem.
-/
theorem zariskisMainProperty_of_isQuasiFiniteAtPrime
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime]
    (hq : IsQuasiFiniteAtPrime R S ⟨q, inferInstance⟩) :
    ∃ h : integralClosure R S, h.1 ∉ q ∧
      Function.Bijective (Localization.awayMap (integralClosure R S).val.toRingHom h) := by
  let q' : PrimeSpectrum S := ⟨q, inferInstance⟩
  let p := q'.comap (algebraMap R S)
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  have : QuasiFiniteAt R q := by
    apply (quasiFiniteAt_iff_isOpen_singleton_fiber q').mpr
    rw [← e.isOpen_image, Set.image_singleton]
    exact hq
  exact ZariskisMainProperty.of_finiteType q

end Algebra
