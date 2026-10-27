module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Spectrum.Prime.Defs

import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes

/-!
# Recovery of a flatly extended primary ideal on its radical fibre

Source: Stacks Project, Algebra, Tags 0312 (`lemma-bourbaki`) and 0311
(`lemma-zero-at-ass-zero`), specialized to a primary quotient
(blueprint: lem-per-flat-primary-fibre-recovery).
-/

@[expose] public section

universe u v

namespace Ideal

/-- A primary ideal extended along a flat map of Noetherian rings is recovered by contracting
its extensions to every prime localization above its radical. The intersection is `⊤` when
there is no such prime. Faithful flatness and reducedness of the radical fibre are not assumed.

Source: Stacks Project, Algebra, Tags 0312 (`lemma-bourbaki`) and 0311
(`lemma-zero-at-ass-zero`), applied to `S / qS`
(blueprint: lem-per-flat-primary-fibre-recovery).

Proof:
1. For `a` outside `q.radical`, multiplication by `a` on `R / q` is injective: if
   `a * b ∈ q` and `b ∉ q`, primaryness forces a positive power of `a` into `q`, a contradiction.
2. Tensor this injection with the flat module `S`, using
   `lem-weil-pbc-flat-tensor-exact`. The canonical quotient-tensor identification in
   `lem-weil-pbc-tensor-over-quotient-ring` identifies this tensor map with multiplication by
   `f a` on `M = S / qS`, so that multiplication is injective.
3. If `Q` is an associated prime of `M`, write `Q = Ann(z)` with `z ≠ 0`.
   The ideal `qS` kills `M`, so `q.radical` is contained in the contraction of `Q`.
   Conversely, Step 2 shows that no `f a` with `a` outside `q.radical` kills `z`.
   Hence the contraction is exactly `q.radical`.
4. The inclusion from left to right follows from extension. If `x` belongs to the right
   side, its localization at each associated prime `Q` belongs to the extended ideal.
   Write it as `y / t` with `y ∈ qS` and `t ∉ Q`. The fraction equality gives `u ∉ Q`
   with `u * (t * x - y) = 0`, so `u * t` lies outside `Q` and kills the class of `x` in `M`.
   This uses the fraction construction in `def-weil-pbc-localization-at-prime`.
5. Apply the annihilator criterion of
   `lem-weil-pbc-module-injects-localizations-associated-primes`, using that `S` is Noetherian.
   It makes the class of `x` zero and therefore puts `x` in `qS`. If the fibre is empty,
   Step 3 gives no associated primes and the same criterion gives `M = 0`, hence `qS = S`.
-/
theorem flat_primary_map_eq_iInf_comap_localization
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (hf : f.Flat) (q : Ideal R) (hq : q.IsPrimary) :
    q.map f =
      ⨅ (Q : PrimeSpectrum S) (_ : Q.asIdeal.comap f = q.radical),
        Ideal.comap (algebraMap S (Localization.AtPrime Q.asIdeal))
          (q.map ((algebraMap S (Localization.AtPrime Q.asIdeal)).comp f)) := by
  sorry

end Ideal
