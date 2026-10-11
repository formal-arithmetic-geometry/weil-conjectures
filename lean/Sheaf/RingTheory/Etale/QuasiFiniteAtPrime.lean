/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.RingTheory.QuasiFiniteAtPrime

/-!
# Étale ring maps are quasi-finite at every prime

Source: Stacks Project, Algebra, Lemma 10.143.6 (Tag 00U5)
(blueprint: lem-weil-pbc-etale-ring-map-quasi-finite).
-/

universe u

namespace Algebra

/-- (blueprint: lem-weil-pbc-etale-ring-map-quasi-finite) If the morphism of affine
schemes induced by a ring map is étale, its target algebra is finitely generated and
it is quasi-finite at every prime (Stacks Project, Algebra, Tag 00U5).

Proof:
1. By `lem-weil-pbc-etale-ring-map-iff-etale-affine`, the ring map is étale and hence
   finitely presented. The images of its finitely many polynomial generators generate
   the algebra, giving finite type (`def-weil-pbc-mv-polynomial-ring`).
2. For a prime `q` of `S`, contract it to `p` in `R`. By
   `lem-weil-pbc-etale-ring-base-change`, the fibre over the residue field of `p` is
   étale over that field (`def-weil-pbc-localization-at-prime`).
3. By `lem-weil-pbc-etale-algebra-over-field-product`, this fibre is a finite product
   of finite separable field extensions. The tensor swap identifies the two orders
   of the fibre tensor product. By `lem-weil-pbc-spec-finite-product-fields`, its
   spectrum is discrete, so every singleton is open.
4. By `lem-weil-pbc-fibre-ring-primes-bijection`, `q` corresponds to a unique prime
   of the fibre. Its singleton is open by step 3. Together with finite type from
   step 1, this is `def-weil-pbc-ring-map-quasi-finite-at-prime`. Since `q` was
   arbitrary, the assertion holds at every prime of `S`.

The finite-type witness is part of the conclusion, and supplies the instance
required by the existing isolated-point definition. -/
theorem finiteType_and_isQuasiFiniteAtPrime_of_etale
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (h : AlgebraicGeometry.Etale
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    ∃ hft : Algebra.FiniteType R S,
      letI := hft
      ∀ q : PrimeSpectrum S, Algebra.IsQuasiFiniteAtPrime R S q := by
  sorry

end Algebra
