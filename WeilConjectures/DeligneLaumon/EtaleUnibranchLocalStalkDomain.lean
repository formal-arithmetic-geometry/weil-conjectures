/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Topology.Irreducible
public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn

/-! # Etale local stalks over geometrically unibranch points are domains

Source: Stacks Project, `more-algebra.tex`, Tag 0GSC, proof, reduction paragraph,
using branch invariance Tag 0DQ1 and the one-branch characterization Tag 0C37
(blueprint: lem-dl-a1-etale-unibranch-local-stalk-domain).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The localization of an etale algebra at a prime over a geometrically unibranch
localization of a domain is an integral domain.

Source: Stacks Project, `more-algebra.tex`, Tag 0GSC, proof, reduction paragraph,
using branch invariance Tag 0DQ1 and the one-branch characterization Tag 0C37
(blueprint: lem-dl-a1-etale-unibranch-local-stalk-domain).

Proof (the two proof steps of the DAG node):
1. Apply `lem-dl-a1-smooth-geounibranch-local` to `A → C`, the prime `Q`, and
   its inverse image `p`. The geometric-unibranch hypothesis on `Aₚ` is precisely
   the stated strict-henselization irreducibility condition, so `C_Q` is
   geometrically unibranch.
2. By `lem-dl-a1-etale-generic-reduced-components`, `C` is reduced. Localization
   preserves reducedness: if `(x/s)^n = 0`, there is `t ∉ Q` with `t * x^n = 0`.
   For positive `n`, this gives `(t * x)^n = 0`, hence `t * x = 0` by reducedness,
   and therefore `x/s = 0`. The zero exponent would imply `1 = 0` in the nonzero
   prime localization, so cannot occur. Thus `C_Q` is reduced, and
   `lem-dl-a1-reduced-geounibranch-local-domain` gives the asserted domainhood.
-/
theorem etale_unibranch_local_stalk_domain
    (A C : Type u) [CommRing A] [IsDomain A] [CommRing C] [Algebra A C]
    (hEtale : Etale
      (Spec.map (CommRingCat.ofHom (algebraMap A C))))
    (Q : Ideal C) [Q.IsPrime]
    (p : Ideal A) [p.IsPrime]
    (hp : Q.comap (algebraMap A C) = p)
    (hgeom : ∀ (K H : Type (max u v)) [Field K]
      [Algebra (IsLocalRing.ResidueField (Localization.AtPrime p)) K]
      [IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime p)) K]
      [Algebra (Localization.AtPrime p) K]
      [IsScalarTower (Localization.AtPrime p)
        (IsLocalRing.ResidueField (Localization.AtPrime p)) K]
      [CommRing H] [Algebra (Localization.AtPrime p) H],
      Algebra.StrictHenselizationPresentationIn.{u, v}
          (Localization.AtPrime p) K H →
        IrreducibleSpace (PrimeSpectrum H)) :
    IsDomain (Localization.AtPrime Q) := by
  sorry

end AlgebraicGeometry
