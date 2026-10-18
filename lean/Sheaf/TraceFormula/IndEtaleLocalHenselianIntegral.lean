/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q132
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.RingTheory.ProEtale.IndEtale
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Sheaf.RingTheory.HenselizationAtPrime

/-!
# Integrality of a local henselian ind-etale algebra

Source: algebraic tame site paper, sentence between Theorems 6.3 and 6.4, printed p. 13;
Stacks Project, Algebra, Tags 04GN and 04GQ (blueprint: lem-trf-ind-etale-local-henselian-integral).
-/

@[expose] public section

universe u

namespace RingHom

/-- Let `f : A → D` be ind-etale with `D` henselian local. At the contraction `p` of the
maximal ideal, every henselization `H` of `Aₚ` admits the canonical local factorization
through `D`, and `D` is integral over `H`. The proof follows the filtered etale
presentation, henselian finite-type product decomposition, exclusion of the residual
factor, and finite-algebra integrality described in the node proof.
(blueprint: lem-trf-ind-etale-local-henselian-integral) -/
theorem indEtale_local_henselian_integral
    (A D : Type u) [CommRing A] [CommRing D]
    (f : A →+* D) [HenselianLocalRing D] (hind : f.IndEtale)
    (p : Ideal A) (hp : p = Ideal.comap f (IsLocalRing.maximalIdeal D))
    [p.IsPrime] (H : Type u) [CommRing H]
    [Algebra (Localization.AtPrime p) H] [HenselianLocalRing H]
    (hH : Algebra.IsHenselizationAtPrime A p H) :
    ∃! h : H →+* D,
      IsLocalHom h ∧
        h.comp ((algebraMap (Localization.AtPrime p) H).comp
          (algebraMap A (Localization.AtPrime p))) = f ∧
        RingHom.IsIntegral h := by
  sorry

end RingHom
