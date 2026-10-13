/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.JapaneseDomain
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.RingTheory.DimOneResidueFieldsFinite

/-!
# Finiteness of the quotient by a root of the parameter

Source: Stacks Project, Algebra, Tag 032P (lemma-tate-japanese), the residue-field argument.
(blueprint: lem-weil-pbc-tate-root-closure-quotient-finite).
-/

@[expose] public section

universe u v

set_option autoImplicit false

/-- The quotient by a root of the prime parameter is finite.
Source: Stacks Project, Algebra, Tag 032P (lemma-tate-japanese), from the description
of the prime over `xR` through the finiteness of `S/yS`.
(blueprint: lem-weil-pbc-tate-root-closure-quotient-finite).

Proof: If x = 0, positivity of p^e gives y = 0. Transport the N-2 condition
along R/(0) = R and the unique equivalence of fraction fields; apply it to L.
For different universes replace the finite-dimensional extension by a small
isomorphic field, using a finite basis. Thus S itself is finite in this case.
Otherwise x and y are nonzero. For a in S, the common-power hypothesis puts
its p^e-th power in K, and integrality and normality put this power in R.
The ideal yS consists exactly of the a for which a^(p^e) lies in xR:
if a^(p^e) = xr, then (a/y)^(p^e) = r, so a/y is integral over R.
This description shows yS is prime and its contraction is xR. Localizing R
at xR gives a one-dimensional Noetherian local domain, by the principal
ideal height theorem and the nonzero chain (0) < xR. Apply Tag 031F to
R_(xR) -> S_(yS), whose fraction fields are K and L, to obtain finiteness
of kappa(yS) over kappa(xR). The latter is a fraction field of R/xR.
N-2, transported to this fraction field and a small isomorphic copy of the
finite residue extension if necessary, makes its integral closure finite.
Reducing integral equations embeds S/yS into that closure. Since R/xR is
Noetherian, this submodule is finite. Restrict scalars along the finite
quotient map R -> R/xR to obtain the assertion. -/
theorem tate_root_closure_quotient_finite
    (R : Type u) (K L : Type v) [CommRing R] [IsDomain R]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [IsNoetherianRing R] (x : R) (hnormal : IsIntegrallyClosed R)
    (p : ℕ) [Fact p.Prime] [CharP K p] [FiniteDimensional K L]
    [IsDomain (R ⧸ Ideal.span ({x} : Set R))]
    (hquot : IsN2 (R ⧸ Ideal.span ({x} : Set R))
      (FractionRing (R ⧸ Ideal.span ({x} : Set R))))
    (e : ℕ) (hpow : ∀ a : L, a ^ (p ^ e) ∈ (algebraMap K L).range)
    (y : integralClosure R L)
    (hy : y ^ (p ^ e) = algebraMap R (integralClosure R L) x) :
    Module.Finite R ((integralClosure R L) ⧸ Ideal.span ({y} : Set (integralClosure R L))) := by
  sorry
