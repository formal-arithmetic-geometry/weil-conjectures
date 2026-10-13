/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.JapaneseDomain
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
import Sheaf.RingTheory.DimOneResidueFieldsFinite

/-!
# The closed fibre of a purely inseparable integral closure

Source: Stacks Project, Algebra, Tag 032P (lemma-tate-japanese).
(blueprint: lem-weil-pbc-tate-purely-inseparable-closure-quotient-finite).
-/

@[expose] public section

universe u v

set_option autoImplicit false

/-- The reduction of a purely inseparable integral closure modulo a prime principal
ideal is finite. Source: Stacks Project, Algebra, Tag 032P (lemma-tate-japanese),
proof before the application of Tag 031D.
(blueprint: lem-weil-pbc-tate-purely-inseparable-closure-quotient-finite).

Proof:
If x = 0, R/xR is R; transport its N-2 hypothesis to its fraction field K and
apply it to L. Assume x is nonzero. Choose a common exponent q = p^e by taking
the maximum of exponents for a finite K-basis of L. Adjoin a q-th root y of x
inside an algebraic closure to get a finite extension L'/K with (L')^q in K.
The integral closure S in L embeds in the closure T in L'. For every a in T,
a^q belongs to R by normality. Also xT intersect R equals xR, by dividing
by the nonzero x in K and using normality. More generally S intersect xT = xS:
if a = xb in T and a is in L, then b = a/x is in L and integral over R.
Consequently S/xS injects R-linearly into T/xT. Since R is Noetherian, it
suffices to prove that T/xT is finite.

The root y is integral over R. The ideal yT consists exactly of those a in T
with a^q in xR: the converse follows because (a/y)^q belongs to R and hence
a/y is integral. This makes yT a prime lying over xR. Localize at xR; the
principal-ideal height bound gives a one-dimensional Noetherian local domain.
Tag 031F (lem-weil-pbc-dim-one-residue-field-extensions-finite) gives a finite
extension of residue fields at yT over xR. Its base is the fraction field of
R/xR. Every element of T/yT is integral over R/xR and this domain embeds in
the residue field at yT. Thus it embeds in the integral closure of R/xR in
that finite field extension. N-2 makes this latter closure finite, and
Noetherianity makes T/yT finite. Multiplication by y^i identifies T/yT with
y^i T/y^(i+1) T, because T is a domain and y is nonzero. The finite filtration
therefore makes T/y^q T = T/xT finite over R. The injection above gives
finiteness of S/xS over R. Its action factors through R/xR, so it is finite
over that quotient as asserted. No completeness assumption is needed. -/
theorem tate_purely_inseparable_closure_quotient_finite
    (R : Type u) (K L : Type v) [CommRing R] [IsDomain R]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [IsNoetherianRing R] (x : R) (hnormal : IsIntegrallyClosed R)
    (p : ℕ) [Fact p.Prime] [CharP K p] [FiniteDimensional K L]
    [IsPurelyInseparable K L]
    [IsDomain (R ⧸ Ideal.span ({x} : Set R))]
    (hquot : IsN2 (R ⧸ Ideal.span ({x} : Set R))
      (FractionRing (R ⧸ Ideal.span ({x} : Set R)))) :
    Module.Finite (R ⧸ Ideal.span ({x} : Set R))
      ((integralClosure R L) ⧸
        (Ideal.span ({x} : Set R) • ⊤ : Submodule R (integralClosure R L))) := by
  sorry
