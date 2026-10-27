/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import WeilConjectures.Mathlib.RingTheory.Henselian

/-! # Simple-root approximation over a dense subfield

Source: ILO, Travaux de Gabber, XX 4.4, printed p.374, Krasner argument.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

namespace FieldTheory

/-- Every element of a separable closure of a henselian valued field L lies in
L(b) for a simple root b of a monic polynomial over a given dense subfield K.
No henselianity is required of K, and no separable closure of K is chosen.
Source: ILO, Travaux de Gabber, XX 4.4, printed p.374, the coefficient-approximation
part of the Krasner argument (blueprint: lem-per-dense-henselian-simple-root-approximation).

Proof: Choose a finite Galois extension N/L in Ls containing a, and prolong the
valuation of L to N by lem-per-henselian-finite-extension-topology. Its valuation
ring is henselian and the induced topology on L is the given one. The minimal
polynomial f of a over L is monic, has positive degree, and is separable; a Bezout
identity for f and its derivative shows that f'(a) is nonzero. Choose an open
Krasner neighbourhood U of a in N using lem-per-henselian-krasner-neighbourhood.
Apply lem-per-henselian-simple-root-stability to f over N and U. It supplies an
open neighbourhood V of the finite coefficient tuple of f such that every monic
polynomial with coefficients in V has a simple root b in U. Pull V back to the
finite product of copies of L. This is an open neighbourhood of the coefficient
tuple because the prolonged topology induces the topology on L. Density of K
in L, applied to a product-basic neighbourhood contained in this preimage,
chooses every coefficient in K. Let g be the resulting monic polynomial over K.
Simple-root stability supplies b in N with g(b)=0 and g'(b) nonzero. Since b is
in U, Krasner gives a in L(b). Embed N in Ls to obtain the stated root and field
containment. All coefficient choices are finite, so the argument works for any
valuation rank, in positive characteristic, and for a already in L (where one
can also take b=a only if a lies in K; the approximation argument still applies).
In the special case a in K one may simply use g=X-a and b=a. -/
theorem denseHenselian_exists_simple_root
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (Γ : Type v) (Δ : Type w)
    [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
    [vK : Valued K Γ] [vL : Valued L Δ]
    [vK.v.IsNontrivial] [vL.v.IsNontrivial]
    [HenselianLocalRing vL.v.valuationSubring]
    (h_induced : Topology.IsInducing (algebraMap K L))
    (h_dense : DenseRange (algebraMap K L))
    (Ls : Type t) [Field Ls] [Algebra L Ls] [IsSepClosure L Ls]
    [Algebra K Ls] [IsScalarTower K L Ls] (a : Ls) :
    ∃ (g : Polynomial K) (b : Ls), g.Monic ∧
      Polynomial.aeval b g = 0 ∧ Polynomial.aeval b g.derivative ≠ 0 ∧
      a ∈ IntermediateField.adjoin L {b} := by sorry

end FieldTheory
