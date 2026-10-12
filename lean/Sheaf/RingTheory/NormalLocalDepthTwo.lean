/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.RingTheory.Depth
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.RingTheory.KollarLocalDichotomy
import Sheaf.RingTheory.NonzerodivisorIfMaximalNotAssociated

/-!
# Depth of a normal local domain in dimension at least two

Source: Stacks Project, Algebra, Tag 031S, forward implication, second paragraph.
(blueprint: lem-weil-pbc-normal-local-depth-two).
-/

@[expose] public section

universe u

/-- A Noetherian normal local domain of dimension at least two has depth at least two.
Source: Stacks Project, Algebra, Tag 031S, forward implication, second paragraph
(blueprint: lem-weil-pbc-normal-local-depth-two).

Proof: Apply Kollár's local dichotomy (Tag 0BHZ). The Artinian case has dimension zero,
and the regular dimension-one case is excluded by the dimension bound. In the finite
extension case A → B, a power of the maximal ideal kills the kernel. The maximal ideal
contains a nonzero element, so the domain property forces the kernel to vanish. Tag 00LL
provides x in the maximal ideal acting injectively on B. If its nth power kills B/A,
embed B in Frac(A) by sending y to (x^n y)/x^n. This is an injective A-algebra map:
cross-multiplication verifies multiplication, and x^n is regular. Every element of B
is integral because B is finite over A. Integral closedness therefore puts its image
in A. Injectivity makes A → B surjective, contradicting the extension case. Thus the
remaining case of the dichotomy gives depth at least two. -/
theorem IsLocalRing.depth_two_of_normal (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A) :
    (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A := by sorry
