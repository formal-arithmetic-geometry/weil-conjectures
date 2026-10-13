/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import Sheaf.RingTheory.Depth
public import Mathlib.RingTheory.AdicCompletion.Basic

/-! # Scalar formal comparison on a complete local puncture

Source: Stacks Project, Tags 0EII, 0AVY and 0BK0.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Compatible scalar sections on all principal thickenings algebraize uniquely.

Source: Stacks Project, Tag 0EII (Lemma 52.12.7), with M = R and a = m;
Tags 0AVY and 0BK0.
(blueprint: lem-sbc-complete-punctured-principal-formal-sections)

Proof: Depth at least three gives H^i_m(R) = 0 for i = 0, 1, 2 by 0AVY.
The punctured-spectrum exact sequence of 0BK0 identifies Gamma(W,O_W)
with R, and H^1(W,O_W) with H^2_m(R), hence the latter is zero. The ring
R is (g)-adically complete: a (g)-adic Cauchy sequence converges in the
maximal-ideal topology; each power of (g) is closed in a Noetherian complete
local ring, so the limit has the required congruences, and Krull intersection
gives uniqueness. Apply 0EII to R, the ideal m and the module R. Its
annihilation hypotheses hold since H^1_m(R) and H^2_m(R) vanish. It gives
Gamma(W,O_W) isomorphic to the inverse limit of Gamma(W,O_W/g^(n+1)).
The quotient map f has kernel (g), and openThickening f W n is the pullback
of W into Spec(R/(g)^(n+1)). Its structure-sheaf sections are precisely
Gamma(W,O_W/g^(n+1)); openThickeningMap gives reduction and
openThickeningTransition gives the quotient transition. Thus an element of
the inverse limit is exactly the family s with hs below. The comparison
isomorphism gives existence and uniqueness of a with the displayed
reductions. Nilpotent g, g = 0, and empty opens require no cancellation of g. -/
theorem complete_punctured_principal_formal_sections
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := R) R)
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R) :
    let f := Ideal.Quotient.mk (Ideal.span {g})
    ∀ s : ∀ n : ℕ, Γ(FiniteEtale.Adic.openThickening f W n, ⊤),
      (∀ n, (FiniteEtale.Adic.openThickeningTransition f W n).appTop
        (s (n + 1)) = s n) →
      ∃! a : Γ(W.toScheme, ⊤), ∀ n,
        (FiniteEtale.Adic.openThickeningMap f W n).appTop a = s n := by sorry

end AlgebraicGeometry.Scheme
