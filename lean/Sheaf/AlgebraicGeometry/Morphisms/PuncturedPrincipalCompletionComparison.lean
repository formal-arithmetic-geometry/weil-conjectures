/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import Sheaf.RingTheory.Depth
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Formal sections as an element of the principal adic completion

Source: Stacks Project, Tags 0BLD, 0AVY and 0BK0.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- On a depth-three puncture, formal sections determine an element of the
principal adic completion, even when the local ring is not complete.

Source: Stacks Project, Tag 0BLD (Lemma 52.3.2, p = 0), as used in Tag 0EII;
Tags 0AVY and 0BK0.
(blueprint: lem-sbc-punctured-principal-completion-comparison)

Proof: Write I = (g), X = Spec R and U = X minus the closed point.
Depth at least three makes H^i_m(R) vanish for i = 0, 1, 2 (0AVY).
The exact sequence of 0BK0 therefore identifies R with Gamma(U,O_U),
by the canonical restriction map, and identifies H^1(U,O_U) with zero.
The kernels of multiplication by successive powers of g on O_U stabilize:
they are restrictions of the ascending annihilator ideals of g^n in R,
which stabilize because R is Noetherian. Apply 0BLD with F = O_U and p = 0.
Its top exact row identifies the ordinary I-adic completion of Gamma(U,O_U)
with lim Gamma(U,O_U/g^n), since the Tate module of H^1(U,O_U) is zero.
Through the canonical identification Gamma(U,O_U) = R, this is AdicCompletion I R.
The kernel of R -> R/(g) is I. The pullback defining openThickening is the open
subscheme of Spec(R/I^(n+1)) over U. Pushforward along this closed immersion
identifies its structure sheaf with O_U/g^(n+1)O_U. Its sections therefore
are the terms in the preceding inverse limit. The quotient transition maps
are openThickeningTransition, by the pullback identities. The comparison
from the completion is obtained by evaluating at n+1, using Gamma(Spec R/I^(n+1))
= R/I^(n+1), and restricting along pullback.snd. This gives exactly the formula
below. Omitting index zero does not change the limit, since R/I^0 is zero.
Existence and uniqueness now follow from the comparison isomorphism.
For g=0 the system is constant; for nilpotent g it is eventually constant.
No regularity of g or completeness of R is required. -/
theorem punctured_principal_completion_comparison
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := R) R)
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R) :
    let f := Ideal.Quotient.mk (Ideal.span {g})
    let I := RingHom.ker f
    ∀ s : ∀ n : ℕ, Γ(FiniteEtale.Adic.openThickening f W n, ⊤),
      (∀ n, (FiniteEtale.Adic.openThickeningTransition f W n).appTop
        (s (n + 1)) = s n) →
      ∃! q : AdicCompletion I R, ∀ n,
        ((ΓSpecIso (.of (R ⧸ I ^ (n + 1)))).inv ≫
          (pullback.snd W.ι (FiniteEtale.Adic.baseMap f n)).appTop)
            (AdicCompletion.evalₐ I (n + 1) q) = s n := by sorry

end AlgebraicGeometry.Scheme
