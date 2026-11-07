/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import Submission.WeilConjectures.RingTheory.Depth
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedPrincipalEventualScalarImage

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Finite-level scalar lifts of compatible punctured principal sections

Source: Stacks Project, Tags 0BLD, 0H3E, 0BK0 and 0AVY.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Each member of a compatible formal section family has an ambient scalar lift.

Source: Stacks Project, Tags 0H3E (the pro-isomorphism of cones with ordinary
quotients), 0BLD (degree zero), 0BK0 and 0AVY.
(blueprint: lem-sbc-punctured-principal-finite-level-lift)

Proof: Put U = W, F = O_U and I = (g). Depth three and 0AVY, 0BK0 give
Gamma(U,F) = R by canonical restriction and H^1(U,F) = 0. The annihilators
Ann_R(g^j) stabilize, by Noetherianity; their restrictions are F[g^j].
Use the two-term complexes E_j = [F --g^j--> F], in degrees -1 and 0.
The transition E_(j+1) to E_j is multiplication by g in degree -1 and the
identity in degree 0. Their maps to F/g^j F have cones F[g^j][2]. Once the
annihilators stabilize at c, a transition across c additional indices on
these error sheaves is multiplication by g^c and is zero. Thus E_j and
F/g^j F are pro-isomorphic, also after derived global sections (0H3E).
The degree-zero cohomology of R Gamma(U,E_j) is R/g^j R, since H^1(U,F)=0.
Consequently the cokernels of R/g^j R to Gamma(U,F/g^j F) form a pro-zero
system. For a fixed n, choose a later m whose cokernel transition to n is
zero. Compatibility says that s_n is the transition image of s_m, so it
belongs to the image of R/g^(n+1) R. Choose a scalar representative a in R.
The open pullback of Spec(R/I^(n+1)) has pushforward structure sheaf
F/g^(n+1)F; naturality of the affine sections isomorphism identifies the
scalar image with the formula below. Only a single finite-level lift is
asserted: these scalar representatives are not asserted to be compatible.
For g=0 or nilpotent g the systems become constant and the same proof applies. -/
theorem punctured_principal_finite_level_lift
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := R) R)
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R) :
    let f := Ideal.Quotient.mk (Ideal.span {g})
    ∀ s : ∀ n : ℕ, Γ(FiniteEtale.Adic.openThickening f W n, ⊤),
      (∀ n, (FiniteEtale.Adic.openThickeningTransition f W n).appTop
        (s (n + 1)) = s n) →
      ∀ n, ∃ a : R,
        ((ΓSpecIso (.of R)).inv ≫
          (FiniteEtale.Adic.openThickeningMap f W n ≫ W.ι).appTop) a = s n := by
  dsimp only
  intro s hs n
  obtain ⟨k, hk⟩ := punctured_principal_eventual_scalar_image R g hg hdepth W hW n
  have hcompat (k : ℕ) :
      puncturedPrincipalSectionRestriction (Ideal.Quotient.mk (Ideal.span {g}))
        W n k (s (n + k)) = s n := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change puncturedPrincipalSectionRestriction (Ideal.Quotient.mk (Ideal.span {g}))
        W n k ((FiniteEtale.Adic.openThickeningTransition
          (Ideal.Quotient.mk (Ideal.span {g})) W (n + k)).appTop
            (s (n + k + 1))) = s n
      rw [hs (n + k)]
      exact ih
  obtain ⟨a, ha⟩ := hk (s (n + k))
  exact ⟨a, ha.trans (hcompat k)⟩

end AlgebraicGeometry.Scheme
