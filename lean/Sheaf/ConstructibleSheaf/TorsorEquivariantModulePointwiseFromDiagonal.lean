/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.ConstructibleSheaf.TorsorAssociatedModule


@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.GaloisCover

/-- A uniform linear formula on diagonal values over the torsor propagates to
all etale objects by naturality. Connectedness is not needed for propagation.
Source: Stacks Project, etale-cohomology.tex Tags 0DV5 (3), 0DV6 (context);
sites.tex Tags 04TR and 04TS (descent context).
(blueprint: lem-weil-pbc-torsor-equivariant-module-pointwise-from-diagonal)

Proof: Fix W, s and a point x of T = W times_V c.P. Regard T as an etale
object over V, with its map to c.P. Let O be the open fibre of the locally
constant function s through x, and let n = s(x). The graph of O to c.P is a
section of the torsor over O. Trivialization by this graph identifies its total
space with copies of O indexed by P. Extend the constant diagonal value n to
an equivariant section q over the torsor object by assigning rho(g)n on the
g-th translate of the diagonal. Restrict q along O to c.P. It agrees with the
restriction of s along O to W: their graph values are n, and equivariance
determines their values on every translate. Naturality of eta along these two
maps gives agreement of the transformed sections on O. Evaluate at the graph
point over x. Its restriction to W is the original point x, while its restriction
to c.P is the diagonal at the second projection of x. The assumed diagonal
formula for q at that point makes this transformed value f(n). Consequently
eta(s)(x)=f(s(x)). Since x was arbitrary the formula holds everywhere.
No choice of geometric points or lifts is needed. Empty W gives a vacuous
pointwise conclusion, and the trivial group and zero coefficients satisfy the
same calculation. -/
theorem equivariantModulePresheaf_pointwise_of_diagonal
    {V : Scheme.{u}} (ℓ : ℕ) {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V)
    (N N' : Rep.{u + 1} (ZMod ℓ) P)
    (η : c.equivariantModulePresheaf ℓ N ⟶ c.equivariantModulePresheaf ℓ N')
    (f : N.V →ₗ[ZMod ℓ] N'.V)
    (hf : letI := c.etale
      ∀ (s : c.equivariantSections ℓ N (Etale.mk c.π)) (x : c.P),
        (η.app (op (Etale.mk c.π)) s).val
            ((pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) rfl) x) =
          f (s.val ((pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) rfl) x))) :
    ∀ (W : V.Etale) (s : c.equivariantSections ℓ N W) (x : c.sectionSpace W),
      (η.app (op W) s).val x = f (s.val x) := by sorry

end AlgebraicGeometry.Scheme.GaloisCover
