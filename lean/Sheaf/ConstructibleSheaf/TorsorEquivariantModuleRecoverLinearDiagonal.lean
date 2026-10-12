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

/-- Recover a unique linear map from the diagonal values of the component of eta
at the torsor object. No formula on arbitrary etale objects is asserted here.
Source: Stacks Project, etale-cohomology.tex Tags 0DV5 (3) and 0DV6 (context).
(blueprint: lem-weil-pbc-torsor-equivariant-module-recover-linear-diagonal)

Proof: The torsor isomorphism, with its factors interchanged, identifies
c.P times_V c.P with copies of c.P indexed by g in P. On the g-th copy a section
has the value rho(g) applied to its value on the diagonal. Thus restriction to
the diagonal determines an equivariant section. Conversely any locally constant
function t on c.P extends on the g-th copy with value rho(g)t. This extension
is locally constant because the copies are open, and equivariance follows from
rho(hg)=rho(h)rho(g). The restriction and extension operations are linear and
inverse. Every locally constant function on the connected nonempty space c.P
is constant, so diagonal evaluation gives a linear isomorphism from these sections
to N, and likewise to N'. Conjugate the linear component eta at Etale.mk c.pi
by these two isomorphisms to obtain f. At each point x the diagonal evaluations
are the same constants, so the asserted formula holds for every s and x.
For uniqueness fix one x, which exists by connectedness. For every n, extend
the constant diagonal function with value n; evaluating the formulas for two
candidate maps on this section at x shows equality at n. Linear extensionality
then gives equality of the maps. The zero module and trivial group work with
the same construction; ell need not be prime or positive. -/
theorem equivariantModulePresheaf_recoverLinear_diagonal
    {V : Scheme.{u}} (ℓ : ℕ) {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (N N' : Rep.{u + 1} (ZMod ℓ) P)
    (η : c.equivariantModulePresheaf ℓ N ⟶ c.equivariantModulePresheaf ℓ N') :
    letI := c.etale
    ∃! f : N.V →ₗ[ZMod ℓ] N'.V,
      ∀ (s : c.equivariantSections ℓ N (Etale.mk c.π)) (x : c.P),
        (η.app (op (Etale.mk c.π)) s).val
            ((pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) rfl) x) =
          f (s.val ((pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) rfl) x)) := by sorry

end AlgebraicGeometry.Scheme.GaloisCover
