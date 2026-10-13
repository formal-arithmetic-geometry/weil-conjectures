/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import Sheaf.RingTheory.Depth

/-! # Eventual vanishing of scalar restriction kernels on principal punctures

Source: Stacks Project, Tags 0H3E, 0BLD, 0BK0 and 0AVY.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A scalar vanishing on a sufficiently deep punctured thickening lies in a
prescribed power of the principal ideal.

Source: Stacks Project, Tag 0H3E (the pro-isomorphism preceding the displayed
diagram), and Tags 0BLD, 0BK0 and 0AVY.
(blueprint: lem-sbc-punctured-principal-restriction-kernel)

Proof: Set F = O_W and I = (g) = ker(R to R/(g)). Depth three gives
Gamma(W,F)=R by canonical restriction and H^1(W,F)=0, using 0AVY and 0BK0.
Choose c with Ann(g^j)=Ann(g^c) for j at least c. Form E_j=[F --g^j--> F]
in degrees -1 and 0, with transition multiplication by g in degree -1.
The natural map E_j to F/g^j F has cone F[g^j][2]. The error-system
transition across c indices is zero, because g^c annihilates its stabilized
sheaf. This is the pro-isomorphism of 0H3E. Apply derived global sections
and degree-zero cohomology; pro-zero systems remain pro-zero under these
operations, and the kernel of the induced comparison is pro-zero.
Since H^1(W,F)=0, the cone cohomology in degree zero is R/g^j R, with its
usual quotient transitions. Hence for each n there is m at least n such
that the kernel of R/I^(m+1) to Gamma(W,F/g^(m+1)F) maps to zero in
R/I^(n+1). The pullback description of openThickening and the canonical
GammaSpecIso identify its scalar comparison with the displayed formula.
Apply this kernel assertion to the class of a-b when their restricted
images agree. Its class at level n is zero exactly when a-b belongs to
I^(n+1). This does not assert injectivity at any individual level.
The zero and nilpotent principal generators are included: stabilization
still holds, and the scalar comparison is eventually ordinary Hartogs. -/
theorem punctured_principal_restriction_kernel
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := R) R)
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R) :
    let f := Ideal.Quotient.mk (Ideal.span {g})
    let I := RingHom.ker f
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∀ a b : R,
      ((ΓSpecIso (.of R)).inv ≫
        (FiniteEtale.Adic.openThickeningMap f W m ≫ W.ι).appTop) a =
      ((ΓSpecIso (.of R)).inv ≫
        (FiniteEtale.Adic.openThickeningMap f W m ≫ W.ι).appTop) b →
      a - b ∈ I ^ (n + 1) := by sorry

end AlgebraicGeometry.Scheme
