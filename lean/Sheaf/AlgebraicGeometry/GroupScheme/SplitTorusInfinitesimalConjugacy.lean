module

public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Infinitesimal conjugacy of split-torus homomorphisms

Source: Conrad, Reductive group schemes, Corollary B.2.6, p.287, and
Remark B.2.4, p.285 (blueprint: lem-sfb-split-torus-infinitesimal-conjugacy).

Reduction is restriction along Spec(A/J) → Spec A. Products and inverses in the
Hom group are the actual group-scheme operations, so the concluding equality is
an equality of morphisms, and holds on points over every test algebra.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- Two split-torus homomorphisms with the same square-zero reduction are conjugate
by a section reducing to the identity. The group need not be connected or reductive,
and neither homomorphism need be injective.

Source: Conrad, Reductive group schemes, Corollary B.2.6, p.287, and
Remark B.2.4, p.285 (blueprint: lem-sfb-split-torus-infinitesimal-conjugacy).

Proof plan:
1. Use lem-sfb-group-space-square-zero-kernel-module to identify the congruence
   kernel M over A with its canonical additive module. Laurent algebras in r and
   2r variables are free, hence flat, over A. Apply
   lem-sfb-smooth-group-congruence-flat-scalar-extension to identify their kernels
   with scalar extensions of M, compatibly with substitution and conjugation.
2. At the universal torus point x put c(x) = f2(x) f1(x)^(-1). Equality modulo J
   places c in the kernel. The homomorphism laws give
   c(xy) = c(x) + rho_x(c(y)), where rho_x is conjugation by f1(x).
3. Write c(y) as a finite Laurent sum and let p be its constant coefficient.
   Compare coefficients of y^0 in the cocycle identity. Linearity of rho_x and
   naturality under Laurent substitution give p = c(x) + rho_x(p).
4. Regard p as a section u reducing to 1. The equation c(x) = p - rho_x(p)
   gives f2(x) = u f1(x) u^(-1). By def-weil-affine-spectrum, equality at the
   universal point gives equality of the scheme morphisms. The same calculation
   covers r = 0; for J = 0 take u = 1. No division or finiteness of J is used. -/
theorem splitTorus_infinitesimal_conjugacy
    (A : Type u) [CommRing A] (J : Ideal A) (_hJ : J ^ 2 = ⊥)
    (G : Over (Spec (.of A))) [GrpObj G] [Smooth G.hom] [IsAffineHom G.hom]
    [LocallyOfFinitePresentation G.hom] (r : ℕ)
    (f₁ f₂ : (RingGroupSchemes.splitTorus A r).X ⟶ G) [IsMonHom f₁] [IsMonHom f₂]
    (hmod :
      pullback.fst (RingGroupSchemes.splitTorus A r).X.hom
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ≫ f₁.left =
        pullback.fst (RingGroupSchemes.splitTorus A r).X.hom
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ≫ f₂.left) :
    ∃ u : Over.mk (𝟙 (Spec (.of A))) ⟶ G,
      Over.homMk (V := Over.mk (𝟙 (Spec (.of A))))
          (U := Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ≫ u = 1 ∧
      (Over.homMk (V := Over.mk (𝟙 (Spec (.of A))))
          (U := (RingGroupSchemes.splitTorus A r).X)
          (RingGroupSchemes.splitTorus A r).X.hom ≫ u) * f₁ *
        (Over.homMk (V := Over.mk (𝟙 (Spec (.of A))))
          (U := (RingGroupSchemes.splitTorus A r).X)
          (RingGroupSchemes.splitTorus A r).X.hom ≫ u)⁻¹ = f₂ := by
  sorry

end AlgebraicGeometry
