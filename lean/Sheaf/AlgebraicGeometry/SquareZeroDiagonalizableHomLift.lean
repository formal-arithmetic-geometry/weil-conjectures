module

public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.GroupTheory.Finiteness

/-! # Square-zero lifting of diagonalizable group homomorphisms

Source: Conrad, Reductive group schemes (2014), Corollary B.2.6 and Remark B.2.4,
printed pp.285--287 (blueprint: lem-sfb-square-zero-diagonalizable-hom-lift).

Group schemes and their homomorphisms are the existing group objects in the category of
schemes over Spec A. Reduction uses the group-object base-change functor. The reduction of
D_A(M) is canonically D_(A/J)(M), since (A/J) tensor_A A[M] = (A/J)[M], with the same
basis and Hopf formulas. Thus a homomorphism from D_(A/J)(M) is represented below on this
chosen pullback, with no additional comparison datum or hypothesis.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every homomorphism from a split diagonalizable group into a smooth affine group
lifts across a square-zero ideal.

Source: Conrad, Reductive group schemes (2014), Corollary B.2.6 and Remark B.2.4,
printed pp.285--287 (blueprint: lem-sfb-square-zero-diagonalizable-hom-lift).

Proof, following the four-step DAG split:
1. Put H = D_A(M) and C = A[M]. Reduction of the basis and Hopf operations identifies
   H_0 with D_(A/J)(M). The ideal JC is square-zero. Smoothness of G supplies an
   S-scheme map f : H → G lifting u_0 (def-sbc-smooth-morphisms). The algebra C and
   all its tensor powers are free on tuples of characters, hence flat over A,
   including when M has torsion.
2. Apply lem-sfb-square-zero-hom-regular-defect to f. The module
   E = Lie(G_0) tensor_(A/J) J has its H_0-coaction, and the regular multiplicativity
   defect c_f in E tensor_(A/J) (A/J)[M] tensor_(A/J) (A/J)[M] is a regular
   two-cocycle. This is an identity of regular cochains over the universal triple,
   valid also over nonreduced bases.
3. Lem-sfb-diagonalizable-regular-two-cocycle gives a regular one-cochain b with
   c_f(h,k) = h.b(k) - b(hk) + b(h). The correction clause of
   lem-sfb-square-zero-hom-regular-defect gives u = b_tilde f with the same reduction
   u_0 and defect c_u = c_f - db = 0. Thus u preserves multiplication.
4. Multiplicativity at the universal identity gives u(1) = u(1)^2, hence u(1) = 1
   in the group G(A). At the universal H-point over C it gives
   u(h)u(h^-1) = 1 = u(h^-1)u(h), so uniqueness of inverses gives preservation of
   inverse. These universal-point equalities are identities of scheme morphisms.
   Therefore u is a group-scheme homomorphism reducing exactly to u_0. -/
theorem squareZero_diagonalizable_hom_lift
    (A : Type u) [CommRing A] (J : Ideal A) (hJ : J ^ 2 = ⊥)
    (M : Type u) [AddCommGroup M] [AddGroup.FG M]
    (G : Grp (Over (Spec (.of A)))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (u₀ : (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).mapGrp.obj
        (ringDiagonalizableGroup A M) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).mapGrp.obj G) :
    ∃ u : ringDiagonalizableGroup A M ⟶ G,
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).mapGrp.map u = u₀ := by
  sorry

end AlgebraicGeometry
