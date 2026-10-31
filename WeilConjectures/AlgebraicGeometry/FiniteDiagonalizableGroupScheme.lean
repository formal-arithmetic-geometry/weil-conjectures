/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.Algebra.Group.Units.Hom

/-! # Finite diagonalizable group schemes

Source: Milne, Algebraic Groups (2017), Proposition 12.3, Remark 12.6 and Theorem 12.8
(blueprint: def-sfb-finite-diagonalizable-group-scheme).

The character functor defining `D(M)` is used directly, with natural group isomorphisms on
all test schemes. Thus no choice of a Hopf structure or of a representing scheme is needed.
-/

@[expose] public section

universe u

open CategoryTheory MonObj

namespace AlgebraicGeometry

set_option autoImplicit false

/-- A group scheme is finite diagonalizable if its group-valued functor of points is
naturally isomorphic to `T ↦ Hom(M, Γ(T, 𝒪_T)ˣ)` for a finite abelian group `M`.

Source: Milne, Algebraic Groups (2017), Proposition 12.3, Remark 12.6 and Theorem 12.8
(blueprint: def-sfb-finite-diagonalizable-group-scheme). Milne's Proposition 12.3 identifies
this functor with `Spec k[M]`, with comultiplication `e_m ↦ e_m ⊗ e_m`. The group law on `M`
is written multiplicatively here. Naturality on all test schemes specifies an isomorphism
of group schemes, including their infinitesimal points, rather than just geometric points.
Over an algebraically closed field, this is precisely finite multiplicative type. -/
def IsFiniteDiagonalizableGroupScheme {k : Type u} [Field k]
    (G : Over (Spec (.of k))) [GrpObj G] : Prop :=
  ∃ (M : Type u) (_ : CommGroup M) (_ : Finite M),
    ∃ e : ∀ T : Over (Spec (.of k)), (T ⟶ G) ≃* (M →* (Γ(T.left, ⊤))ˣ),
      ∀ (T U : Over (Spec (.of k))) (t : T ⟶ U) (x : U ⟶ G),
        e T (t ≫ x) = (Units.map t.left.appTop.hom.toMonoidHom).comp (e U x)

end AlgebraicGeometry
