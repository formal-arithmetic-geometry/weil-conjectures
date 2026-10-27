/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q155
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Nilpotent adjoint operators detect nilpotent connected groups

Source: Milne, Algebraic Groups (2017), Proposition 17.80 proof, p.378, read with
Proposition 17.74, Proposition 10.15, and Proposition 6.38
(blueprint: lem-sfb-charzero-ad-nilpotence-group-criterion).

The canonical `GrpObj.Lie` is the identity tangent space, represented by dual-number
points through `GrpObj.lieEquivTangent`; its bracket is the mixed infinitesimal commutator.
The conclusion records closed normal subgroup schemes and tests the central-series
condition on all commutative algebras, including nonreduced algebras.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- In characteristic zero, nilpotence of every adjoint Lie endomorphism forces a smooth
connected affine group of finite type to admit a finite descending central series.
Source: Milne, Proposition 17.80 proof, p.378, Proposition 17.74, p.377,
Proposition 10.15, p.190, and Proposition 6.38, p.133
(blueprint: lem-sfb-charzero-ad-nilpotence-group-criterion).

Proof:
1. The adjoint-differential lemma
   lem-sfb-charzero-adjoint-differential-central-kernel makes Lie(G) finite dimensional
   and identifies dAd with ad. Apply lem-sfb-noetherian-lie-engel-criterion (Mathlib's
   LieAlgebra.isNilpotent_iff_forall) to obtain a lower central series C with C^d = 0;
   increase d to be at least one.
2. Let J consist of endomorphisms lowering C by one step. It is closed under composition,
   and J^d = 0. The affine translates U_i = 1 + J^i are closed subgroup schemes of GL(Lie(G));
   their inverse is the finite geometric sum. The dual-number description gives Lie(U_1) = J.
3. Every ad(X) lowers C. By lem-sfb-charzero-lie-detects-factorization, Ad factors through
   U_1, giving rho : G → U_1.
4. Over every commutative k-algebra, for s = 1 + u and t = 1 + v in U_1 and U_i,
   sts⁻¹t⁻¹ - 1 = (uv - vu)s⁻¹t⁻¹ lies in J^(i+1). The inverse polynomials preserve this
   two-sided ideal. Hence [U_1,U_i] lies in U_(i+1), and these subgroups are normal.
5. Pull U_(i+1) back along rho for 0 ≤ i < d and append the trivial subgroup G_d.
   The initial subgroup is G. The commutator calculation gives all but the last inclusion.
   The penultimate subgroup is ker(rho) = ker(Ad), which is central by
   lem-sfb-charzero-adjoint-differential-central-kernel, giving the final inclusion.
   When Lie(G) = 0, J = 0 and U_1 = 1, so the same construction applies. The trivial
   group is also allowed, including a series of length zero. -/
theorem charZero_nilpotent_of_ad_nilpotent
    (k : Type u) [Field k] [CharZero k]
    (kbar : Type v) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (G : Grp (Over (Spec (.of k))))
    (haff : IsAffine G.X.left)
    (hsm : Smooth G.X.hom) (hconn : ConnectedSpace G.X.left)
    (hft : LocallyOfFiniteType G.X.hom) (hqc : QuasiCompact G.X.hom)
    (had : ∀ X : GrpObj.Lie G.X, ∃ m : ℕ, 1 ≤ m ∧
      (LieAlgebra.ad k (GrpObj.Lie G.X) X) ^ m = 0) :
    ∃ (c : ℕ) (C : Fin (c + 1) → Grp (Over (Spec (.of k))))
      (i : ∀ j : Fin (c + 1), C j ⟶ G),
      (∀ j : Fin (c + 1), IsClosedSubgroupScheme (i j).hom.hom ∧
        IsNormalSubgroupScheme (i j).hom.hom) ∧
      IsIso (i 0) ∧ Nonempty (C (Fin.last c) ≅ Grp.trivial _) ∧
      (∀ j : Fin c, ∃ l : C j.succ ⟶ C j.castSucc, l ≫ i j.castSucc = i j.succ) ∧
      ∀ (j : Fin c) (A : Type u) [CommRing A] [Algebra k A]
        (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ G.X)
        (h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶
          (C j.castSucc).X),
        ∃ z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ (C j.succ).X,
          z ≫ (i j.succ).hom.hom =
            g * (h ≫ (i j.castSucc).hom.hom) * g⁻¹ *
              (h ≫ (i j.castSucc).hom.hom)⁻¹ := by
  sorry

end AlgebraicGeometry
