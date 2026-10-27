/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
import Sheaf.AlgebraicGeometry.GroupScheme.BorelQuotientProperGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.BorelHomomorphismRigidity
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # A nilpotent Borel subgroup equals its ambient group

Source: Milne, Algebraic Groups (2017), Proposition 17.23(b) implies (c), printed p.359;
Section 17b, printed p.353, and Proposition 6.38, printed p.133.
(blueprint: lem-sfb-nilpotent-borel-equals-group)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- A Borel subgroup admitting a finite descending central series is the whole group.
The series terms are closed subgroup schemes of B, without smoothness or connectedness
conditions. Its commutator containment is tested on every commutative k-algebra,
including nonreduced algebras. Isomorphism of the specified inclusion means equality
as closed subgroup schemes, rather than an abstract isomorphism between B and G.

Source: Milne, Algebraic Groups (2017), Proposition 17.23(b) implies (c), printed p.359;
Section 17b, printed p.353, and Proposition 6.38, printed p.133.
(blueprint: lem-sfb-nilpotent-borel-equals-group)

Proof plan, by induction on the supplied central-series length m for all pairs (G,B):
1. If m = 0, B is trivial. Apply lem-sfb-borel-quotient-proper-geometry to the
   identity quotient G → G by B = 1. Thus G is proper and integral. It is affine,
   so lem-sc-proper-affine-finite-general makes it finite over k. Its coordinate
   ring is a finite-dimensional domain over k, hence a field algebraic over k.
   Algebraic closedness makes this field k, giving G = B = 1.
2. If m > 0, put N = C_(m-1). The last commutator condition says N centralizes B
   on every test algebra. For n in N(R), conjugation by n on G_R restricts to the
   identity on B_R. Apply lem-sfb-borel-homomorphism-rigidity over R to conclude
   that it is the identity on G_R. Hence N is central, and therefore normal in G.
3. By lem-sfb-affine-normal-quotient-geometry, q : G → Q = G/N is faithfully flat
   and finitely presented, with kernel N; Q is affine, finite type, smooth and
   connected. Here G is geometrically connected since k is algebraically closed.
   By lem-sfb-quotient-borel-torus-images, D = q(B) is Borel in Q. The subgroup
   correspondence identifies B with q⁻¹(D), with no smoothness assumption on N.
4. The same correspondence gives D_j in Q with q⁻¹(D_j) = C_j for j ≤ m-1.
   Then D_0 = D and D_(m-1) = 1. To check [D,D_j] ⊆ D_(j+1), lift two sections
   over a common fppf cover to B and C_j. Their commutator lies in C_(j+1), so
   its image lies in D_(j+1) on that cover. Closed-subscheme membership descends
   faithfully flatly, since an ideal vanishing after faithfully flat extension
   already vanishes. This gives a central series for D of length m-1.
5. Induction gives D = Q. Taking inverse images along q gives B = q⁻¹(D) = G.
   All containments and equalities retain the full scheme structure. -/
theorem isIso_of_borel_of_nilpotent
    {k : Type u} [Field k] [IsAlgClosed k]
    (G B : Grp (Over (Spec (.of k)))) (i : B ⟶ G)
    [IsAffine G.X.left] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (hB : IsBorelGroupScheme i.hom.hom)
    (hnil : ∃ (m : ℕ) (C : Fin (m + 1) → Grp (Over (Spec (.of k))))
      (c : ∀ j : Fin (m + 1), C j ⟶ B),
      (∀ j : Fin (m + 1), IsClosedSubgroupScheme (c j).hom.hom) ∧
      IsIso (c 0) ∧ Nonempty (C (Fin.last m) ≅ Grp.trivial _) ∧
      (∀ j : Fin m, ∃ l : C j.succ ⟶ C j.castSucc, l ≫ c j.castSucc = c j.succ) ∧
      ∀ (j : Fin m) (A : Type u) [CommRing A] [Algebra k A]
        (b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ B.X)
        (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ (C j.castSucc).X),
        ∃ z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ (C j.succ).X,
          z ≫ (c j.succ).hom.hom =
            b * (x ≫ (c j.castSucc).hom.hom) * b⁻¹ * (x ≫ (c j.castSucc).hom.hom)⁻¹) :
    IsIso i := by
  sorry

end AlgebraicGeometry
