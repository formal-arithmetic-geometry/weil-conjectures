/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
import Sheaf.AlgebraicGeometry.StandardGroupSchemes
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothGroupOrbitGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Unipotent homogeneous quotients immerse into affine space

Source: Milne, Algebraic Groups (2017), Proposition 14.26, printed p.286;
Corollaries 14.6 and 14.12, printed pp.282--283
(blueprint: lem-sfb-unipotent-homogeneous-quasiaffine).

The quotient is any separated finite-type representative of the fppf coset sheaf,
using exactly the sheafification interface of the homogeneous-orbit quotient node.
The target is the spectrum of the polynomial algebra in n variables over k.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A smooth unipotent closed subgroup has a homogeneous quotient admitting an
immersion into finite-dimensional affine space. Unipotence is the explicit
nilpotence condition on k-points of the supplied faithful matrix representation.

Source: Milne, Proposition 14.26, p.286, and Corollaries 14.6 and 14.12, pp.282--283
(blueprint: lem-sfb-unipotent-homogeneous-quasiaffine).

Proof:
1. The closed immersion rho into GL makes U affine and finite type, since its
   coordinate ring is a quotient of the finitely generated localized polynomial
   algebra of GL. It also makes rho injective on every algebra's points.
2. Apply lem-sfb-geometric-unipotence-unitriangular-embedding with algebraic
   closure k itself. It identifies the stated matrix condition with unipotence.
3. By lem-sfb-chevalley-scheme-line-stabilizer, choose a finite-dimensional rational
   G-representation V and a line L with scheme-theoretic stabilizer U. The action
   on L is a character U to G_m (def-sc-gm-ga). It is trivial by
   lem-sfb-unipotent-to-multiplicative-trivial, so L is contained in V^U.
   The unnecessary equality V^U = L printed in Milne is not used.
4. For a nonzero x in L and every k-algebra A, x_A generates the rank-one
   summand L_A. Fixing x_A implies preserving L_A, hence membership in U(A);
   conversely U(A) fixes x_A. This also holds for the zero algebra. Thus U is
   the full scheme-theoretic vector stabilizer, without a normality assumption.
5. A basis of V identifies its underlying affine scheme with Spec k[t_1,...,t_n].
   Its coordinate action sends t_i to the sum of r_ij tensor t_j. This scheme
   is finite type and is separated by lem-weil-pbc-affine-source-morphism-separated.
6. By lem-sfb-smooth-group-orbit-geometry the reduced orbit is locally closed.
   By lem-sfb-homogeneous-orbit-quotient-geometry the specified fppf quotient Q
   is canonically isomorphic to that orbit. Composing with the orbit immersion
   gives j. An immersion factors as closed into open by
   IsImmersion.isImmersion_iff_exists, exactly the node's immersion convention.
-/
theorem exists_unipotent_homogeneous_quotient_immersion
    {k : Type u} [Field k] [IsAlgClosed k]
    (G U : Over (Spec (.of k))) [GrpObj G] [GrpObj U]
    [IsAffine G.left] [Smooth G.hom] [ConnectedSpace G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (i : U ⟶ G) [IsClosedSubgroupScheme i] [Smooth U.hom]
    (m : ℕ) (hm : 1 ≤ m)
    (ρ : U ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} m) k)
    [IsMonHom ρ] [IsClosedImmersion ρ.left]
    (hρ : ∀ a : (Spec (.of k)).asOver (Spec (.of k)) ⟶ U,
      ∃ N : ℕ, 1 ≤ N ∧
        ((GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} m) k k
          (a ≫ ρ) : Matrix (LinearGroupSchemes.Index.{u} m)
            (LinearGroupSchemes.Index.{u} m) k) - 1) ^ N = 0)
    (Q : Over (Spec (.of k))) (q : G ⟶ Q)
    [IsSeparated Q.hom] [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    (hQ : Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (.of k))) (yoneda.obj Q))
    (ηq : coequalizer (yoneda.map (fst G U))
      (yoneda.map (lift (fst G U) (snd G U ≫ i) ≫ μ[G])) ⟶ yoneda.obj Q)
    (hηq : coequalizer.π _ _ ≫ ηq = yoneda.map q)
    (hquot : ∀ Z : Sheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type u),
      Function.Bijective (fun f : yoneda.obj Q ⟶ Z.obj ↦ ηq ≫ f)) :
    ∃ (n : ℕ)
      (j : Q ⟶ (Spec (.of (MvPolynomial (Fin n) k))).asOver (Spec (.of k))),
      IsImmersion j.left := by
  sorry

end AlgebraicGeometry
