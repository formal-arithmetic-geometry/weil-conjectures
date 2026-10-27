/-
Copyright (c) 2026 Q61. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q61
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Sheaf.AlgebraicGeometry.FiniteDiagonalizableGroupScheme
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry

/-! # Central isogenies of semisimple groups are multiplicative

Source: Milne, Algebraic Groups (2017), Proposition 19.15, printed pp.400--401;
Definition 18.1 and the following paragraph, printed p.387; Proposition 5.47, printed p.110
(blueprint: lem-sfb-semisimple-central-isogeny-multiplicative).
-/

@[expose] public section

universe u

open CategoryTheory MonObj

namespace AlgebraicGeometry

/-- A surjective homomorphism of semisimple groups with finite central scheme-theoretic
kernel is faithfully flat and has finite diagonalizable kernel, hence is multiplicative.

Source: Milne, Algebraic Groups (2017), Proposition 19.15 and its proof, printed pp.400--401;
Definition 18.1 and the following paragraph, printed p.387; Proposition 5.47, printed p.110
(blueprint: lem-sfb-semisimple-central-isogeny-multiplicative).

Proof plan:
1. For a rational point y of G0, its affine fibre has coordinate algebra
   F[G1] tensor over F[G0] with F (lem-weil-pbc-fibre-product-affine-spectra).
   Scheme-surjectivity makes this algebra nonzero: a point above y supplies a map
   to its residue field. It is of finite type over F. Choose a maximal ideal
   (lem-weil-common-extension-fields-maximal-ideal) and apply the Nullstellensatz
   (lem-wf-affine-nullstellensatz-vanishing). The resulting F-point of the fibre
   proves surjectivity on F-points (def-weil-affine-spectrum).
2. Apply lem-sfb-affine-group-homomorphism-image, since G0 is smooth, to obtain
   faithful flatness of the coordinate-algebra map.
3. G1 is reductive: a smooth connected normal unipotent subgroup U is solvable by
   lem-sfb-smooth-unipotent-solvable. Its solvable series yields termination of its
   derived series: the quotients have their displayed kernels by
   lem-sfb-affine-normal-quotient-geometry; their commutativity puts each derived
   subgroup inside the next term. Monotonicity D(H) ⊆ D(H') for H ⊆ H' gives the
   induction. Semisimplicity forces U to be trivial. Since F is algebraically closed,
   no additional extension is required for the geometric reductivity condition.
4. The kernel K is a closed subgroup (lem-sc-kernel-subgroup). Centrality factors
   its inclusion through the represented centre (lem-sfb-affine-group-centre-base-change):
   evaluate the functor inclusion on K's universal point. The induced factor is a
   closed immersion, as F[G1] → F[K] is surjective and factors through F[Z(G1)]
   (def-weil-closed-immersion, def-weil-affine-spectrum). By
   lem-sfb-reductive-centre-multiplicative-type, the centre is a closed subgroup of
   a split torus. Thus K is a closed subgroup of a split torus.
5. Apply lem-sfb-split-torus-subgroups-diagonalizable to get K ≅ D(M) with its
   group-algebra Hopf structure. Finiteness of F[K] makes M finite. Together with
   Step 2 this is exactly a multiplicative isogeny. No reducedness, separability,
   or restriction on the characteristic or on the kernel's order was used. -/
theorem semisimpleCentralIsogeny_multiplicative {F : Type u} [Field F] [IsAlgClosed F]
    (G1 G0 : Over (Spec (.of F))) [GrpObj G1] [GrpObj G0]
    (hG1 : IsSemisimpleGroupScheme G1) (hG0 : IsSemisimpleGroupScheme G0)
    (f : G1 ⟶ G0) [IsMonHom f] [Surjective f.left]
    [IsFinite (GrpObj.ker f).hom]
    (hcentral : ∀ (T : Over (Spec (.of F))) (x : T ⟶ GrpObj.ker f) (g : T ⟶ G1),
      (x ≫ GrpObj.kerι f) * g = g * (x ≫ GrpObj.kerι f)) :
    f.left.appTop.hom.FaithfullyFlat ∧
      IsFiniteDiagonalizableGroupScheme (GrpObj.ker f) := by
  sorry

end AlgebraicGeometry
