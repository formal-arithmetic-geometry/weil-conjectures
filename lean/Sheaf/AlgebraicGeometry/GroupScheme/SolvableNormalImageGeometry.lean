module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothConnectedDerivedSubgroup
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage

/-! # Images of smooth connected solvable normal subgroup schemes

Source: Milne, Algebraic Groups (2017), Theorem 5.39 and Remark 5.42, p.108;
Proposition 1.62(b), p.24; Propositions 6.27 and 6.30, pp.131--132;
Lemma 19.14, p.400.
(blueprint: lem-sfb-solvable-normal-image-geometry)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The faithfully flat image of a smooth connected solvable normal closed subgroup
is smooth, connected, solvable and normal in the quotient ambient group.
The closed immersion j need not be assumed to be a homomorphism: this follows
from its composite with the faithfully flat homomorphism q.

Source: Milne, Algebraic Groups (2017), Theorem 5.39 and Remark 5.42, p.108;
Proposition 1.62(b), p.24; Propositions 6.27 and 6.30, pp.131--132;
Lemma 19.14, p.400.
(blueprint: lem-sfb-solvable-normal-image-geometry)

Proof plan:
1. Faithful flatness makes q* injective by
   lem-weil-pbc-faithfully-flat-universally-injective. Split injections as F-linear
   maps to see that their tensor products are injective. Use def-weil-affine-spectrum,
   lem-weil-pbc-fibre-product-affine-spectra and
   lem-weil-pbc-algebra-tensor-pushout-universal-property to identify product coordinates.
   Injective pullback detects equality and factorization through a closed subscheme
   (def-weil-closed-immersion). Apply this after q times q, q and the identity section
   to obtain the homomorphism property of j.
2. Smoothness of N gives geometrically reduced fibres by
   sbc-lem-smooth-geometrically-reduced. Injectivity of q* persists over every field
   extension and embeds the coordinate ring of I into that of N; thus I is
   geometrically reduced (def-pc-reduced-scheme). Apply
   lem-sfb-geometrically-reduced-group-smooth to obtain smoothness of I.
3. By lem-weil-pbc-faithfully-flat-surjective-spectrum, q is surjective on points.
   Pulling back a nontrivial clopen decomposition of I contradicts connectedness of N
   (def-weil-connected-scheme). The identity point ensures nonemptiness.
4. Iterate lem-sfb-smooth-connected-derived-subgroup on N until the trivial term.
   Apply lem-sfb-affine-homomorphism-flat-image to the maps of its derived terms into I,
   obtaining closed images J_r with faithfully flat maps from those terms. Take J_0 = I
   and the terminal J_t to be the identity subgroup. Steps 2 and 3 give smoothness
   and connectedness of every J_r; this includes derived length zero.
5. The commutator of J_r factors through J_(r+1): after the faithfully flat product
   of source-image maps it does, by the derived-subgroup property. The tensor
   injectivity of step 1 detects vanishing of the defining ideal already on J_r times J_r.
6. Inductively the r-th derived subgroup of I lies in J_r. Restrict the commutator
   factorization of step 5 to that derived subgroup and intersect with J_(r+1).
   The intersection is closed (sum of defining ideals), so minimality in
   lem-sfb-smooth-connected-derived-subgroup gives the next inclusion. The terminal
   term J_t is trivial, so the derived series of I terminates.
7. Let K be the defining ideal of j and let c send (h,i) to h j(i) h⁻¹.
   Normality of N (def-sc-group-scheme-subgroup) makes c after f times q factor
   through I, by evaluation at the universal affine pair. Thus the pullback of K
   vanishes after f times q. Its coordinate map is injective by step 1 applied to
   f* and q*, so c itself factors through I. On every F-algebra this gives invariance
   under conjugation; applying the same assertion to h⁻¹ gives equality, hence normality.
   Neither kernel has been assumed finite or smooth. -/
theorem solvableNormalImage_geometry {F : Type u} [Field F] [IsAlgClosed F]
    (G H N I : Over (Spec (.of F))) [GrpObj G] [GrpObj H] [GrpObj N] [GrpObj I]
    [IsAffine G.left] [IsAffine H.left] [IsAffine I.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    [LocallyOfFiniteType I.hom] [QuasiCompact I.hom]
    (f : G ⟶ H) [IsMonHom f]
    (hf : @Module.FaithfullyFlat Γ(H.left, ⊤) Γ(G.left, ⊤) _ _
      f.left.appTop.hom.toAlgebra.toModule)
    (i : N ⟶ G) [IsClosedSubgroupScheme i] [IsNormalSubgroupScheme i]
    [Smooth N.hom] [ConnectedSpace N.left] (hN : IsSolvableGroupScheme N)
    (q : N ⟶ I) [IsMonHom q]
    (hq : @Module.FaithfullyFlat Γ(I.left, ⊤) Γ(N.left, ⊤) _ _
      q.left.appTop.hom.toAlgebra.toModule)
    (j : I ⟶ H) [IsClosedImmersion j.left] (hfactor : i ≫ f = q ≫ j) :
    Smooth I.hom ∧ ConnectedSpace I.left ∧ IsSolvableGroupScheme I ∧
      IsNormalSubgroupScheme j := by
  sorry

end AlgebraicGeometry
