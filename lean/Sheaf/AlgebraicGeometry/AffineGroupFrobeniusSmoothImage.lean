/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Group.Smooth
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import Sheaf.RingTheory.HopfAlgebra.ReducedCoreNilpotentFibre
import Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Smooth images of iterated relative Frobenius on affine group schemes

Source: Milne, Algebraic Groups (2017), Theorem 3.23 (Cartier), Proposition 3.29
and Remark 3.30, printed pp. 71--73.
(blueprint: lem-sfb-affine-group-frobenius-smooth-image)

The two pullback projections specify relative Frobenius uniquely. Under the affine
base-change identification its coordinate map is b tensor c to c b^(p^r).
The image is Mathlib's scheme-theoretic image, namely the closed subscheme defined
by the kernel ideal sheaf; on this affine target it is Spec of the coordinate-ring
quotient by the kernel. Both factor maps are the canonical image factor maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An affine finite-type group scheme over an algebraically closed field is smooth
in characteristic zero. In positive characteristic, some positive iterate of relative
Frobenius has smooth affine finite-type scheme-theoretic image, and its canonical
image factorization is by group homomorphisms with a closed immersion as second map.
The target group structure is exactly the base change of the given one.

Source: Milne, Algebraic Groups (2017), Theorem 3.23, Proposition 3.29 and
Remark 3.30, printed pp. 71--73.
(blueprint: lem-sfb-affine-group-frobenius-smooth-image)

Proof plan, following the six steps of the node:
1. Set A = k[G]. The affine group coordinate Hopf instance
   (lem-sfb-affine-group-coordinate-hopf) gives its Hopf structure, and
   lem-pc-affine-finite-type-algebra gives finite generation over k.
2. Apply lem-sfb-hopf-reduced-core-nilpotent-fibre to obtain a finitely generated
   reduced Hopf subalgebra C. In characteristic zero C = A; in characteristic p,
   C is the subalgebra of p^r-th powers for some r >= 1. The Hopf spectrum functor
   (lem-sfb-hopf-spectrum-functor) makes H = Spec C a group. It is finite type
   by its generators and reduced by lem-weil-pbc-affine-scheme-reduced-iff.
3. Algebraic closure makes k perfect. Apply lem-kun-geometric-reduced-perfect to H,
   then lem-sfb-geometrically-reduced-group-smooth. In characteristic zero H = G,
   proving the first clause. Retain r in positive characteristic.
4. The affine fibre-product dictionary (lem-weil-pbc-fibre-product-affine-spectra)
   gives the twisted coordinate algebra B = A tensor_(k,F_k^r) k. The tensor
   universal property (lem-weil-pbc-algebra-tensor-pushout-universal-property)
   gives the map phi(b tensor c) = c b^(p^r). Its image is C, since every scalar
   has a p^r-th root. The two projections characterize its spectrum morphism.
5. Base change gives the target group structure. On pure tensors, comultiplication,
   counit and antipode commute with phi by the p^r-power identities. The inclusion
   C tensor C into A tensor A is injective, as follows by extending a k-basis.
   Hence both the inclusion C into A and the corestriction B onto C are Hopf maps.
   The Hopf spectrum functor makes their spectra group homomorphisms whose
   composite is relative Frobenius.
6. The quotient B / ker phi is canonically isomorphic to C: equal images are
   exactly equal residue classes and every element of C has a preimage. Thus
   the specified scheme-theoretic image is isomorphic to H. Transport its group
   structure and smoothness along this isomorphism. The canonical quotient map
   is surjective, so lem-weil-pbc-closed-immersion-affine-cover-criterion makes
   the image inclusion a closed immersion. The canonical image factorization
   then supplies u and j with the required composition and homomorphism properties. -/
theorem affine_group_frobenius_smooth_image
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : Scheme.{u}) (s : G ⟶ Spec (.of k)) [GrpObj (Over.mk s)] [IsAffine G]
    [LocallyOfFiniteType s] [QuasiCompact s] :
    (CharZero k → Smooth s) ∧
      ∀ (p : ℕ) (hp : p.Prime) (hk : (p : k) = 0),
        ∃ r : ℕ, 1 ≤ r ∧
          ∃ (hG : (p : Γ(G, ⊤)) = 0)
            (F : G ⟶ pullback s
              (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk r)))),
            F ≫ pullback.fst s
                (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk r))) =
              G.iterateFrobenius hp hG r ∧
            F ≫ pullback.snd s
                (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk r))) = s ∧
            ∃ hT : GrpObj (Over.mk (pullback.snd s
                (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk r))))),
              hT = Over.grpObjMkPullbackSnd ∧
              ∃ _ : GrpObj (Over.mk (F.imageι ≫ pullback.snd s
                  (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk r))))),
                IsAffine F.image ∧
                LocallyOfFiniteType (F.imageι ≫ pullback.snd s
                  (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk r)))) ∧
                QuasiCompact (F.imageι ≫ pullback.snd s
                  (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk r)))) ∧
                Smooth (F.imageι ≫ pullback.snd s
                  (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk r)))) ∧
                ∃ (u : Over.mk s ⟶ Over.mk (F.imageι ≫ pullback.snd s
                    (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk r)))))
                  (j : Over.mk (F.imageι ≫ pullback.snd s
                      (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk r)))) ⟶
                    Over.mk (pullback.snd s
                      (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk r))))),
                  u.left = F.toImage ∧ j.left = F.imageι ∧
                  IsMonHom u ∧ IsMonHom j ∧ IsClosedImmersion j.left ∧
                  u.left ≫ j.left = F := by
  sorry

end AlgebraicGeometry
