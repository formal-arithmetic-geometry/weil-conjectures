/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.PerfectFieldGroupoidImageClosure
import Sheaf.AlgebraicGeometry.GroupoidScheme
import Sheaf.AlgebraicGeometry.ClosedImmersionProducts
import Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# The reduced neutral p-kernel of a group of bounded exponent

Source: Milne, Algebraic Groups (2017), Corollary 14.55, printed p.297;
Proposition 1.34, Corollary 1.39 and Proposition 1.52
(blueprint: lem-sfb-bounded-exponent-reduced-p-kernel).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The reduced neutral component of the p-kernel is a nontrivial smooth connected
commutative closed subgroup killed by p. Source: Milne, Algebraic Groups (2017),
Corollary 14.55, p.297; Proposition 1.34, Corollary 1.39 and Proposition 1.52
(blueprint: lem-sfb-bounded-exponent-reduced-p-kernel).

Here `H = GrpObj.ker (𝟙 C ^ p)`. The closed immersion `j` and its specified
kernel ideal identify `K` with the reduced induced closed subscheme on the
identity component of H. Reduction preserves the underlying space, and that
component is clopen for a finite type group, so this is precisely `(H_red)°`.
The specified ideal fixes its scheme structure, not just its point set.
Powers in the group of morphisms are pointwise powers: `𝟙 C ^ n` is [n],
and `1` is the constant identity morphism. Nontriviality means that the
structure morphism to Spec k is not an isomorphism.

Proof, following the five steps of the node:
1. By lem-sc-kernel-subgroup, H is a closed subgroup of C. Quotienting the
   finitely generated affine coordinate algebra, first by its kernel ideal
   and then by its nilradical, preserves finite type. Surjectivity of the
   p-th power map makes k perfect. The reduction clause of
   lem-sfb-perfect-field-groupoid-image-closure makes H_red a subgroup;
   its inclusion is the canonical reduction closed immersion.
2. Apply lem-sfb-finite-type-group-identity-subgroup to H_red. Its identity
   component K is connected, open and closed, with its open subscheme structure.
   Compose its closed inclusion with the reduction inclusion and H to C using
   lem-weil-pbc-closed-immersion-products. The affine closed immersion criterion
   gives an affine finite type K. As an open subscheme of H_red it is reduced.
3. By lem-kun-geometric-reduced-perfect K is geometrically reduced, and by
   lem-sfb-geometrically-reduced-group-smooth it is smooth. The injections
   K(R) into H(R) into C(R), for every k-algebra R, give commutativity and
   [p]_K = 0. The reduced closed structure gives the displayed vanishing ideal.
4. Choose the least n at least one with [p^n]_C = 0. Then a = [p^(n-1)]_C
   is nonzero by minimality. For n = 1, a is the identity, which is nonzero
   because C is nontrivial. Since [p] composed with a is zero, the kernel
   fibre product factors a through H.
5. By sbc-lem-smooth-geometrically-reduced C is reduced. The reduced-source
   factorization lemma factors C to H through H_red. The lift preserves the
   identity. Its connected image lies in the identity component, so the open
   subscheme factorization lemma factors it through K. If K were Spec k,
   this would make a constant at the identity, contradicting step 4. -/
theorem exists_nontrivial_reduced_neutral_p_kernel_of_bounded_exponent
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hperfect : Function.Surjective (fun a : k => a ^ p))
    (C : Over (Spec (CommRingCat.of k))) [GrpObj C] [IsCommMonObj C]
    [IsAffine C.left] [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
    [Smooth C.hom] [ConnectedSpace C.left] (hC : ¬ IsIso C.hom)
    (e : ℕ) (he : 1 ≤ e) (hexponent : 𝟙 C ^ (p ^ e) = 1) :
    ∃ (K : Over (Spec (CommRingCat.of k))) (_ : GrpObj K)
      (j : K ⟶ GrpObj.ker (𝟙 C ^ p)),
      IsClosedImmersion j.left ∧
      j.left.ker = Scheme.IdealSheafData.vanishingIdeal
        ⟨connectedComponent (GrpObj.onePoint (GrpObj.ker (𝟙 C ^ p))),
          isClosed_connectedComponent⟩ ∧
      IsClosedSubgroupScheme (j ≫ GrpObj.kerι (𝟙 C ^ p)) ∧
      IsAffine K.left ∧ LocallyOfFiniteType K.hom ∧ QuasiCompact K.hom ∧
      IsReduced K.left ∧ ¬ IsIso K.hom ∧ Smooth K.hom ∧
      ConnectedSpace K.left ∧ IsCommMonObj K ∧ 𝟙 K ^ p = 1 := by
  sorry

end AlgebraicGeometry
