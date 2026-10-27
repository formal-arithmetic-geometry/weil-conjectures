/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.Dimension
import WeilConjectures.AlgebraicGeometry.EffectiveDescent
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Sheaf.AlgebraicGeometry.AbelianVariety.SubvarietySeparableDefinition
import Sheaf.AlgebraicGeometry.DimensionExtension
import Sheaf.AlgebraicGeometry.ProperDimZeroFiniteOverField
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Basic

/-! # The abelian part of a homomorphism kernel

Source: Milne, Abelian Varieties, Chapter I, Proposition 10.1 and footnote 10,
printed p.42, and the discussion after Remark 10.2 and footnote 11, printed p.43.
(blueprint: lem-sfb-abelian-kernel-abelian-part)

The ground field is arbitrary. The abelian subgroup is not asserted to be the reduction
of the kernel over an imperfect field. The kernel itself may be nonreduced.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The scheme-theoretic kernel of a homomorphism of abelian varieties contains a closed
abelian subgroup of the same dimension. A zero-dimensional kernel is finite, with no
reducedness assumption.

Source: Milne, Abelian Varieties, Chapter I, discussion after Remark 10.2 and footnote 11,
printed p.43; the imperfect-field issue also appears in Proposition 10.1, footnote 10, p.42.
(blueprint: lem-sfb-abelian-kernel-abelian-part)

Proof:
1. By lem-sc-kernel-subgroup, K is the fibre-product kernel and is a closed subgroup of A.
   The ambient A is proper by def-sc-abelian-variety, so K is proper and of finite type by
   lem-weil-pbc-closed-immersion-proper and def-weil-proper-morphism. Its identity is a k-point.
2. Choose an algebraic closure Omega by def-weil-algebraic-closure. The ambient base change
   is abelian by lem-sfb-abelian-field-extension. Closed immersions are preserved by base
   change (lem-weil-pbc-closed-immersion-base-change), and the kernel base changes to the
   kernel by def-pc-base-change. By lem-sfb-abelian-closed-subgroup-reduced-component, the
   reduced identity component C of this geometric kernel is an abelian subgroup with the
   dimension of the geometric kernel.
3. By lem-sfb-abelian-subvariety-separable-definition, C descends as a closed abelian
   subvariety C_E of A_E over a finite Galois intermediate extension E/k.
4. Every k-automorphism of E extends to Omega by
   lem-weil-pbc-normal-subextension-automorphism-extends. Its semilinear action on the kernel
   preserves both its reduction and its identity component, hence C. Faithful scalar
   extension reflects equality of ideals: injectivity of R/J into its tensor product
   detects I contained in J, and conversely. Thus C_E is Galois invariant as a closed
   subscheme and satisfies lem-sfb-galois-closed-subscheme-descent.
5. That descent lemma supplies a closed k-subgroup D of A with geometric base change C.
   Properness, smoothness, connectedness and finite type descend along E/k by
   thm-pd-fpqc-local-properties, so D is abelian by def-sc-abelian-variety. The ideal of K
   vanishes on D after extending to Omega, hence already over k by the same tensor-product
   injectivity. Thus D factors through K. Locally the factor is the quotient map
   R/I_K to R/I_D, so it is a closed immersion. Its group compatibility is detected after
   composition with the monomorphism K into A.
6. By lem-kun-dimension-extension, dimensions of D and K are unchanged by extension to
   Omega. There D becomes C, whose dimension equals that of the geometric kernel.
   These are the dimensions of def-kun-topological-krull-dimension. If dim K = 0, use
   lem-pc-scheme-dimension-local-rings and lem-pc-dim-zero-finite-over-field on the proper
   kernel. This proves finiteness without assuming that the kernel is reduced. -/
theorem IsAbelianVariety.exists_closed_subgroup_ker_same_dimension
    {k : Type u} [Field k] {A B : Over (Spec (.of k))}
    [GrpObj A] [GrpObj B] [IsAbelianVariety A] [IsAbelianVariety B]
    (f : A ⟶ B) [IsMonHom f] :
    (∃ (D : Over (Spec (.of k))) (_ : GrpObj D) (_ : IsAbelianVariety D)
      (i : D ⟶ GrpObj.ker f),
      IsClosedSubgroupScheme i ∧
        topologicalKrullDim D.left = topologicalKrullDim (GrpObj.ker f).left) ∧
      (topologicalKrullDim (GrpObj.ker f).left = 0 → IsFinite (GrpObj.ker f).hom) := by
  sorry

end AlgebraicGeometry
