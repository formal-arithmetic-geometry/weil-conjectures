/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: SHEAF group Q149
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.FppfSheafCoproductPartition
public import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Coproducts of algebraic spaces

Source: Stacks Project, Spaces, Tag 02WQ (blueprint: lem-trf-algebraic-space-coproduct).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A set-indexed coproduct of algebraic spaces over a scheme is an algebraic space when
there is a scheme coproduct of the chosen surjective étale atlases.

Source: Stacks Project, Spaces, Tag 02WQ (blueprint: lem-trf-algebraic-space-coproduct).

Proof:
1. Apply lem-trf-fppf-sheaf-coproduct-partition to the underlying fppf sheaves of the
   `F i` (def-trf-algebraic-space). The coprojections `c i` are injective on sections.
   Every section `a ∈ C(T)` has a unique clopen partition `T = ∐ T_i(a)` with component
   sections `a_i ∈ F_i(T_i(a))`, and `h_{T_i(a)} ≅ h_T ×_C F_i`, compatibly with every
   scheme test. These partitions replace the generally false identity `C(T) = ∐ F_i(T)`.
2. Diagonal. For `a, b ∈ C(T)` put `T_ij = T_i(a) ∩ T_j(b)`. For `i = j` the scheme
   `E_i = h_{T_ii} ×_{F_i × F_i} F_i` exists by the representable diagonal of `F i`
   (def-trf-algebraic-space); let `E = ∐ E_i` (lem-weil-pbc-scheme-coproduct-family). On a
   test `Z → T`, equality `a|_Z = b|_Z` forces equal partitions by uniqueness in
   lem-trf-fppf-sheaf-coproduct-partition, so the `Z ×_T T_ij` with `i ≠ j` are empty and
   the `Z ×_T T_ii` cover `Z`. Injectivity of `c i` turns equality on each piece into a
   unique map to `E_i`; these glue to `Z → E` (lem-weil-pbc-scheme-morphism-gluing).
   Conversely a map `Z → E` gives equality on each summand, hence on `Z` by the sheaf
   condition (def-weil-pbc-sites-and-cohomology). So `E` represents `h_T ×_{C × C} C`.
3. Atlas. Let `U = ∐ U_i` be the given scheme coproduct; its summands form a disjoint
   clopen covering (lem-weil-pbc-scheme-coproduct-family). The sections `c_i(p_i)` agree
   on the empty overlaps (a sheaf has one section over the empty scheme,
   def-weil-pbc-sites-and-cohomology) and glue to `p : h_U → C` with `p|_{U_i} = c_i p_i`.
   The hypothesis that `U` is an object of the site makes it an allowed atlas.
4. Representability of `p`. For `a : h_T → C` with partition `T_i`, the scheme
   `V_i = h_{T_i} ×_{F_i} h_{U_i}` exists and `V_i → T_i` is surjective étale
   (def-trf-algebraic-space); put `V = ∐ V_i` (lem-weil-pbc-scheme-coproduct-family).
   A map `u : Z → U` with `p u = a|_Z` has `u⁻¹(U_i) = Z ×_T T_i` by uniqueness in
   lem-trf-fppf-sheaf-coproduct-partition; on each piece the datum is exactly a map to
   `V_i` since `c i` is injective, and the pieces glue uniquely to `Z → V`
   (lem-weil-pbc-scheme-morphism-gluing). Hence `h_V ≅ h_T ×_C h_U`.
5. Surjective étale. Each `t ∈ T` lies in a unique `T_i` and has a preimage in `V_i`.
   Étaleness of `V → T` holds by the affine-chart characterization of
   def-weil-etale-morphism, since `V_i ⊆ V` and `T_i ⊆ T` are open. Steps 1, 2 and 4 give
   the sheaf, diagonal and atlas conditions of def-trf-algebraic-space. For empty `I`
   every test `T → C` is empty and `U = V = ∅`; empty summands change nothing. -/
theorem algebraicSpace_coproduct
    {S : Scheme.{u}} (I : Type u) (F : I → AlgebraicSpace S) (U : I → Over S)
    (p : ∀ i, yoneda.obj (U i) ⟶ (F i).obj.obj)
    (hp : ∀ i, AlgebraicSpace.IsEtale (p i) ∧ AlgebraicSpace.IsSurjective (p i))
    (Ucoprod : Over S) (ι : ∀ i, U i ⟶ Ucoprod)
    (hU : Nonempty (IsColimit (Cofan.mk Ucoprod ι)))
    (C : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (c : ∀ i, (F i).obj ⟶ C)
    (hC : IsColimit (Cofan.mk C c)) : AlgebraicSpace.IsAlgebraicSpace C := by
  sorry

end AlgebraicGeometry
