/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.LinearAlgebra.Basis.VectorSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-! # Normality from geometric conjugations in a smooth ambient group

Source: Milne, Algebraic Groups (2017), Corollary 1.85, printed p.32, and
Proposition 1.90, printed p.33 (blueprint: lem-sfb-smooth-ambient-normality-geometric).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- A closed subgroup of a smooth affine algebraic group is normal if every geometric
conjugation preserves the subgroup scheme. Source: Milne, Algebraic Groups (2017),
Corollary 1.85, printed p.32 (blueprint: lem-sfb-smooth-ambient-normality-geometric).

The equality in `hconj` is tested on every scheme `T` over the algebraic closure, not
merely on its field-valued points. Via the base-change adjunction this is exactly
`Int(g)(N_Ω) = N_Ω` as closed subgroup schemes. The morphism `Over.homMk T.hom`
pulls the geometric point `g` back to `T`.

Proof:
1. Write `J = Spec R` and `N = Spec (R/I)` using
   lem-weil-pbc-closed-immersion-affine-cover-criterion. The relative diagonals of
   affine schemes come from the surjective multiplication maps on tensor products,
   so both schemes are separated (lem-weil-pbc-fibre-product-affine-spectra).
   Finite type makes `R` finitely generated (lem-weil-pbc-lft-affine-pairs).
2. Apply lem-sfb-constant-source-closed-factorization-locus to `Y = W = N`,
   `X = S = J`, and `(n,j) ↦ jnj⁻¹`. Its closed locus `L` represents the
   one-sided conjugation transporter, on all test schemes and after scalar extension.
3. The hypothesis puts every geometric point of `J` in `L`. Smoothness makes `J_Ω`
   reduced (sbc-lem-smooth-geometrically-reduced). The base-changed closed immersion
   is cut out by an ideal in the finitely generated algebra `R ⊗[k] Ω`
   (lem-weil-pbc-closed-immersion-base-change and the affine criterion).
   Every element of that ideal vanishes at all geometric points; clause 2 of
   lem-wf-affine-nullstellensatz-vanishing makes it zero. Thus `L_Ω = J_Ω`.
4. Write `L = Spec (R/H)`. For `h ∈ H`, the previous step gives `h ⊗ 1 = 0`.
   Choose a basis of `Ω` over `k` (lem-weil-pbc-vector-space-free). A coordinate
   functional, divided by a nonzero coefficient in the expansion of `1`, gives
   a linear map `λ : Ω → k` with `λ(1) = 1`. Applying `r ⊗ a ↦ r λ(a)` gives
   `h = 0`. Hence `H = 0` and `L = J`, without a perfection assumption.
5. On `Spec A` for any commutative `k`-algebra, `L = J` gives
   `jN(A)j⁻¹ ⊆ N(A)`. Applying this to `j⁻¹` gives the reverse inclusion.
   Thus the image subgroup is normal for every `A`, exactly
   def-sc-group-scheme-subgroup. Neither connectedness nor smoothness of `N` is used. -/
theorem isNormalSubgroupScheme_of_geometric_conjugations
    {k : Type u} [Field k] (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (J N : Over (Spec (.of k))) [GrpObj J] [GrpObj N]
    [IsAffine J.left] [IsAffine N.left]
    [LocallyOfFiniteType J.hom] [QuasiCompact J.hom]
    [LocallyOfFiniteType N.hom] [QuasiCompact N.hom] [Smooth J.hom]
    (i : N ⟶ J) [IsClosedSubgroupScheme i]
    (hconj : ∀ (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ⟶ J)
      (T : Over (Spec (.of Ω))),
      Set.image
        (fun x : (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj T ⟶ J ↦
          (Over.homMk T.hom ≫ g) * x * (Over.homMk T.hom ≫ g)⁻¹)
        (Set.range (fun n :
          (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj T ⟶ N ↦ n ≫ i)) =
      Set.range (fun n :
        (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj T ⟶ N ↦ n ≫ i)) :
    IsNormalSubgroupScheme i := by
  sorry

end AlgebraicGeometry
