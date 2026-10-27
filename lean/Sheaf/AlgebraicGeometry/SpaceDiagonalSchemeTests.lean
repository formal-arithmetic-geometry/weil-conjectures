/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q91
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties

/-! # Scheme tests of the relative diagonal of an algebraic-space morphism

Source: Stacks Project, Morphisms of Spaces, Tag 03HK (1)--(3), and Spaces,
Tag 025V (blueprint: lem-sfb-space-diagonal-scheme-tests).

The diagonal is formed in fppf sheaves. The existing `IsRepresentableWith` predicate
retains a representing scheme and its actual projection for every scheme test.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every scheme test of the relative diagonal is represented by a scheme whose
projection to the test scheme is locally of finite type and a monomorphism of schemes.
Source: Stacks Project, Morphisms of Spaces, Tag 03HK (1)--(3), and Spaces, Tag 025V
(blueprint: lem-sfb-space-diagonal-scheme-tests).

Proof:
1. For a test `t = (t₁,t₂) : T → U ×_V U`, the representing scheme of the pullback
   of the absolute diagonal of `U` along `(t₁,t₂)` also represents the relative test:
   both functors assign to `Z` the maps `z : Z → T` with `t₁z = t₂z`. The other
   coordinate of the relative test is forced. Use def-trf-algebraic-space and the
   fibre-product universal properties of lem-trf-space-fibre-products-etale-covers.
2. The same forced-coordinate description proves monomorphy on every scheme `Z`.
   Equal projections give equal maps to the test. Even without a prescribed base
   structure on `Z`, the common projection to `T` supplies it, so this is monomorphy
   in schemes, not only in schemes over the base (def-trf-algebraic-space).
3. Choose a surjective etale scheme atlas `A → U`. Both `R = A ×_U A` and
   `P = A ×_V A` are schemes by the representable diagonals. The map `P → U ×_V U`
   is surjective etale, since it is a composite of two base changes of the atlas;
   `R → P` is the pullback of the relative diagonal. Use def-pc-fibre-product,
   def-trf-algebraic-space, lem-trf-space-chartwise-etale-permanence, and
   lem-trf-space-fibre-products-etale-covers.
4. The projection `R → A` is etale, hence unramified and locally of finite type
   (def-weil-etale-morphism and def-weil-unramified-morphism). Its factorization
   through `R → P → A` makes `R → P` locally of finite type by clause (a) of
   lemma-nagata-finite-type-to-separated-target; no condition on `P → A` is needed.
5. Set `Q = T ×_(U ×_V U) P`. It is a scheme surjective etale over `T` by the
   same base-change results. The test over `Q` identifies with `R ×_P Q`, by
   forgetting or restoring the forced `U` coordinate. Its projection to `Q` is
   locally of finite type by lem-weil-pbc-lft-base-change. Its projection to the
   original representing scheme is surjective etale (def-pc-fibre-product).
6. Apply lem-sfb-scheme-etale-source-target-properties to this square: both vertical
   maps are etale and the source map is surjective, so local finite type descends
   from the test over `Q` to the test over `T`. This proves all three clauses with
   no finiteness or separation assumption on the original morphism or spaces. -/
theorem diagonal_scheme_tests {B : Scheme.{u}} (U V : AlgebraicSpace B) (g : U ⟶ V) :
    IsRepresentableWith (fun _ _ p ↦ LocallyOfFiniteType p.left ∧ Mono p.left)
      (pullback.diagonal g.hom).hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
