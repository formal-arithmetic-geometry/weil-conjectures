/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceGroupoid
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange

/-!
# Constant local dimension of a field groupoid

Source: Stacks Project, spaces-more-groupoids.tex, Tags 06FD(1) and 06FE(1),
with the dimension conventions of Tags 04N5 and 04N6
(blueprint: lem-sfb-field-groupoid-constant-local-dimension).

The object space is the representable presheaf of `Spec K` over the given base.
The group specialization uses the same structural map for source and target.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every point of the arrow space of a locally finite type field groupoid has its
full dimension. Source: Stacks Project, Tag 06FD(1)
(blueprint: lem-sfb-field-groupoid-constant-local-dimension).

Proof:
1. For a field-valued object `a : Spec L → Spec K`, form the source fibre `F_a`.
   By lem-trf-space-fibre-products-etale-covers, an étale scheme atlas `V → R`
   base changes to an atlas `V ×_K L → F_a`. The hypothesis on `s` makes `V → Spec K`
   locally of finite type. The field specialization of
   lem-sc-fibre-dimension-after-base-change identifies local topological dimensions
   on these two schemes, hence the chart-local dimensions on `F_a` and `R`.
2. Represent any two points of `R` over a common field `L`, refining so that their
   targets agree, since `Spec K` has only one point. Call the arrows `a,b` and their
   sources `u,v`; the embeddings `u,v : Spec L → Spec K` can be distinct.
3. Set `q = a⁻¹ ∘ b : v → u`. Right composition `f ↦ f ∘ q` identifies `F_u` with
   `F_v`; its inverse is right composition by `q⁻¹`, by associativity and the inverse
   and identity laws. These formulas are natural on test schemes and take `a` to `b`.
   Transporting étale charts along this pointed isomorphism preserves their local
   dimensions. Step 1 gives equality of the local dimensions at the original points.
4. The identity supplies a point of `R`. Thus the defining supremum of all its local
   dimensions is the common value obtained in step 3. -/
theorem fieldGroupoid_localDimension_eq_dimension {S : Scheme.{u}} (K : Type u) [Field K]
    (b : Spec (CommRingCat.of K) ⟶ S) (R : AlgebraicSpace S)
    (s t : R.obj.obj ⟶ yoneda.obj (Over.mk b))
    (e : yoneda.obj (Over.mk b) ⟶ R.obj.obj) (i : R.obj.obj ⟶ R.obj.obj)
    (c : Limits.pullback s t ⟶ R.obj.obj) (hgroupoid : IsPresheafGroupoid s t e i c)
    (hs : ∀ (V : Over S) (a : yoneda.obj V ⟶ R.obj.obj)
      (f : V ⟶ Over.mk b), IsEtale a → a ≫ s = yoneda.map f →
        LocallyOfFiniteType f.left)
    (ht : ∀ (V : Over S) (a : yoneda.obj V ⟶ R.obj.obj)
      (f : V ⟶ Over.mk b), IsEtale a → a ≫ t = yoneda.map f →
        LocallyOfFiniteType f.left)
    (r : Point R.obj.obj) :
    etaleLocalDimension R.obj.obj r = etaleDimension R.obj.obj := by
  sorry

/-- A locally finite type group algebraic space over a field has its full dimension
at every point. Its group laws are the groupoid laws with source equal to target.
Source: Stacks Project, Tag 06FE(1)
(blueprint: lem-sfb-field-groupoid-constant-local-dimension).

Proof: specialize the preceding four-step groupoid argument to `s = t = p`, the
structural map of the group. Multiplication, identity and inverse give exactly
`IsPresheafGroupoid p p e i c`; the one chartwise locally finite type hypothesis
supplies both source and target hypotheses. Thus every local dimension equals
its defining global supremum, as asserted by the final step of the node. -/
theorem fieldGroup_localDimension_eq_dimension {S : Scheme.{u}} (K : Type u) [Field K]
    (b : Spec (CommRingCat.of K) ⟶ S) (H : AlgebraicSpace S)
    (p : H.obj.obj ⟶ yoneda.obj (Over.mk b))
    (e : yoneda.obj (Over.mk b) ⟶ H.obj.obj) (i : H.obj.obj ⟶ H.obj.obj)
    (c : Limits.pullback p p ⟶ H.obj.obj) (hgroup : IsPresheafGroupoid p p e i c)
    (hp : ∀ (V : Over S) (a : yoneda.obj V ⟶ H.obj.obj)
      (f : V ⟶ Over.mk b), IsEtale a → a ≫ p = yoneda.map f →
        LocallyOfFiniteType f.left)
    (h : Point H.obj.obj) :
    etaleLocalDimension H.obj.obj h = etaleDimension H.obj.obj := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
