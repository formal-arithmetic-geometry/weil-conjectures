/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Data.List.TFAE
import WeilConjectures.AlgebraicGeometry.FlatUnramifiedFormallyEtale
import WeilConjectures.AlgebraicGeometry.FirstOrderThickeningBaseChange

/-! # Formal unramifiedness on étale scheme charts

Source: Stacks Project, More on Morphisms of Spaces, Tag 04G8,
lemma-formally-unramified, conditions (1)--(3)
(blueprint: lem-sfb-space-formally-unramified-etale-charts).

The affine square-zero test is written out in the equivalence, rather than introducing
another definition of formal unramifiedness. Scheme specialization uses Mathlib's
`FormallyUnramified`. No representability or finiteness of the space morphism is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- The affine first-order uniqueness test for a scheme morphism agrees with Mathlib's
formal unramifiedness.
Source: Stacks, More on Morphisms, Tag 02H7; More on Morphisms of Spaces, Tag 04AL
(blueprint: lem-sfb-space-formally-unramified-etale-charts).

Proof: `FormallyUnramified.hom_ext` gives uniqueness for a closed immersion whose
kernel is square zero, since its kernel is nilpotent. Conversely, apply
`FormallyUnramified.of_hom_ext`: its tests are surjective ring maps with square-zero
kernel. Their spectrum maps are closed immersions with square-zero ideal sheaf,
hence first-order thickenings between affine schemes. The assumed uniqueness gives
exactly the equality required by that criterion. -/
theorem scheme_formallyUnramified_iff_affine_firstOrder {V U : Scheme.{u}} (g : V ⟶ U) :
    FormallyUnramified g ↔
      ∀ (T T' : Scheme.{u}) (i : T ⟶ T'), IsAffine T → IsAffine T' →
        IsFirstOrderThickening i → ∀ (a₁ a₂ : T' ⟶ V),
          a₁ ≫ g = a₂ ≫ g → i ≫ a₁ = i ≫ a₂ → a₁ = a₂ := by
  sorry

/-- Formal unramifiedness of an algebraic-space morphism is equivalent both to formal
unramifiedness on every compatible étale scheme chart and to its existence on one
compatible pair of surjective étale scheme charts.
Source: Stacks, More on Morphisms of Spaces, Tag 04G8, conditions (1)--(3)
(blueprint: lem-sfb-space-formally-unramified-etale-charts).

Proof, following the five steps of the node:
1. A representable étale map has unique lifts across affine square-zero thickenings:
base change it by the thickened test scheme. The resulting scheme projection is
flat and unramified, so [lem-weil-pbc-flat-unramified-formally-etale] supplies its
unique section extending the given reduced section. The pullback universal property
identifies these sections with the requested lifts.
2. Given (1), two lifts into a source chart with equal images in the target chart
have equal images in Z by (1). Uniqueness for the source chart from step 1 then
makes them equal. The scheme specialization above identifies this with (2).
3. Choose a surjective étale atlas of X. Compatible surjective charts exist by the
existence clause of [lem-sfb-unramified-etale-compatible-charts]; applying (2)
to them gives (3). This uses no unramifiedness assumption on f.
4. Given (3) and two lifts a,b into Z agreeing on the reduction, pull the source
atlas back along a, using [lem-trf-space-fibre-products-etale-covers]. Cover its
scheme source by affine opens A. Their reductions are affine first-order
thickenings by [lem-weil-pbc-first-order-thickening-base-change]. Step 1 lifts
the common reduced source-chart map over b. Uniqueness for the target chart
makes the two maps into U equal; formal unramifiedness of g then makes their
maps into V equal. Thus a and b agree after this étale cover.
5. These affine maps form an fppf cover: étale maps are flat and locally of finite
presentation, and the family is jointly surjective. The fppf sheaf condition for Z
detects equality, giving a=b and (1). The empty cover is allowed and detects equality
on the empty scheme. No local finite type, quasi-compactness or separation is used. -/
theorem space_formallyUnramified_etale_charts {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (f : Z ⟶ X) :
    List.TFAE [
      (∀ (T T' : Over S) (i : T ⟶ T'), IsAffine T.left → IsAffine T'.left →
        IsFirstOrderThickening i.left →
          ∀ (b : yoneda.obj T' ⟶ X.obj.obj) (a₁ a₂ : yoneda.obj T' ⟶ Z.obj.obj),
            a₁ ≫ f.hom.hom = b → a₂ ≫ f.hom.hom = b →
              yoneda.map i ≫ a₁ = yoneda.map i ≫ a₂ → a₁ = a₂),
      (∀ (V U : Over S) (p : yoneda.obj V ⟶ Z.obj.obj)
        (q : yoneda.obj U ⟶ X.obj.obj) (g : V ⟶ U),
          IsEtale p → IsEtale q → p ≫ f.hom.hom = yoneda.map g ≫ q →
            FormallyUnramified g.left),
      (∃ (V U : Over S) (p : yoneda.obj V ⟶ Z.obj.obj)
        (q : yoneda.obj U ⟶ X.obj.obj) (g : V ⟶ U),
          IsEtale p ∧ IsEtale q ∧ IsSurjective p ∧ IsSurjective q ∧
            p ≫ f.hom.hom = yoneda.map g ≫ q ∧ FormallyUnramified g.left)] := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
