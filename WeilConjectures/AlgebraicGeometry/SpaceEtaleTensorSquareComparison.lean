/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModuleOperations
import WeilConjectures.AlgebraicGeometry.SpaceChartTensorRealization

/-! # Tensor pullbacks through an étale commutative square

Source: Stacks Project, Properties of Spaces, Tag 03LX, pullback-comparison footnote,
and Tags 03LV and 03LW (blueprint: lem-trf-etale-tensor-square-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}

/-- Tensor pullbacks agree around a commutative square with étale horizontal arrows.
On local tensors the comparison multiplies the two regular-function coefficients.
No cartesian hypothesis is needed for this pullback-composition assertion.
Source: Stacks Project, Properties of Spaces, Tag 03LX, pullback-comparison footnote,
and Tags 03LV and 03LW; Modules on Sites, Tags 03D7 and 03D8.
(blueprint: lem-trf-etale-tensor-square-comparison).

Proof: apply the normalized chart tensor-realization theorem to the pairs `(f,h)` and
`(g,f')`. Its composition comparisons identify the two iterated pullbacks with pullback
along `h ≫ f` and `f' ≫ g`; the commuting square identifies those morphisms. Identify the
pullbacks along `g` and `h` with literal étale restriction, using the multiplication and
insertion-of-one isomorphisms of that theorem. Conjugating the composition comparisons
by these restriction isomorphisms gives the asserted natural isomorphism. To compute
its value, first express an étale-restricted section as `1 ⊗` that section. The first
composition map sends `a ⊗ (b ⊗ m)` to `(a*b) ⊗ m` on the unchanged scheme chart.
The inverse composition on the other path inserts the inner unit. Étale multiplication
then removes that unit and leaves `m` unchanged. Both coefficients are regular functions
on the same scheme, so their pullbacks along the identity chart arrow are unchanged.
Balancing proves the inverse identities before sheafification, and the unit-normalized
chart comparisons carry these local formulas to the specified tensor adjunctions.
Empty charts and zero modules cause no exception, and no section is assumed globally
to be a pure tensor. -/
theorem etale_tensor_square_comparison
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : X' ⟶ X) (f' : X' ⟶ Y')
    (hg : IsEtale g.hom.hom) (hh : IsEtale h.hom.hom)
    (w : h.hom ≫ f.hom = f'.hom ≫ g.hom) :
    let transport : ∀ V : Y'.EtaleSite, ModuleChart f' V →
        ModuleChart f ((etaleMap g hg).obj V) := fun V q ↦
      CostructuredArrow.mk (Y := (etaleMap h hh).obj q.left)
        (CostructuredArrow.homMk q.hom.left (by
          have hw : h.hom.hom ≫ f.hom.hom = f'.hom.hom ≫ g.hom.hom :=
            congrArg (fun k ↦ k.hom) w
          have hq : yoneda.map q.hom.left ≫ V.obj.hom =
              q.left.obj.hom ≫ f'.hom.hom := by
            exact CostructuredArrow.w q.hom
          change yoneda.map q.hom.left ≫ (V.obj.hom ≫ g.hom.hom) =
            q.left.obj.hom ≫ h.hom.hom ≫ f.hom.hom
          rw [← Category.assoc, hq, Category.assoc, hw]))
    ∃ lambda : moduleTensorPullback f ⋙ pullback h hh ≅
        pullback g hg ⋙ moduleTensorPullback f',
      ∀ (M : Y.Modules) (V : Y'.EtaleSite) (q : ModuleChart f' V)
        (a b : X'.structureSheaf.obj.obj (op q.left))
        (m : M.val.obj (op ((etaleMap g hg).obj V))),
        (lambda.hom.app M).val.app (op q.left)
            (a • moduleTensorSection f M ((etaleMap g hg).obj V) (transport V q) b m) =
          moduleTensorSection f' ((pullback g hg).obj M) V q (a * b) m := by sorry

end AlgebraicGeometry.AlgebraicSpace
