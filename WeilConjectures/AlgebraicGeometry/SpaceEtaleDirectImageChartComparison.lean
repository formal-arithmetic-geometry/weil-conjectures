/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import WeilConjectures.AlgebraicGeometry.SpaceChartLimitEnlargedSections
import WeilConjectures.AlgebraicGeometry.LocalizeRingedSiteMorphismGeneral

/-! # Direct-image comparison under étale base change

Source: Stacks Project, Properties of Spaces, Tag 03LX, and Morphisms of Spaces,
Tag 03M8 (blueprint: lem-trf-etale-direct-image-chart-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}

/-- The direct-image part of étale base change, normalized on every scheme chart.
The explicitly constructed transport keeps the underlying scheme and map to `V`.
Source: Stacks Project, Properties of Spaces, Tag 03LX; Morphisms of Spaces,
Tag 03M8; Modules on Sites, Tag 04J0.
(blueprint: lem-trf-etale-direct-image-chart-comparison).

Proof: extend modules to the enlarged étale sites. The chart-limit theorem identifies
this direct image with `moduleDirectImage`, preserving all chart projections. Étale
postcomposition identifies the enlarged sites over `Y'` and `X'` with the corresponding
localized sites over `Y` and `X`. The given pullback square identifies the two base-change
functors: on a test object the map sends `(x,v)` to `((x,g_V(v)),v)` and its inverse forgets
the middle coordinate. Their structural ring maps pull back along the same chart maps.
Apply ringed-site localization to obtain the direct-image isomorphism, then conjugate by
the two projection-preserving chart-limit comparisons. On a scheme chart the coordinate
comparison keeps the scheme and its map to `V`, exactly the displayed transport. Hence
both sides of the asserted equation are the same restriction of the extended section.
The localization and chart comparisons are module maps natural in test objects and
modules, so their conjugate is the required natural module isomorphism. This uses no
surjectivity of `g`, nor any representability, finiteness or quasi-coherence of `f`. -/
theorem etale_directImage_chart_comparison
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : X' ⟶ X) (f' : X' ⟶ Y')
    (hg : IsEtale g.hom.hom) (hh : IsEtale h.hom.hom)
    (hp : IsPullback h.hom f'.hom f.hom g.hom) :
    let transport : ∀ V : Y'.EtaleSite, ModuleChart f' V →
        ModuleChart f ((etaleMap g hg).obj V) := fun V q ↦
      CostructuredArrow.mk (Y := (etaleMap h hh).obj q.left)
        (CostructuredArrow.homMk q.hom.left (by
          have hw : h.hom.hom ≫ f.hom.hom = f'.hom.hom ≫ g.hom.hom :=
            congrArg (fun k ↦ k.hom) hp.w
          have hq : yoneda.map q.hom.left ≫ V.obj.hom =
              q.left.obj.hom ≫ f'.hom.hom := by
            exact CostructuredArrow.w q.hom
          change yoneda.map q.hom.left ≫ (V.obj.hom ≫ g.hom.hom) =
            q.left.obj.hom ≫ h.hom.hom ≫ f.hom.hom
          rw [← Category.assoc, hq, Category.assoc, hw]))
    ∃ beta : moduleDirectImage f ⋙ pullback g hg ≅
        pullback h hh ⋙ moduleDirectImage f',
      ∀ (F : X.Modules) (V : Y'.EtaleSite) (q : ModuleChart f' V)
        (s : ((moduleDirectImage f).obj F).val.obj (op ((etaleMap g hg).obj V))),
        ((moduleDirectImageModel f').projection ((pullback h hh).obj F) V).app (op q)
            ((beta.hom.app F).val.app (op V) s) =
          ((moduleDirectImageModel f).projection F ((etaleMap g hg).obj V)).app
            (op (transport V q)) s := by sorry

end AlgebraicGeometry.AlgebraicSpace
