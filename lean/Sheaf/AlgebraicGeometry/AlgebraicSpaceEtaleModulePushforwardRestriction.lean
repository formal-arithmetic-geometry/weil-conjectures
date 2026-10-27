/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Sheaf.AlgebraicGeometry.SpaceChartTensorRealization
import Sheaf.AlgebraicGeometry.SpaceEtaleDirectImageChartComparison
import Sheaf.AlgebraicGeometry.SpaceEtaleTensorSquareComparison
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Étale localization and module direct images on algebraic spaces

Source: Stacks Project, Properties of Spaces, Tags 03LX, 03LV and 03LW; Morphisms of
Algebraic Spaces, Tag 03M8; Modules on Sites, Tag 04J0
(blueprint: lem-trf-space-etale-module-pushforward-restriction).

The direct images are fixed by their limits of compatible sections on scheme charts.
The tensor pullbacks retain their actual units. Thus the formulas below normalize the
comparison isomorphisms on sections and on local tensors, including their scalar action.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}

/-- Inverse image on ring sheaves along an étale map is restriction of the small sites.
Source: Stacks, Tags 03LP, 03LV and 03LW
(blueprint: lem-trf-space-etale-module-pushforward-restriction). -/
def etaleRingRestriction (g : Y' ⟶ Y) (hg : IsEtale g.hom.hom) :
    Sheaf Y.etaleTopology RingCat.{u} ⥤ Sheaf Y'.etaleTopology RingCat.{u} :=
  letI := etaleMap_isContinuous g hg
  (etaleMap g hg).sheafPushforwardContinuous RingCat.{u} Y'.etaleTopology Y.etaleTopology

/-- Restriction of the structure sheaf is the structure sheaf with identical regular
functions, ring operations and restriction maps.
Source: Stacks, Tags 03LV and 03LW
(blueprint: lem-trf-space-etale-module-pushforward-restriction). -/
def etaleStructureRestrictionIso (g : Y' ⟶ Y) (hg : IsEtale g.hom.hom) :
    (etaleRingRestriction g hg).obj Y.structureSheaf ≅ Y'.structureSheaf :=
  Iso.refl _

/-- An étale chart triangle is also a morphism of the small étale site of the target.
Source: Stacks, Tags 03LP and 03LV
(blueprint: lem-trf-space-etale-module-pushforward-restriction). -/
def moduleChartEtaleHom (g : Y' ⟶ Y) (hg : IsEtale g.hom.hom) (V : Y.EtaleSite)
    (q : ModuleChart g V) : (etaleMap g hg).obj q.left ⟶ V :=
  ⟨q.hom⟩

/-- Restriction is tensor pullback, normalized by `a ⊗ m ↦ a m` on every local tensor.
The ring identification is the explicit `etaleStructureRestrictionIso` above.
Source: Stacks, Tags 03LV and 03LW
(blueprint: lem-trf-space-etale-module-pushforward-restriction).

Proof: in the enlarged étale ringed-site model, localization leaves the rings and their
maps unchanged. Hence tensor pullback is `𝒪 ⊗_𝒪 (-)`. Multiplication sends `a ⊗ m` to
`am`, and the inverse sends `m` to `1 ⊗ m`. Balancing gives `1 ⊗ am = a ⊗ m`, so these
maps are inverse locally before sheafification. They commute with restrictions and module
maps, hence define the natural isomorphism. The adjunction unit is `m ↦ 1 ⊗ m`, which
identifies the formula here with `moduleTensorSection`. No section is assumed globally
to be a pure tensor, and no surjectivity hypothesis on the étale map is used. -/
theorem moduleTensorPullback_etale_restriction (g : Y' ⟶ Y) (hg : IsEtale g.hom.hom) :
    ∃ e : moduleTensorPullback g ≅ pullback g hg,
      ∀ (M : Y.Modules) (V : Y.EtaleSite) (q : ModuleChart g V)
        (a : Y'.structureSheaf.obj.obj (op q.left)) (m : M.val.obj (op V)),
        (e.hom.app M).val.app (op q.left) (moduleTensorSection g M V q a m) =
          a • M.val.map (moduleChartEtaleHom g hg V q).op m := by
  have hgc : IsChartwiseEtale g := fun T a ha ↦ isEtale_comp a g.hom.hom ha hg
  obtain ⟨L, _, _, σ, hσ, _, _⟩ :=
    (space_chart_adjunction_tensor_realization g (𝟙 Y')).2 Y' Y g hgc
  refine ⟨L.comparison ≪≫ σ, ?_⟩
  intro M V q a m
  change (σ.hom.app M).val.app (op q.left)
    ((L.comparison.hom.app M).val.app (op q.left)
      (moduleTensorSection g M V q a m)) = _
  rw [L.chartTensor]
  exact hσ M V q a m

/-- Commutativity of the ringed square supplies the triangle on the same chart scheme.
Source: Stacks, Tags 03LX and 03M8
(blueprint: lem-trf-space-etale-module-pushforward-restriction).
Proof: the chart triangle for `q`, followed by `g`, is the required triangle because
`h ≫ f = f' ≫ g`. Associativity gives equality of the two natural transformations. -/
theorem moduleChartBaseChange_triangle
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : X' ⟶ X) (f' : X' ⟶ Y')
    (hg : IsEtale g.hom.hom) (hh : IsEtale h.hom.hom) (w : h.hom ≫ f.hom = f'.hom ≫ g.hom)
    (V : Y'.EtaleSite) (q : ModuleChart f' V) :
    yoneda.map q.hom.left ≫ ((etaleMap g hg).obj V).obj.hom =
      ((moduleChartTarget f).obj ((etaleMap h hh).obj q.left)).hom := by
  have hw : h.hom.hom ≫ f.hom.hom = f'.hom.hom ≫ g.hom.hom :=
    congrArg (fun k ↦ k.hom) w
  have hq : yoneda.map q.hom.left ≫ V.obj.hom =
      q.left.obj.hom ≫ f'.hom.hom := by
    exact CostructuredArrow.w q.hom
  change yoneda.map q.hom.left ≫ (V.obj.hom ≫ g.hom.hom) =
    q.left.obj.hom ≫ h.hom.hom ≫ f.hom.hom
  rw [← Category.assoc, hq, Category.assoc, hw]

/-- The same scheme chart, regarded as a chart of `X ×_Y V` through the square.
Source: Stacks, Tags 03LX and 03M8
(blueprint: lem-trf-space-etale-module-pushforward-restriction). -/
def moduleChartBaseChange
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : X' ⟶ X) (f' : X' ⟶ Y')
    (hg : IsEtale g.hom.hom) (hh : IsEtale h.hom.hom) (w : h.hom ≫ f.hom = f'.hom ≫ g.hom)
    (V : Y'.EtaleSite) (q : ModuleChart f' V) :
    ModuleChart f ((etaleMap g hg).obj V) :=
  CostructuredArrow.mk (Y := (etaleMap h hh).obj q.left)
    (CostructuredArrow.homMk q.hom.left
      (moduleChartBaseChange_triangle f g h f' hg hh w V q))

/-- Degree-zero étale base change of arbitrary module direct images, and the canonical
comparison between the two tensor-pullback paths. The square is a fibre product of the
underlying fppf sheaves; `f` is arbitrary and only `g` is assumed étale. The first equation
says that the direct-image comparison keeps every compatible chart section unchanged.
The second sends `a ⊗ (b ⊗ m)` to `(a * b) ⊗ m` after étale restriction: both scalar
coefficients are viewed on the same underlying chart scheme. These equations specify the
canonical comparisons, and the isomorphisms themselves encode all restriction and module
naturality. The commutativity used in the chart formula is supplied by the pullback square itself.

Source: Stacks, Tags 03LX, 03LV, 03LW and 03M8
(blueprint: lem-trf-space-etale-module-pushforward-restriction).

Proof:
1. Use the enlarged étale ringed-site model to compute sections on an étale algebraic
space as compatible sections on its scheme charts. The functor for `f` sends `V` to
`X ×_Y V`, including when this fibre product is not a scheme.
2. For any étale map, localization preserves the structure sheaf. The multiplication and
unit tensor maps of `moduleTensorPullback_etale_restriction` identify tensor pullback with
restriction, including its module structure.
3. Base-change the jointly surjective étale family `{g, id_Y}` along `f`. Its first member
is `h`, so `h` is étale even if `g` is not surjective. The two localized functors agree
via `X ×_Y V ≅ X' ×_{Y'} V`, with the same regular-function pullbacks on every chart.
4. Apply ringed-site localization (Tag 04J0). Both direct images have exactly the same
compatible sections; the component is identity on every chart and respects scalars,
restrictions in `V`, and maps in the module.
5. The corresponding tensor-pullback comparison identifies both paths with
`𝒪_{X'} ⊗_{(fh)^{-1}𝒪_Y} (fh)^{-1}M`. Locally the two associativity maps multiply the
outer coefficient by the pulled-back inner coefficient and keep `m` unchanged; their
inverse inserts `1`. Balancing proves the inverse identities before sheafification.
Under the étale restrictions both coefficients are functions on the same chart, giving
the product `a * b` in the formula below. -/
theorem etale_module_pushforward_restriction
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : X' ⟶ X) (f' : X' ⟶ Y')
    (hg : IsEtale g.hom.hom) (hp : IsPullback h.hom f'.hom f.hom g.hom) :
    ∃ hh : IsEtale h.hom.hom,
      ∃ (beta : moduleDirectImage f ⋙ pullback g hg ≅
          pullback h hh ⋙ moduleDirectImage f')
        (lambda : moduleTensorPullback f ⋙ pullback h hh ≅
          pullback g hg ⋙ moduleTensorPullback f'),
        (∀ (F : X.Modules) (V : Y'.EtaleSite) (q : ModuleChart f' V)
          (s : ((moduleDirectImage f).obj F).val.obj
            (op ((etaleMap g hg).obj V))),
          ((moduleDirectImageModel f').projection ((pullback h hh).obj F) V).app (op q)
              ((beta.hom.app F).val.app (op V) s) =
            ((moduleDirectImageModel f).projection F ((etaleMap g hg).obj V)).app
              (op (moduleChartBaseChange f g h f' hg hh hp.w V q)) s) ∧
        (∀ (M : Y.Modules) (V : Y'.EtaleSite) (q : ModuleChart f' V)
          (a b : X'.structureSheaf.obj.obj (op q.left))
          (m : M.val.obj (op ((etaleMap g hg).obj V))),
          (lambda.hom.app M).val.app (op q.left)
              (a • moduleTensorSection f M ((etaleMap g hg).obj V)
                (moduleChartBaseChange f g h f' hg hh hp.w V q) b m) =
            moduleTensorSection f' ((pullback g hg).obj M) V q (a * b) m) := by
  have hh : IsEtale h.hom.hom :=
    representableWith_baseChange _
      ((sheafToPresheaf _ _).map_isPullback hp.flip) hg
  obtain ⟨beta, hbeta⟩ := etale_directImage_chart_comparison f g h f' hg hh hp
  obtain ⟨lambda, hlambda⟩ := etale_tensor_square_comparison f g h f' hg hh hp.w
  exact ⟨hh, beta, lambda, hbeta, hlambda⟩

end AlgebraicGeometry.AlgebraicSpace
