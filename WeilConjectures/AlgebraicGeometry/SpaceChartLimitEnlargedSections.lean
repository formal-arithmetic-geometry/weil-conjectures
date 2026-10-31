/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmallEnlargedEtaleModules
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModuleOperations

/-!
# All-chart module limits are enlarged étale sections

Source: Stacks Project, Tags 03G1, 03H7, 03G8, 03M8, 03LX and 041F
(blueprint: lem-trf-space-chart-limit-enlarged-sections).

The cone vertex has coefficient universe `u`, although all scheme charts form a category
in universe `u+1`. Its projections are restrictions on the actual enlarged fibre product.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Enlarged-site module direct image transported through the normalized equivalences.
Source: Stacks, Tags 03G8 and 03M8
(blueprint: lem-trf-space-chart-limit-enlarged-sections). -/
def enlargedSmallModuleDirectImage (f : X ⟶ Y) : X.Modules ⥤ Y.Modules :=
  (smallEnlargedModuleEquivalence.{u, u} X).inverse ⋙
    SheafOfModules.pushforward (enlargedStructuralMap f) ⋙
    smallEnlargedModuleRestriction Y

/-- The canonical arrow from a chart triangle to the enlarged fibre product.
Source: Stacks, Tags 03G8 and 03M8
(blueprint: lem-trf-space-chart-limit-enlarged-sections). -/
def enlargedModuleChartLift (f : X ⟶ Y) (V : Y.EtaleSite) (q : ModuleChart f V) :
    (enlargedSchemeInclusion X).obj q.left ⟶
      (enlargedBaseChange f).obj ((enlargedSchemeInclusion Y).obj V) :=
  enlargedChartLift f q.left V q.hom.left q.hom.w

/-- Restrict an enlarged section to the scheme chart, then use the extension counit.
Source: Stacks, Tags 03H7 and 03M8
(blueprint: lem-trf-space-chart-limit-enlarged-sections). -/
def enlargedModuleChartRestriction (f : X ⟶ Y) (F : X.Modules) (V : Y.EtaleSite)
    (q : ModuleChart f V)
    (s : ((enlargedSmallModuleDirectImage f).obj F).val.obj (op V)) :
    F.val.obj (op q.left) :=
  (((smallEnlargedModuleEquivalence.{u, u} X).counitIso.hom.app F).val.app (op q.left))
    (((smallEnlargedModuleEquivalence.{u, u} X).inverse.obj F).val.map
      (enlargedModuleChartLift f V q).op s)

/-- Restrictions are additive and linear for exactly the chart's pullback of functions.
Source: Stacks, Tags 03G8 and 03M8
(blueprint: lem-trf-space-chart-limit-enlarged-sections).
Proof: the structural ring map is normalized on scheme charts by pullback of functions.
Semilinearity of restriction and linearity of the extension counit give scalar
compatibility; their underlying additive maps give preservation of addition. -/
theorem enlargedModuleChartRestriction_linear (f : X ⟶ Y) (F : X.Modules)
    (V : Y.EtaleSite) (q : ModuleChart f V) :
    (∀ s t, enlargedModuleChartRestriction f F V q (s + t) =
      enlargedModuleChartRestriction f F V q s + enlargedModuleChartRestriction f F V q t) ∧
    (∀ (r : Y.structureSheaf.obj.obj (op V)) s,
      enlargedModuleChartRestriction f F V q (r • s) =
        moduleChartScalar f V q r • enlargedModuleChartRestriction f F V q s) := by
  let H := (smallEnlargedModuleEquivalence.{u, u} X).inverse.obj F
  let ε := ((smallEnlargedModuleEquivalence.{u, u} X).counitIso.hom.app F).val
  constructor
  · intro s t
    change H.val.obj
      (op ((enlargedBaseChange f).obj ((enlargedSchemeInclusion Y).obj V))) at s t
    exact (congrArg (ε.app (op q.left))
      ((H.val.map (enlargedModuleChartLift f V q).op).hom.map_add s t)).trans
        ((ε.app (op q.left)).hom.map_add _ _)
  · intro r s
    change H.val.obj
      (op ((enlargedBaseChange f).obj ((enlargedSchemeInclusion Y).obj V))) at s
    have hn := (enlargedStructuralMap_existsUnique f).choose_spec.1
      q.left V q.hom.left q.hom.w
    have hr :
        X.enlargedStructureSheaf.obj.map (enlargedModuleChartLift f V q).op
            ((enlargedStructuralMap f).hom.app (op ((enlargedSchemeInclusion Y).obj V))
              ((enlargedStructureRestriction Y).inv.hom.app (op V) r)) =
          (enlargedStructureRestriction X).inv.hom.app (op q.left)
            (moduleChartScalar f V q r) := by
      have he := ConcreteCategory.congr_hom hn r
      change (enlargedStructureRestriction X).hom.hom.app (op q.left)
          (X.enlargedStructureSheaf.obj.map (enlargedModuleChartLift f V q).op
            ((enlargedStructuralMap f).hom.app (op ((enlargedSchemeInclusion Y).obj V))
              ((enlargedStructureRestriction Y).inv.hom.app (op V) r))) =
        moduleChartScalar f V q r at he
      have hi := ConcreteCategory.congr_hom
        (congrArg (fun k ↦ k.hom.app (op q.left))
          (enlargedStructureRestriction X).hom_inv_id)
        (X.enlargedStructureSheaf.obj.map (enlargedModuleChartLift f V q).op
          ((enlargedStructuralMap f).hom.app (op ((enlargedSchemeInclusion Y).obj V))
            ((enlargedStructureRestriction Y).inv.hom.app (op V) r)))
      change (enlargedStructureRestriction X).inv.hom.app (op q.left)
          ((enlargedStructureRestriction X).hom.hom.app (op q.left) _) = _ at hi
      rw [he] at hi
      exact hi.symm
    let rf : X.enlargedStructureSheaf.obj.obj
        (op ((enlargedBaseChange f).obj ((enlargedSchemeInclusion Y).obj V))) :=
      (enlargedStructuralMap f).hom.app (op ((enlargedSchemeInclusion Y).obj V))
        ((enlargedStructureRestriction Y).inv.hom.app (op V) r)
    change ε.app (op q.left)
        (H.val.map (enlargedModuleChartLift f V q).op (rf • s)) = _
    rw [H.val.map_smul]
    dsimp only [rf]
    rw [hr]
    exact (ε.app (op q.left)).hom.map_smul (moduleChartScalar f V q r) _

/-- Linear projection of the enlarged section module to one chart.
Source: Stacks, Tags 03H7 and 03M8
(blueprint: lem-trf-space-chart-limit-enlarged-sections). -/
def enlargedModuleChartProjection (f : X ⟶ Y) (F : X.Modules) (V : Y.EtaleSite)
    (q : ModuleChart f V) :
    ((enlargedSmallModuleDirectImage f).obj F).val.obj (op V) ⟶
      (moduleChartDiagram f F V).obj (op q) :=
  ModuleCat.ofHom
    (X := ((enlargedSmallModuleDirectImage f).obj F).val.obj (op V))
    (Y := (moduleChartDiagram f F V).obj (op q))
    { toFun := enlargedModuleChartRestriction f F V q
      map_add' := (enlargedModuleChartRestriction_linear f F V q).1
      map_smul' := (enlargedModuleChartRestriction_linear f F V q).2 }

set_option maxHeartbeats 800000 in
-- The nested module restrictions require extra definitional equality checks.
/-- All chart restrictions form a natural cone.
Source: Stacks, Tags 03H7 and 03M8
(blueprint: lem-trf-space-chart-limit-enlarged-sections).
Proof: an arrow of chart triangles gives the composite arrow into the fibre product.
Functoriality of the extended module and naturality of its restriction counit identify
the two restrictions. Their scalar maps agree by the commuting triangle. -/
theorem enlargedModuleChartProjection_naturality (f : X ⟶ Y) (F : X.Modules)
    (V : Y.EtaleSite) {q r : (ModuleChart f V)ᵒᵖ} (a : q ⟶ r) :
    enlargedModuleChartProjection f F V q.unop ≫ (moduleChartDiagram f F V).map a =
      enlargedModuleChartProjection f F V r.unop := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let H := (smallEnlargedModuleEquivalence.{u, u} X).inverse.obj F
  let ε := ((smallEnlargedModuleEquivalence.{u, u} X).counitIso.hom.app F).val
  have hl : (enlargedSchemeInclusion X).map a.unop.left ≫
      enlargedModuleChartLift f V q.unop = enlargedModuleChartLift f V r.unop := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    apply Limits.pullback.hom_ext
    · apply Sheaf.hom_ext
      simp [enlargedSchemeInclusion, enlargedModuleChartLift, enlargedChartLift]
    · have he : a.unop.left.hom.left ≫ q.unop.hom.left = r.unop.hom.left :=
        congrArg (fun k ↦ k.left) a.unop.w
      simp only [enlargedSchemeInclusion, Over.mk_left, Over.mk_hom,
        ObjectProperty.homMk_hom, enlargedModuleChartLift, enlargedChartLift,
        ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Over.homMk_left,
        Category.assoc, limit.lift_π, PullbackCone.mk_π_app]
      apply Sheaf.hom_ext
      change yoneda.map a.unop.left.hom.left ≫ yoneda.map q.unop.hom.left = _
      rw [← Functor.map_comp, he]
      rfl
  change H.val.obj
    (op ((enlargedBaseChange f).obj ((enlargedSchemeInclusion Y).obj V))) at s
  change F.val.map a.unop.left.op
      (ε.app (op q.unop.left) (H.val.map (enlargedModuleChartLift f V q.unop).op s)) =
    ε.app (op r.unop.left) (H.val.map (enlargedModuleChartLift f V r.unop).op s)
  have hn := PresheafOfModules.naturality_apply ε a.unop.left.op
    (H.val.map (enlargedModuleChartLift f V q.unop).op s)
  change ε.app (op r.unop.left)
      (H.val.map ((enlargedSchemeInclusion X).map a.unop.left).op
        (H.val.map (enlargedModuleChartLift f V q.unop).op s)) =
    F.val.map a.unop.left.op
      (ε.app (op q.unop.left) (H.val.map (enlargedModuleChartLift f V q.unop).op s)) at hn
  refine hn.symm.trans (congrArg (ε.app (op r.unop.left)) ?_)
  exact (H.val.map_comp_apply _ _ s).symm.trans
    (H.val.congr_map_apply (by rw [← op_comp, hl]) s)

/-- The specified cone on all charts, with a small enlarged-section vertex.
Source: Stacks, Tags 03H7 and 03M8
(blueprint: lem-trf-space-chart-limit-enlarged-sections). -/
def enlargedModuleChartCone (f : X ⟶ Y) (F : X.Modules) (V : Y.EtaleSite) :
    Cone (moduleChartDiagram f F V) where
  pt := ((enlargedSmallModuleDirectImage f).obj F).val.obj (op V)
  π := { app := fun q ↦ enlargedModuleChartProjection f F V q.unop
         naturality := fun _ _ a ↦ by
           simpa using (enlargedModuleChartProjection_naturality f F V a).symm }

/-- The all-chart cone is limiting with its small vertex; every atlas gives its
normalized equalizer, and the comparisons are natural in modules and test schemes.
Source: Stacks, Tags 03G1, 03H7, 03G8 and 03M8
(blueprint: lem-trf-space-chart-limit-enlarged-sections).
Proof, following Steps 1--7 of the node:
1. A chart triangle is uniquely a scheme map into `W = X ×_Y V`; permanence makes it
   étale. An atlas of `W` and its scheme overlap are therefore chart objects.
2. The normalized structural ring map makes each displayed restriction linear over
   `Γ(V,O_V)`, via exactly `a♯` on the chart; restrictions form the displayed cone.
3. For any surjective étale scheme atlas, the sheaf equalizer computes the extension
   on `W`. It is a submodule of the small atlas section module, so is small.
4. Any cone maps to this equalizer through its atlas component. Injectivity on that
   atlas proves linearity and uniqueness of the induced map into the vertex.
5. On an arbitrary chart use its pullback of the atlas. Cone compatibility identifies
   the two restrictions there; sheaf injectivity makes them equal on the chart.
6. Restrictions and the extension counit commute with module maps and with test-scheme
   maps, the latter semilinearly over pullback of functions. Thus all comparisons do.
7. The transported ringed direct image has this very vertex and scalar action.
   The two limit properties give the unique natural isomorphism preserving every
   chart projection; its composites are identities by the same uniqueness. -/
theorem space_chart_limit_enlarged_sections (f : X ⟶ Y) :
    (∀ (F : X.Modules) (V : Y.EtaleSite),
      Nonempty (IsLimit (enlargedModuleChartCone f F V))) ∧
    (∀ (F : X.Modules) (V : Y.EtaleSite) (q₀ q₁ : ModuleChart f V)
      (p r : q₁ ⟶ q₀),
      IsEtale (enlargedModuleChartLift f V q₀).hom.left.hom.hom →
      IsSurjective (enlargedModuleChartLift f V q₀).hom.left.hom.hom →
      IsPullback ((enlargedSchemeInclusion X).map p.left)
        ((enlargedSchemeInclusion X).map r.left)
        (enlargedModuleChartLift f V q₀) (enlargedModuleChartLift f V q₀) →
      ∃ e : ((enlargedSmallModuleDirectImage f).obj F).val.obj (op V) ≃ₗ[
          Y.structureSheaf.obj.obj (op V)]
          LinearMap.ker ((moduleChartMap f F V p).hom - (moduleChartMap f F V r).hom),
        ∀ s, (e s).val = enlargedModuleChartRestriction f F V q₀ s) ∧
    (∀ (F G : X.Modules) (b : F ⟶ G) (V : Y.EtaleSite) (q : ModuleChart f V) s,
      enlargedModuleChartRestriction f G V q
          (((enlargedSmallModuleDirectImage f).map b).val.app (op V) s) =
        b.val.app (op q.left) (enlargedModuleChartRestriction f F V q s)) ∧
    (∀ (F : X.Modules) (V₁ V₂ : Y.EtaleSite) (c : V₁ ⟶ V₂)
      (q : ModuleChart f V₁) s,
      enlargedModuleChartRestriction f F V₁ q
          (((enlargedSmallModuleDirectImage f).obj F).val.map c.op s) =
        enlargedModuleChartRestriction f F V₂ ((moduleChartPost f c).obj q) s) ∧
    (∃! α : moduleDirectImage f ≅ enlargedSmallModuleDirectImage f,
      ∀ (F : X.Modules) (V : Y.EtaleSite) (q : ModuleChart f V) s,
        enlargedModuleChartRestriction f F V q ((α.hom.app F).val.app (op V) s) =
          ((moduleDirectImageModel f).projection F V).app (op q) s) := by
  sorry

/-- The second projection of the actual algebraic-space fibre product.
Source: Stacks, Tag 03LX
(blueprint: lem-trf-space-chart-limit-enlarged-sections). -/
def enlargedModuleBaseChangeSnd {Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    enlargedFibreProduct f g ⟶ Y' :=
  ObjectProperty.homMk (Limits.pullback.snd f.hom g.hom)

/-- The localization comparison retains coordinates, chart schemes, arrows, projections
and coefficient pullbacks, without assuming representability of `f` or surjectivity of `g`.
Source: Stacks, Tags 03LX, 03LP, 03G8 and 041F
(blueprint: lem-trf-space-chart-limit-enlarged-sections).
Proof, following Steps 8--9 of the node:
8. Base change makes `h` chartwise étale. The enlarged model identifies postcomposition
   with localization, preserving covers and the restricted structure ring. A section
   `(x,v)` maps to `((x,g_V(v)),v)` in the other fibre product; its inverse forgets
   the middle coordinate. The fibre-product equation forces that coordinate, proving
   the inverse identities and naturality on every enlarged object and arrow.
9. A scheme chart keeps the same scheme and the same arrow to `V`; only the extra
   coordinate is inserted. This gives inverse functors on chart triangles. The two
   arrows into the fibre products commute with the coordinate comparison. Applying
   any extended module identifies all cone projections, by restriction functoriality.
   The map to `V` is unchanged, so its pullback on regular functions is unchanged.
   The chart-normalized structural ring maps therefore agree as well. No step
   requires the original map to be representable or the étale map to be surjective. -/
theorem space_chart_limit_enlarged_localization {Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hg : IsChartwiseEtale g) :
    ∃ hh : IsChartwiseEtale (enlargedFibreProductFst f g),
      ∃ e : enlargedPostcompose g hg ⋙ enlargedBaseChange f ≅
          enlargedBaseChange (enlargedModuleBaseChangeSnd f g) ⋙
            enlargedPostcompose (enlargedFibreProductFst f g) hh,
        (∀ V : Y'.EnlargedEtaleSite,
          (e.hom.app V).hom.left.hom ≫
              Limits.pullback.fst (enlargedModuleBaseChangeSnd f g).hom V.obj.hom.hom ≫
              Limits.pullback.fst f.hom g.hom =
            Limits.pullback.fst f.hom ((enlargedPostcompose g hg).obj V).obj.hom.hom) ∧
        (∀ V : Y'.EnlargedEtaleSite,
          (e.hom.app V).hom.left.hom ≫
              Limits.pullback.snd (enlargedModuleBaseChangeSnd f g).hom V.obj.hom.hom =
            Limits.pullback.snd f.hom ((enlargedPostcompose g hg).obj V).obj.hom.hom) ∧
        (∀ V : Y'.EnlargedEtaleSite,
          (e.inv.app V).hom.left.hom ≫
              Limits.pullback.fst f.hom ((enlargedPostcompose g hg).obj V).obj.hom.hom =
            Limits.pullback.fst (enlargedModuleBaseChangeSnd f g).hom V.obj.hom.hom ≫
              Limits.pullback.fst f.hom g.hom) ∧
        (∀ V : Y'.EnlargedEtaleSite,
          (e.inv.app V).hom.left.hom ≫
              Limits.pullback.snd f.hom ((enlargedPostcompose g hg).obj V).obj.hom.hom =
            Limits.pullback.snd (enlargedModuleBaseChangeSnd f g).hom V.obj.hom.hom) ∧
        ∀ V : Y'.EtaleSite,
          ∃ E : ModuleChart (enlargedModuleBaseChangeSnd f g) V ≌
              ModuleChart f ((chartwiseEtaleMap g hg).obj V),
            (∀ q, (E.functor.obj q).left.obj.left = q.left.obj.left) ∧
            (∀ (q r : ModuleChart (enlargedModuleBaseChangeSnd f g) V) (a : q ⟶ r),
              HEq (E.functor.map a).left.hom.left a.left.hom.left) ∧
            (∀ q, HEq (E.functor.obj q).hom.left q.hom.left) ∧
            (∀ q, HEq
              (moduleChartScalar f ((chartwiseEtaleMap g hg).obj V) (E.functor.obj q))
              (moduleChartScalar (enlargedModuleBaseChangeSnd f g) V q)) ∧
            ∀ q,
              ∃ i : (enlargedSchemeInclusion X).obj (E.functor.obj q).left ≅
                  (enlargedPostcompose (enlargedFibreProductFst f g) hh).obj
                    ((enlargedSchemeInclusion (enlargedFibreProduct f g)).obj q.left),
                HEq i.hom.hom.left.hom (𝟙 (schemeSpace q.left.obj.left).obj) ∧
                (enlargedModuleChartLift f ((chartwiseEtaleMap g hg).obj V)
                    (E.functor.obj q) ≫
                    e.hom.app ((enlargedSchemeInclusion Y').obj V) =
                  i.hom ≫ (enlargedPostcompose (enlargedFibreProductFst f g) hh).map
                    (enlargedModuleChartLift (enlargedModuleBaseChangeSnd f g) V q)) ∧
                ∀ (H : ringedSiteModules.{u} X.enlargedStructureSheaf) s,
                  H.val.map
                      (enlargedModuleChartLift f ((chartwiseEtaleMap g hg).obj V)
                        (E.functor.obj q)).op
                      (H.val.map (e.hom.app ((enlargedSchemeInclusion Y').obj V)).op s) =
                    H.val.map i.hom.op
                      (H.val.map ((enlargedPostcompose
                        (enlargedFibreProductFst f g) hh).map
                        (enlargedModuleChartLift
                          (enlargedModuleBaseChangeSnd f g) V q)).op s) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
