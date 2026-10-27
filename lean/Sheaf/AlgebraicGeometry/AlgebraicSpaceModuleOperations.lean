/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-!
# Canonical module operations on the small étale sites of algebraic spaces

Source: Stacks Project, Properties of Spaces, Tags 03G8, 03H7 and 03LV;
Morphisms of Algebraic Spaces, Tag 03M8; Modules on Sites, Tag 03D7
(blueprint: def-trf-space-etale-module-functors).

A direct image is specified by a limit of sections on ALL étale scheme charts, together
with the restriction and module-map identities for the limit projections. This universal
property determines the functor up to its unique normalized natural isomorphism. Tensor
pullback is the left adjoint to this direct image, with its adjunction unit retained.
No arbitrary functor or unnormalized comparison is supplied as a hypothesis.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}

/-- The functor forgetting étaleness after composing a scheme chart with `f`.
Source: Stacks, Tags 03G2 and 03M8 (blueprint: def-trf-space-etale-module-functors). -/
def moduleChartTarget (f : X ⟶ Y) :
    X.EtaleSite ⥤ CostructuredArrow yoneda Y.obj.obj :=
  ObjectProperty.ι _ ⋙ CostructuredArrow.map f.hom.hom

/-- Scheme charts of `X ×_Y V`, with their maps to `X` and `V` and the commuting triangle.
Source: Stacks, Tags 03H7 and 03M8 (blueprint: def-trf-space-etale-module-functors). -/
abbrev ModuleChart (f : X ⟶ Y) (V : Y.EtaleSite) :=
  CostructuredArrow (moduleChartTarget f) V.obj

/-- The actual map of regular functions from `V` to a chart of `X ×_Y V`.
Source: Stacks, Tags 03G8 and 03M8 (blueprint: def-trf-space-etale-module-functors). -/
def moduleChartScalar (f : X ⟶ Y) (V : Y.EtaleSite) (q : ModuleChart f V) :
    Y.structureSheaf.obj.obj (op V) ⟶ X.structureSheaf.obj.obj (op q.left) :=
  (forget₂ CommRingCat RingCat).map (Scheme.Γ.map q.hom.left.left.op)

/-- A chart restriction is linear over the functions on `V`.
Source: Stacks, Tag 03M8 (blueprint: def-trf-space-etale-module-functors).
Proof: semilinearity of the module restriction, followed by functoriality of the two
pullbacks of regular functions along the commuting triangle of chart schemes. -/
theorem moduleChartMap_smul (f : X ⟶ Y) (M : X.Modules) (V : Y.EtaleSite)
    {q r : ModuleChart f V} (a : q ⟶ r)
    (b : Y.structureSheaf.obj.obj (op V)) (m : M.val.obj (op r.left)) :
    M.val.map a.left.op (moduleChartScalar f V r b • m) =
      moduleChartScalar f V q b • M.val.map a.left.op m := by
  rw [M.val.map_smul]
  have h : a.left.hom.left.left ≫ r.hom.left.left = q.hom.left.left :=
    congrArg (fun k ↦ k.left.left) (CostructuredArrow.w a)
  have hs : X.structureSheaf.obj.map a.left.op (moduleChartScalar f V r b) =
      moduleChartScalar f V q b := by
    change a.left.hom.left.left.appTop (r.hom.left.left.appTop b) =
      q.hom.left.left.appTop b
    let hb : (Scheme.Γ.obj (op V.obj.left.left)) := b
    change a.left.hom.left.left.appTop (r.hom.left.left.appTop hb) =
      q.hom.left.left.appTop hb
    exact ConcreteCategory.congr_hom
      ((Scheme.Hom.comp_appTop a.left.hom.left.left r.hom.left.left).symm.trans
        (congrArg Scheme.Hom.appTop h)) hb
  rw [hs]

/-- Restriction between chart sections, viewed as a linear map over `Γ(V,𝒪_V)`.
Source: Stacks, Tag 03M8 (blueprint: def-trf-space-etale-module-functors). -/
def moduleChartMap (f : X ⟶ Y) (M : X.Modules) (V : Y.EtaleSite)
    {q r : ModuleChart f V} (a : q ⟶ r) :
    (ModuleCat.restrictScalars (moduleChartScalar f V r).hom).obj
        (M.val.obj (op r.left)) ⟶
      (ModuleCat.restrictScalars (moduleChartScalar f V q).hom).obj
        (M.val.obj (op q.left)) :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (moduleChartScalar f V r).hom).obj
      (M.val.obj (op r.left)))
    (Y := (ModuleCat.restrictScalars (moduleChartScalar f V q).hom).obj
      (M.val.obj (op q.left)))
    { toFun := fun m ↦ M.val.map a.left.op m
      map_add' := (M.val.map a.left.op).hom.map_add
      map_smul' := moduleChartMap_smul f M V a }

/-- Identity law for the chart diagram.
Source: Stacks, Tag 03M8 (blueprint: def-trf-space-etale-module-functors).
Proof: the restriction of `M` along the identity is the identity on every section. -/
theorem moduleChartMap_id (f : X ⟶ Y) (M : X.Modules) (V : Y.EtaleSite)
    (q : ModuleChart f V) : moduleChartMap f M V (𝟙 q) = 𝟙 _ := by
  ext m
  change M.val.map (𝟙 (op q.left)) m = m
  rw [M.val.map_id]
  rfl

/-- Composition law for the chart diagram.
Source: Stacks, Tag 03M8 (blueprint: def-trf-space-etale-module-functors).
Proof: both maps are the iterated module restriction along the composite chart map. -/
theorem moduleChartMap_comp (f : X ⟶ Y) (M : X.Modules) (V : Y.EtaleSite)
    {q r t : ModuleChart f V} (a : q ⟶ r) (b : r ⟶ t) :
    moduleChartMap f M V (a ≫ b) = moduleChartMap f M V b ≫ moduleChartMap f M V a := by
  ext m
  change M.val.map (b.left.op ≫ a.left.op) m =
    M.val.map a.left.op (M.val.map b.left.op m)
  exact M.val.map_comp_apply b.left.op a.left.op m

/-- The diagram whose limit is the compatible sections on all scheme charts of `X ×_Y V`.
Source: Stacks, Tags 03H7 and 03M8 (blueprint: def-trf-space-etale-module-functors). -/
def moduleChartDiagram (f : X ⟶ Y) (M : X.Modules) (V : Y.EtaleSite) :
    (ModuleChart f V)ᵒᵖ ⥤ ModuleCat.{u} (Y.structureSheaf.obj.obj (op V)) where
  obj q := (ModuleCat.restrictScalars (moduleChartScalar f V q.unop).hom).obj
    (M.val.obj (op q.unop.left))
  map a := moduleChartMap f M V a.unop
  map_id q := moduleChartMap_id f M V q.unop
  map_comp a b := moduleChartMap_comp f M V b.unop a.unop

/-- Postcompose a chart with a map of test schemes over `Y`.
Source: Stacks, Tag 03M8 (blueprint: def-trf-space-etale-module-functors). -/
def moduleChartPost (f : X ⟶ Y) {V W : Y.EtaleSite} (a : V ⟶ W) :
    ModuleChart f V ⥤ ModuleChart f W :=
  CostructuredArrow.map a.hom

/-- A normalized direct image: its sections are limits of the actual chart module diagram;
its maps are characterized by their components on EVERY chart. The projection identities
include both restrictions in the test scheme and morphisms of modules.
Source: Stacks, Tags 03H7 and 03M8 (blueprint: def-trf-space-etale-module-functors). -/
structure ModuleDirectImageModel (f : X ⟶ Y) where
  /-- Module direct image on the small étale sites. -/
  functor : X.Modules ⥤ Y.Modules
  /-- Projection of a section to a chart of the fibre product. -/
  projection (M : X.Modules) (V : Y.EtaleSite) :
    (Functor.const (ModuleChart f V)ᵒᵖ).obj ((functor.obj M).val.obj (op V)) ⟶
      moduleChartDiagram f M V
  /-- Compatible sections are exactly the limit, with its specified projections. -/
  isLimit (M : X.Modules) (V : Y.EtaleSite) :
    IsLimit (Cone.mk ((functor.obj M).val.obj (op V)) (projection M V))
  /-- Naturality for module morphisms, on every chart section. -/
  map_projection {M N : X.Modules} (a : M ⟶ N) (V : Y.EtaleSite)
    (q : ModuleChart f V) (s : (functor.obj M).val.obj (op V)) :
    (projection N V).app (op q) ((functor.map a).val.app (op V) s) =
      a.val.app (op q.left) ((projection M V).app (op q) s)
  /-- Naturality for restrictions of the test scheme, on every chart section. -/
  restriction_projection (M : X.Modules) {V W : Y.EtaleSite} (a : V ⟶ W)
    (q : ModuleChart f V) (s : (functor.obj M).val.obj (op W)) :
    (projection M V).app (op q) ((functor.obj M).val.map a.op s) =
      (projection M W).app (op ((moduleChartPost f a).obj q)) s

/-- The compatible-chart-section universal property is realized by a module direct image.
Source: Stacks, Tags 03H7, 03G8 and 03M8
(blueprint: def-trf-space-etale-module-functors).
Proof: extend each module to étale algebraic spaces by compatible sections. On a scheme
atlas this is the descent equalizer, so the result is a sheaf and is independent of the
atlas. Pullback of regular functions supplies the scalar action on every chart. Sections
on `V` are the compatible sections on `X ×_Y V`; restrictions and module maps act on
these same families componentwise. These are limits with the displayed projections.
The atlas and its overlaps are schemes in universe `u`, so these limits have `u`-small
carriers even though the category indexing ALL charts has object universe `u+1`.
The limit property and the two projection identities determine the functor up to its
unique normalized natural isomorphism; this is a universal-property construction. -/
theorem moduleDirectImageModel_nonempty (f : X ⟶ Y) :
    Nonempty (ModuleDirectImageModel f) := by
  sorry

private theorem model_section_ext (f : X ⟶ Y) (D : ModuleDirectImageModel f)
    (M : X.Modules) (V : Y.EtaleSite) (s t : (D.functor.obj M).val.obj (op V))
    (h : ∀ q : ModuleChart f V,
      (D.projection M V).app (op q) s = (D.projection M V).app (op q) t) : s = t := by
  let R := Y.structureSheaf.obj.obj (op V)
  let l (x : (D.functor.obj M).val.obj (op V)) :
      ModuleCat.of R R ⟶ (D.functor.obj M).val.obj (op V) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x)
  have hl : l s = l t := (D.isLimit M V).hom_ext (f := l s) (f' := l t) (fun q ↦ by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (D.projection M V).app q (r • s) =
      (D.projection M V).app q (r • t)
    simpa only [map_smul] using congrArg (r • ·) (h q.unop))
  have hst := ConcreteCategory.congr_hom hl 1
  simpa [l] using hst

private def model_section_iso (f : X ⟶ Y) (D E : ModuleDirectImageModel f)
    (M : X.Modules) (V : Y.EtaleSite) :
    (D.functor.obj M).val.obj (op V) ≅ (E.functor.obj M).val.obj (op V) :=
  (D.isLimit M V).conePointUniqueUpToIso (E.isLimit M V)

private theorem model_section_iso_projection (f : X ⟶ Y)
    (D E : ModuleDirectImageModel f) (M : X.Modules) (V : Y.EtaleSite)
    (q : ModuleChart f V) (s : (D.functor.obj M).val.obj (op V)) :
    (E.projection M V).app (op q) ((model_section_iso f D E M V).hom s) =
      (D.projection M V).app (op q) s :=
  ConcreteCategory.congr_hom
    ((D.isLimit M V).conePointUniqueUpToIso_hom_comp (E.isLimit M V) (op q)) s

private def model_comparison (f : X ⟶ Y) (D E : ModuleDirectImageModel f) :
    D.functor ⟶ E.functor where
  app M := ⟨{
    app V := (model_section_iso f D E M V.unop).hom
    naturality := by
      intro V W a
      ext s
      change (model_section_iso f D E M W.unop).hom
          ((D.functor.obj M).val.map a s) =
        (E.functor.obj M).val.map a ((model_section_iso f D E M V.unop).hom s)
      apply model_section_ext f E M W.unop
      intro q
      erw [model_section_iso_projection, E.restriction_projection M a.unop,
        model_section_iso_projection, D.restriction_projection M a.unop] }⟩
  naturality := by
    intro M N a
    ext V s
    change (model_section_iso f D E N V.unop).hom
        ((D.functor.map a).val.app V s) =
      (E.functor.map a).val.app V ((model_section_iso f D E M V.unop).hom s)
    apply model_section_ext f E N V.unop
    intro q
    rw [model_section_iso_projection, E.map_projection,
      model_section_iso_projection, D.map_projection]

private theorem model_comparison_projection (f : X ⟶ Y)
    (D E : ModuleDirectImageModel f) (M : X.Modules) (V : Y.EtaleSite)
    (q : ModuleChart f V) (s : (D.functor.obj M).val.obj (op V)) :
    (E.projection M V).app (op q) (((model_comparison f D E).app M).val.app (op V) s) =
      (D.projection M V).app (op q) s :=
  model_section_iso_projection f D E M V q s

/-- The chart universal property determines direct image up to a unique normalized iso.
Source: Stacks, Tags 03H7 and 03M8 (blueprint: def-trf-space-etale-module-functors).
Proof: the universal property gives the unique section map between the two limits on
`V`. The projection identities make these maps natural in `V` and in the module. Their
composites have the projections of the identity and hence equal the identity, by limit
uniqueness. The same argument proves uniqueness of the normalized natural isomorphism. -/
theorem moduleDirectImageModel_unique (f : X ⟶ Y) (D E : ModuleDirectImageModel f) :
    ∃! e : D.functor ≅ E.functor,
      ∀ (M : X.Modules) (V : Y.EtaleSite) (q : ModuleChart f V)
        (s : (D.functor.obj M).val.obj (op V)),
        (E.projection M V).app (op q) ((e.hom.app M).val.app (op V) s) =
          (D.projection M V).app (op q) s := by
  let e : D.functor ≅ E.functor :=
    { hom := model_comparison f D E
      inv := model_comparison f E D
      hom_inv_id := by
        ext M V s
        apply model_section_ext f D M V.unop
        intro q
        change (D.projection M V.unop).app (op q)
            (((model_comparison f E D).app M).val.app V
              (((model_comparison f D E).app M).val.app V s)) =
          (D.projection M V.unop).app (op q) s
        rw [model_comparison_projection, model_comparison_projection]
      inv_hom_id := by
        ext M V s
        apply model_section_ext f E M V.unop
        intro q
        change (E.projection M V.unop).app (op q)
            (((model_comparison f D E).app M).val.app V
              (((model_comparison f E D).app M).val.app V s)) =
          (E.projection M V.unop).app (op q) s
        rw [model_comparison_projection, model_comparison_projection] }
  refine ⟨e, ?_, ?_⟩
  · exact model_comparison_projection f D E
  · intro e' he'
    apply Iso.ext
    ext M V s
    apply model_section_ext f E M V.unop
    intro q
    exact (he' M V.unop q s).trans (model_comparison_projection f D E M V.unop q s).symm

/-- The normalized direct-image model, selected by its complete limit universal property.
Source: Stacks, Tags 03H7 and 03M8 (blueprint: def-trf-space-etale-module-functors). -/
def moduleDirectImageModel (f : X ⟶ Y) : ModuleDirectImageModel f :=
  Classical.choice (moduleDirectImageModel_nonempty f)

/-- Canonical module direct image, retaining the compatible-section model above.
Source: Stacks, Tag 03G8 (blueprint: def-trf-space-etale-module-functors). -/
def moduleDirectImage (f : X ⟶ Y) : X.Modules ⥤ Y.Modules :=
  (moduleDirectImageModel f).functor

/-- Tensor pullback exists as the left adjoint of the specified module direct image.
Source: Stacks, Tag 03D7 and Tag 03G8 (blueprint: def-trf-space-etale-module-functors).
Proof: on the enlarged étale ringed sites form the usual inverse image and extension of
scalars, and transport it through the scheme-chart equivalences. The tensor universal
property identifies its maps to `F` with maps to the compatible-section direct image.
This supplies the adjunction to the direct image already fixed above; uniqueness of a
left adjoint identifies any two such tensor constructions compatibly with their units. -/
theorem moduleDirectImage_isRightAdjoint (f : X ⟶ Y) :
    (moduleDirectImage f).IsRightAdjoint := by
  sorry

attribute [instance] moduleDirectImage_isRightAdjoint

/-- The tensor pullback, specified by its adjunction to the canonical direct image.
Source: Stacks, Tags 03D7 and 03G8 (blueprint: def-trf-space-etale-module-functors). -/
def moduleTensorPullback (f : X ⟶ Y) : Y.Modules ⥤ X.Modules :=
  (moduleDirectImage f).leftAdjoint

/-- The unit and counit fixing the normalization of tensor pullback.
Source: Stacks, Tag 03D7 (blueprint: def-trf-space-etale-module-functors). -/
def moduleTensorAdjunction (f : X ⟶ Y) : moduleTensorPullback f ⊣ moduleDirectImage f :=
  Adjunction.ofIsRightAdjoint (moduleDirectImage f)

/-- The local tensor `b ⊗ m`, for `m` represented on `V` and a chart over `V`.
The unit sends `m` to `1 ⊗ m`; projection to the chart and multiplication by `b` give
`b ⊗ m`. This uses the chosen adjunction, not a freely chosen map into the pullback.
Source: Stacks, Tags 03D7, 03LV (blueprint: def-trf-space-etale-module-functors). -/
def moduleTensorSection (f : X ⟶ Y) (M : Y.Modules) (V : Y.EtaleSite)
    (q : ModuleChart f V) (b : X.structureSheaf.obj.obj (op q.left))
    (m : M.val.obj (op V)) : ((moduleTensorPullback f).obj M).val.obj (op q.left) :=
  b • @id (((moduleTensorPullback f).obj M).val.obj (op q.left))
    (((moduleDirectImageModel f).projection ((moduleTensorPullback f).obj M) V).app
      (op q) (((moduleTensorAdjunction f).unit.app M).val.app (op V) m))

end AlgebraicGeometry.AlgebraicSpace
