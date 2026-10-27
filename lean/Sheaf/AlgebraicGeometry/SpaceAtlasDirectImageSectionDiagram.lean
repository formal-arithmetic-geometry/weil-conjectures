/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
import Sheaf.AlgebraicGeometry.SpaceChartTensorRealization
public import Sheaf.AlgebraicGeometry.SchemeEtaleCotangentRingMap
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.EnlargedRingedCompositionLocalization

/-! # The atlas direct-image section diagram

Source: Stacks Project, Morphisms of Algebraic Spaces, Tag 03M8, the section
identifications and restriction arrows in the proof
(blueprint: lem-trf-space-atlas-direct-image-section-diagram).

The atlas need not cover. The comparison data retain every chart projection, the
actual tensor pullbacks and their units, and the regular-function scalar maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y A B : AlgebraicSpace S}

/-- `A ×_Y V`, viewed as an enlarged object over `X` through the étale map `g`.
Source: Stacks, Tag 03M8
(blueprint: lem-trf-space-atlas-direct-image-section-diagram). -/
def atlasSectionObject (f : X ⟶ Y) (g : A ⟶ X) (hg : IsChartwiseEtale g)
    (V : Y.EtaleSite) : X.EnlargedEtaleSite :=
  (enlargedPostcompose g hg).obj
    ((enlargedBaseChange (g ≫ f)).obj ((enlargedSchemeInclusion Y).obj V))

/-- The projection `A ×_Y V → X ×_Y V`, retaining both fibre-product coordinates.
Source: Stacks, Tag 03M8
(blueprint: lem-trf-space-atlas-direct-image-section-diagram). -/
def atlasSectionToBase (f : X ⟶ Y) (g : A ⟶ X) (hg : IsChartwiseEtale g)
    (V : Y.EtaleSite) : atlasSectionObject f g hg V ⟶
      (enlargedBaseChange f).obj ((enlargedSchemeInclusion Y).obj V) :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk
    (Limits.pullback.map (g ≫ f).hom
      ((enlargedSchemeInclusion Y).obj V).obj.hom.hom f.hom
      ((enlargedSchemeInclusion Y).obj V).obj.hom.hom g.hom (𝟙 _) (𝟙 _)
      (by simp) (by simp)))
    (by
      apply ObjectProperty.hom_ext
      simp [atlasSectionObject, enlargedPostcompose, enlargedBaseChange,
        enlargedFibreProductFst]))

/-- The arrow on fibre products induced by a map over `X`.
Source: Stacks, Tag 03M8, the two relation projections
(blueprint: lem-trf-space-atlas-direct-image-section-diagram). -/
def atlasSectionArrow (f : X ⟶ Y) (g : A ⟶ X) (h : B ⟶ X)
    (hg : IsChartwiseEtale g) (hh : IsChartwiseEtale h)
    (k : A ⟶ B) (w : k ≫ h = g) (V : Y.EtaleSite) :
    atlasSectionObject f g hg V ⟶ atlasSectionObject f h hh V :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk
    (Limits.pullback.map (g ≫ f).hom
      ((enlargedSchemeInclusion Y).obj V).obj.hom.hom (h ≫ f).hom
      ((enlargedSchemeInclusion Y).obj V).obj.hom.hom k.hom (𝟙 _) (𝟙 _)
      (by simpa using congrArg (fun l ↦ (l ≫ f).hom) w.symm) (by simp)))
    (by
      apply ObjectProperty.hom_ext
      have wh : k.hom ≫ h.hom = g.hom := congrArg (fun l ↦ l.hom) w
      change Limits.pullback.lift _ _ _ ≫
        (Limits.pullback.fst _ _ ≫ h.hom) =
          Limits.pullback.fst (g ≫ f).hom
            ((enlargedSchemeInclusion Y).obj V).obj.hom.hom ≫ g.hom
      rw [← Category.assoc, Limits.pullback.lift_fst, Category.assoc, wh]))

/-- Base change of a map of test schemes, with the same map to `X`.
Source: Stacks, Tag 03M8, functoriality in `V`
(blueprint: lem-trf-space-atlas-direct-image-section-diagram). -/
def atlasSectionTestMap (f : X ⟶ Y) (g : A ⟶ X) (hg : IsChartwiseEtale g)
    {V V' : Y.EtaleSite} (c : V ⟶ V') :
    atlasSectionObject f g hg V ⟶ atlasSectionObject f g hg V' :=
  (enlargedPostcompose g hg).map
    ((enlargedBaseChange (g ≫ f)).map ((enlargedSchemeInclusion Y).map c))

/-- A chart of `A ×_Y V` is the same chart scheme viewed over `X`.
Source: Stacks, Tag 03M8
(blueprint: lem-trf-space-atlas-direct-image-section-diagram). -/
def atlasSectionChartLift (f : X ⟶ Y) (g : A ⟶ X) (hg : IsChartwiseEtale g)
    (V : Y.EtaleSite) (q : ModuleChart (g ≫ f) V) :
    (enlargedSchemeInclusion X).obj ((chartwiseEtaleMap g hg).obj q.left) ⟶
      atlasSectionObject f g hg V :=
  (enlargedPostcompose g hg).map (enlargedChartLift (g ≫ f) q.left V q.hom.left q.hom.w)

/-- Scalars on enlarged sections are pulled back from `V` through `X ×_Y V`.
Source: Stacks, Tags 03G8 and 03M8
(blueprint: lem-trf-space-atlas-direct-image-section-diagram). -/
def atlasSectionScalar (f : X ⟶ Y) (g : A ⟶ X) (hg : IsChartwiseEtale g)
    (V : Y.EtaleSite) : Y.structureSheaf.obj.obj (op V) ⟶
      X.enlargedStructureSheaf.obj.obj (op (atlasSectionObject f g hg V)) :=
  (enlargedStructureRestriction Y).inv.hom.app (op V) ≫
    (enlargedStructuralMap f).hom.app (op ((enlargedSchemeInclusion Y).obj V)) ≫
    X.enlargedStructureSheaf.obj.map (atlasSectionToBase f g hg V).op

/-- The actual extension section module with the indicated `O_Y(V)` action.
Source: Stacks, Tag 03M8
(blueprint: lem-trf-space-atlas-direct-image-section-diagram). -/
def atlasSectionModule (f : X ⟶ Y) (g : A ⟶ X) (hg : IsChartwiseEtale g)
    (F : X.Modules) (V : Y.EtaleSite) : ModuleCat (Y.structureSheaf.obj.obj (op V)) :=
  (ModuleCat.restrictScalars (atlasSectionScalar f g hg V).hom).obj
    (((smallEnlargedModuleEquivalence.{u, u} X).inverse.obj F).val.obj
      (op (atlasSectionObject f g hg V)))

/-- Restrict an enlarged section to a chart and apply the extension counit.
Source: Stacks, Tags 03H7 and 03M8
(blueprint: lem-trf-space-atlas-direct-image-section-diagram). -/
def atlasSectionProjection (f : X ⟶ Y) (g : A ⟶ X) (hg : IsChartwiseEtale g)
    (F : X.Modules) (V : Y.EtaleSite) (q : ModuleChart (g ≫ f) V)
    (s : atlasSectionModule f g hg F V) :
    F.val.obj (op ((chartwiseEtaleMap g hg).obj q.left)) :=
  (((smallEnlargedModuleEquivalence.{u, u} X).counitIso.hom.app F).val.app
    (op ((chartwiseEtaleMap g hg).obj q.left)))
    (((smallEnlargedModuleEquivalence.{u, u} X).inverse.obj F).val.map
      (atlasSectionChartLift f g hg V q).op s)

/-- A comparison retaining the restriction identification, all chart projections,
regular-function scalar maps, and naturality in both arguments. `L` is the actual
single or iterated tensor pullback; its normalization is imposed in the theorem below.
Source: Stacks, Tag 03M8
(blueprint: lem-trf-space-atlas-direct-image-section-diagram). -/
structure AtlasSectionComparison (f : X ⟶ Y) (g : A ⟶ X)
    (hg : IsChartwiseEtale g) (L : X.Modules ⥤ A.Modules) where
  restriction : L ≅ (SheafOfModules.pushforward (F := chartwiseEtaleMap g hg) ⟨𝟙 _⟩)
  sections (F : X.Modules) (V : Y.EtaleSite) :
    ((moduleDirectImage (g ≫ f)).obj (L.obj F)).val.obj (op V) ≃ₗ[
      Y.structureSheaf.obj.obj (op V)] atlasSectionModule f g hg F V
  projection (F : X.Modules) (V : Y.EtaleSite) (q : ModuleChart (g ≫ f) V)
      (s : ((moduleDirectImage (g ≫ f)).obj (L.obj F)).val.obj (op V)) :
    (restriction.hom.app F).val.app (op q.left)
        (((moduleDirectImageModel (g ≫ f)).projection (L.obj F) V).app (op q) s) =
      atlasSectionProjection f g hg F V q (sections F V s)
  coefficient (V : Y.EtaleSite) (q : ModuleChart (g ≫ f) V) :
    atlasSectionScalar f g hg V ≫
        X.enlargedStructureSheaf.obj.map (atlasSectionChartLift f g hg V q).op ≫
        (enlargedStructureRestriction X).hom.hom.app
          (op ((chartwiseEtaleMap g hg).obj q.left)) = moduleChartScalar (g ≫ f) V q
  moduleMap (F G : X.Modules) (b : F ⟶ G) (V : Y.EtaleSite)
      (s : ((moduleDirectImage (g ≫ f)).obj (L.obj F)).val.obj (op V)) :
    sections G V (((moduleDirectImage (g ≫ f)).map (L.map b)).val.app (op V) s) =
      (((smallEnlargedModuleEquivalence.{u, u} X).inverse.map b).val.app
        (op (atlasSectionObject f g hg V))) (sections F V s)
  testMap (F : X.Modules) (V V' : Y.EtaleSite) (c : V ⟶ V')
      (s : ((moduleDirectImage (g ≫ f)).obj (L.obj F)).val.obj (op V')) :
    sections F V (((moduleDirectImage (g ≫ f)).obj (L.obj F)).val.map c.op s) =
      (((smallEnlargedModuleEquivalence.{u, u} X).inverse.obj F).val.map
        (atlasSectionTestMap f g hg c).op) (sections F V' s)

/-- Normalization on nested chart-unit tensors: multiply the two coefficients and
restrict the original section. The heterogeneous equality only compares the identical
chart scheme along the two equal composites to `X`.
Source: Stacks, Tags 03D8, 03LV and 03LW
(blueprint: lem-trf-space-atlas-direct-image-section-diagram). -/
def AtlasNestedTensorFormula (p : A ⟶ X) (hp : IsChartwiseEtale p)
    (k : B ⟶ A) (hk : IsChartwiseEtale k) (L : X.Modules ⥤ B.Modules)
    (e : moduleTensorPullback p ⋙ moduleTensorPullback k ≅ L)
    (g : B ⟶ X) (hg : IsChartwiseEtale g)
    (σ : L ≅ (SheafOfModules.pushforward (F := chartwiseEtaleMap g hg) ⟨𝟙 _⟩)) : Prop :=
  ∀ (F : X.Modules) (V : X.EtaleSite) (q : ModuleChart p V)
    (r : ModuleChart k q.left) (a : B.structureSheaf.obj.obj (op r.left))
    (b : A.structureSheaf.obj.obj (op q.left)) (m : F.val.obj (op V)),
    HEq ((σ.hom.app F).val.app (op r.left)
      ((e.hom.app F).val.app (op r.left)
        (moduleTensorSection k ((moduleTensorPullback p).obj F) q.left r a
          (moduleTensorSection p F V q b m))))
      ((a * moduleChartScalar k q.left r b) •
        F.val.map ((chartwiseEtaleMap p hp).map
          (ObjectProperty.homMk r.hom :
            (chartwiseEtaleMap k hk).obj r.left ⟶ q.left) ≫
            (ObjectProperty.homMk q.hom : (chartwiseEtaleMap p hp).obj q.left ⟶ V)).op m)

/-- Canonical section identifications and all three restriction arrows, without a
surjectivity or affineness assumption on the scheme map `p`.
Source: Stacks, Tag 03M8, section-evaluation part of the proof
(blueprint: lem-trf-space-atlas-direct-image-section-diagram).

Proof, following the six steps of the node:
1. Represent `U ×_X U` by a scheme using fibre-products-etale-covers. Chartwise
   étale permanence makes its projections, and the composite to `X`, étale. Base
   change of `V` gives the enlarged objects `W`, `Z`, and `Q`; no covering is used.
2. Chart-adjunction-tensor-realization identifies the specified tensor pullbacks
   with restriction by `a tensor m ↦ a m`, inverse `m ↦ 1 tensor m`. Its nested
   tensor formula gives the two normalized identifications on `R`, with no extra
   automorphism. These are the restriction and nested-tensor equations below.
3. Chart-limit-enlarged-sections supplies the three linear section comparisons,
   each characterized by restriction on every specified chart projection. The
   extension counit makes their chart targets literally the original `F(T)`.
4. Apply `f_*` to the specified unit for `p`, then use the projection-preserving
   composition comparison of enlarged-ringed-composition-localization. The tensor
   unit becomes restriction to `Z → W`. The fibre-product comparison preserves
   its coordinates, so projecting to every scheme chart gives the first equation.
5. Repeat with each relation projection. The normalized comparison between the
   two iterated tensor pullbacks gives the common `F_R`. On enlarged sections the
   two arrows are restrictions along the two displayed coordinate maps `Q → Z`.
6. Functoriality of restrictions gives naturality in `V`, and module maps commute
   with restrictions. The natural-transformation types retain naturality in `F`.
   Pullback of functions along the common map to `V` proves linearity of every
   arrow. The coefficient and projection fields retain this on every chart,
   including when the all-chart category exceeds the module universe. -/
theorem space_atlas_direct_image_section_diagram (f : X ⟶ Y)
    (U : Over S) (p : schemeSpace U ⟶ X) (hp : IsChartwiseEtale p) :
    ∃ (R : Over S) (p₁ p₂ : schemeSpace R ⟶ schemeSpace U)
      (h₁ : IsChartwiseEtale p₁) (h₂ : IsChartwiseEtale p₂),
      IsPullback p₁.hom p₂.hom p.hom p.hom ∧
      ∃ (w : p₂ ≫ p = p₁ ≫ p) (hr : IsChartwiseEtale (p₁ ≫ p))
        (α : moduleDirectImage f ≅
          (smallEnlargedModuleEquivalence.{u, u} X).inverse ⋙
            SheafOfModules.pushforward (enlargedStructuralMap f) ⋙
              smallEnlargedModuleRestriction Y)
        (CU : AtlasSectionComparison f p hp (moduleTensorPullback p))
        (CR : AtlasSectionComparison f (p₁ ≫ p) hr
          (moduleTensorPullback p ⋙ moduleTensorPullback p₁))
        (c : moduleTensorPullback p ⋙ moduleTensorPullback p₂ ≅
          moduleTensorPullback p ⋙ moduleTensorPullback p₁)
        (ι : moduleDirectImage f ⟶ moduleTensorPullback p ⋙ moduleDirectImage (p ≫ f))
        (r₁ r₂ : moduleTensorPullback p ⋙ moduleDirectImage (p ≫ f) ⟶
          (moduleTensorPullback p ⋙ moduleTensorPullback p₁) ⋙
            moduleDirectImage ((p₁ ≫ p) ≫ f)),
        (∀ (F : X.Modules) (V : Y.EtaleSite) (q : ModuleChart f V) s,
          (((smallEnlargedModuleEquivalence.{u, u} X).counitIso.hom.app F).val.app
            (op q.left))
              (((smallEnlargedModuleEquivalence.{u, u} X).inverse.obj F).val.map
                (enlargedChartLift f q.left V q.hom.left q.hom.w).op
                ((α.hom.app F).val.app (op V) s)) =
            ((moduleDirectImageModel f).projection F V).app (op q) s) ∧
        (∀ (F : X.Modules) (V : X.EtaleSite) (q : ModuleChart p V)
          (a : (schemeSpace U).structureSheaf.obj.obj (op q.left))
          (m : F.val.obj (op V)),
          (CU.restriction.hom.app F).val.app (op q.left)
              (moduleTensorSection p F V q a m) =
            a • F.val.map
              (ObjectProperty.homMk q.hom : (chartwiseEtaleMap p hp).obj q.left ⟶ V).op m) ∧
        AtlasNestedTensorFormula p hp p₁ h₁
          (moduleTensorPullback p ⋙ moduleTensorPullback p₁) (Iso.refl _)
          (p₁ ≫ p) hr CR.restriction ∧
        AtlasNestedTensorFormula p hp p₂ h₂
          (moduleTensorPullback p ⋙ moduleTensorPullback p₁) c
          (p₁ ≫ p) hr CR.restriction ∧
        (∀ (F : X.Modules) (V : Y.EtaleSite) s,
          CU.sections F V ((ι.app F).val.app (op V) s) =
            (((smallEnlargedModuleEquivalence.{u, u} X).inverse.obj F).val.map
              (atlasSectionToBase f p hp V).op)
              ((α.hom.app F).val.app (op V) s)) ∧
        (∀ (F : X.Modules) (V : Y.EtaleSite) s,
          CR.sections F V ((r₁.app F).val.app (op V) s) =
            (((smallEnlargedModuleEquivalence.{u, u} X).inverse.obj F).val.map
              (atlasSectionArrow f (p₁ ≫ p) p hr hp p₁ rfl V).op)
              (CU.sections F V s)) ∧
        (∀ (F : X.Modules) (V : Y.EtaleSite) s,
          CR.sections F V ((r₂.app F).val.app (op V) s) =
            (((smallEnlargedModuleEquivalence.{u, u} X).inverse.obj F).val.map
              (atlasSectionArrow f (p₁ ≫ p) p hr hp p₂ w V).op)
              (CU.sections F V s)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
