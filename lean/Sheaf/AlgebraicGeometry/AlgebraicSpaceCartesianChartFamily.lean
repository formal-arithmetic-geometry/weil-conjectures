/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule

/-!
# Cartesian module families on all étale charts

Source: Stacks Project, Properties of Spaces, Tags 03LY and 03LZ
(blueprint: def-sfb-space-cartesian-chart-family).

The chart site is the localized site `X_et/V`, as specified by the algebraic-space
interface. The identity and composition constraints are sectionwise equalities after the
canonical reindexings `Over.mapId` and `Over.mapComp`, with no arbitrary comparison map.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Iterated localization has additive sheafification by the canonical equivalence
`(X_et/V)/W ≌ X_et/W.left` and the already supplied chart sheafification.
Source: Stacks Project, Sites, localization; Modules on Sites, Tag 03DL
(blueprint: def-sfb-space-cartesian-chart-family). -/
noncomputable instance chartIteratedWeakSheafify (X : AlgebraicSpace S)
    (V : X.EtaleSite) (W : Over V) :
    HasWeakSheafify ((X.etaleTopology.over V).over W) AddCommGrpCat.{u} := by
  let : (W.iteratedSliceEquiv.inverse.sheafPushforwardContinuous AddCommGrpCat.{u}
      (X.etaleTopology.over W.left) ((X.etaleTopology.over V).over W)).IsEquivalence :=
    inferInstanceAs ((W.iteratedSliceEquiv.sheafCongr
      ((X.etaleTopology.over V).over W) (X.etaleTopology.over W.left)
      AddCommGrpCat.{u}).functor.IsEquivalence)
  exact Functor.IsDenseSubsite.hasWeakSheafify_of_isEquivalence
    (X.etaleTopology.over W.left) ((X.etaleTopology.over V).over W)
    W.iteratedSliceEquiv.inverse AddCommGrpCat.{u}

/-- Local bijectivity transports across the same canonical iterated-slice equivalence.
Source: Stacks Project, Sites, localization; Modules on Sites, Tag 03DL
(blueprint: def-sfb-space-cartesian-chart-family). -/
noncomputable instance chartIteratedWEqualsLocallyBijective (X : AlgebraicSpace S)
    (V : X.EtaleSite) (W : Over V) :
    ((X.etaleTopology.over V).over W).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  let : (W.iteratedSliceEquiv.inverse.sheafPushforwardContinuous AddCommGrpCat.{u}
      (X.etaleTopology.over W.left) ((X.etaleTopology.over V).over W)).IsEquivalence :=
    inferInstanceAs ((W.iteratedSliceEquiv.sheafCongr
      ((X.etaleTopology.over V).over W) (X.etaleTopology.over W.left)
      AddCommGrpCat.{u}).functor.IsEquivalence)
  exact GrothendieckTopology.WEqualsLocallyBijective.transport
    ((X.etaleTopology.over V).over W) (X.etaleTopology.over W.left)
    W.iteratedSliceEquiv.inverse
    (Functor.IsDenseSubsite.coverPreserving _ _ _)

/-- A module on every localized chart, with invertible transitions and the normalized
identity and composition laws, expressed on sections after the canonical
reindexings `Over.mapId` and `Over.mapComp`.
Source: Stacks Project, Properties of Spaces, Tag 03LY
(blueprint: def-sfb-space-cartesian-chart-family). -/
structure CartesianModuleChartFamily (X : AlgebraicSpace S) where
  /-- The module on the localized étale site of a chart. -/
  obj (V : X.EtaleSite) : SheafOfModules.{u} (X.structureSheaf.over V)
  /-- The transition is the specified localized étale pullback isomorphism. -/
  transition {W V : X.EtaleSite} (f : W ⟶ V) :
    (X.etalePullbackMap f).obj (obj V) ≅ obj W
  /-- Identity normalization, under the canonical identity reindexing. -/
  identity (V : X.EtaleSite) (A : Over V)
      (s : ((X.etalePullbackMap (𝟙 V)).obj (obj V)).val.obj (op A)) :
    (transition (𝟙 V)).hom.val.app (op A) s =
      (obj V).val.map ((Over.mapId V).inv.app A).op s
  /-- Composition normalization, under the canonical composition reindexing. -/
  composition {T W V : X.EtaleSite} (g : T ⟶ W) (f : W ⟶ V) (A : Over T)
      (s : ((X.etalePullbackMap (g ≫ f)).obj (obj V)).val.obj (op A)) :
    (transition (g ≫ f)).hom.val.app (op A) s =
      (transition g).hom.val.app (op A)
        ((transition f).hom.val.app (op ((Over.map g).obj A))
          ((obj V).val.map ((Over.mapComp g f).inv.app A).op s))

namespace CartesianModuleChartFamily

variable {X : AlgebraicSpace S}

/-- Compatible families of linear module maps.
Source: Stacks Project, Properties of Spaces, Tag 03LY, categorical formulation
(blueprint: def-sfb-space-cartesian-chart-family). -/
@[ext] structure Hom (F G : CartesianModuleChartFamily X) where
  /-- A module map on every chart. -/
  app (V : X.EtaleSite) : F.obj V ⟶ G.obj V
  /-- The maps commute with each specified transition. -/
  comm {W V : X.EtaleSite} (f : W ⟶ V) :
    (F.transition f).hom ≫ app W =
      (X.etalePullbackMap f).map (app V) ≫ (G.transition f).hom

/-- Composition and identities are chartwise.
Source: Stacks Project, Properties of Spaces, Tag 03LY, categorical formulation
(blueprint: def-sfb-space-cartesian-chart-family). -/
instance : Category (CartesianModuleChartFamily X) where
  Hom := Hom
  id F := ⟨fun V ↦ 𝟙 (F.obj V), by intros; simp⟩
  comp a b := ⟨fun V ↦ a.app V ≫ b.app V, by
    intro W V f
    rw [← Category.assoc, a.comm, Category.assoc, b.comm]
    simp only [Functor.map_comp, Category.assoc]⟩

/-- Evaluation remembers the actual chart module and the actual component map.
Source: Stacks Project, Properties of Spaces, Tag 03LY
(blueprint: def-sfb-space-cartesian-chart-family). -/
def evaluation (V : X.EtaleSite) :
    CartesianModuleChartFamily X ⥤ SheafOfModules.{u} (X.structureSheaf.over V) where
  obj F := F.obj V
  map h := h.app V

end CartesianModuleChartFamily

/-- The full subcategory whose module on every chart is quasi-coherent, with the
existing local-presentation predicate, including arbitrary small presentations.
Source: Stacks Project, Properties of Spaces, Tag 03LZ; Modules on Sites, Tag 03DL
(blueprint: def-sfb-space-cartesian-chart-family). -/
abbrev CartesianQCohChartFamily (X : AlgebraicSpace S) :=
  ObjectProperty.FullSubcategory
    (fun F : CartesianModuleChartFamily X ↦ ∀ V : X.EtaleSite, (F.obj V).IsQuasicoherent)

end AlgebraicGeometry.AlgebraicSpace
