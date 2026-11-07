/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.FreeModuleSheafConstruction
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.LinearAlgebra.FreeModule.Basic

import WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-!
# Conditional calculus of normalized free-module comparisons

Source: Stacks Project, Modules on Sites, Tag 08TQ (lemma-pullback-differentials),
free-module identifications, and Tag 04BL (lemma-universal-module), generator extensions
(auxiliary; not a blueprint node).

The free sheaves, generators, and simultaneous coefficient/generator changes are the
existing `SheafFreeModule.free`, `generator`, and `change`. No adjunction is assumed for
the set-sheaf functors. Equalities of semilinear maps are expressed on their underlying
sheaves; this forgetful description is faithful. The explicit `ULift` identifications
are those of the recorded algebraic inverse-image interface.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w wI uC vC uD vD uH vH

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.SheafFreeModule

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

-- Cache the existing sheaf-composition witnesses once for each site.
local instance : J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance
local instance : J.HasSheafCompose (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance
local instance : J.HasSheafCompose (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance
local instance : K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance
local instance : K.HasSheafCompose (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance
local instance : K.HasSheafCompose (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance


attribute [-instance] hasSheafCompose_of_preservesMulticospan in
private abbrev coefficientSets (B : Sheaf J CommRingCat.{w}) :=
  (sheafCompose J (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).obj B

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
private def addSections {B : Sheaf J CommRingCat.{w}}
    (M : SheafOfModules.{w} (ring B)) :
    (moduleSets B).obj M ⊗ (moduleSets B).obj M ⟶ (moduleSets B).obj M :=
  ⟨{ app := fun U ↦ ↾(fun z ↦ ULift.up (z.1.down + z.2.down))
     naturality := by
       intro U V f
       ext z
       apply ULift.ext
       exact ((M.val.map f).hom.map_add _ _).symm }⟩

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
private def smulSections {B : Sheaf J CommRingCat.{w}}
    (M : SheafOfModules.{w} (ring B)) :
    coefficientSets B ⊗ (moduleSets B).obj M ⟶ (moduleSets B).obj M :=
  ⟨{ app := fun U ↦ ↾(fun z ↦ ULift.up
        ((@id (B.obj.obj U) z.1.down) • (@id (M.val.obj U) z.2.down)))
     naturality := by
       intro U V f
       ext z
       apply ULift.ext
       exact (M.val.map_smul f z.1.down z.2.down).symm }⟩

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
omit [EssentiallySmall.{w} C] [EssentiallySmall.{w} D] in
private theorem pair_sections (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    [PreservesFiniteLimits L] (X Y : Sheaf J (Type w)) (V : Dᵒᵖ)
    (x : (L.obj X).obj.obj V) (y : (L.obj Y).obj.obj V) :
    ∃ z : (L.obj (X ⊗ Y)).obj.obj V,
      (L.map (CartesianMonoidalCategory.fst X Y)).hom.app V z = x ∧
      (L.map (CartesianMonoidalCategory.snd X Y)).hom.app V z = y := by
  refine ⟨(inv (CartesianMonoidalCategory.prodComparison L X Y)).hom.app V (x, y),
    ?_, ?_⟩
  · exact congrArg (fun f ↦ f.hom.app V (x, y))
      (CartesianMonoidalCategory.inv_prodComparison_map_fst L X Y)
  · exact congrArg (fun f ↦ f.hom.app V (x, y))
      (CartesianMonoidalCategory.inv_prodComparison_map_snd L X Y)


attribute [-instance] hasSheafCompose_of_preservesMulticospan in
private def linearMapOfSets {B : Sheaf J CommRingCat.{w}}
    {M N : SheafOfModules.{w} (ring B)}
    (f : (moduleSets B).obj M ⟶ (moduleSets B).obj N)
    (ha : ∀ U (x y : M.val.obj U),
      (f.hom.app U (ULift.up (x + y))).down =
        (f.hom.app U (ULift.up x)).down + (f.hom.app U (ULift.up y)).down)
    (hs : ∀ U (a : B.obj.obj U) (x : M.val.obj U),
      (f.hom.app U (ULift.up (a • x))).down =
        a • (@id (N.val.obj U) (f.hom.app U (ULift.up x)).down)) : M ⟶ N where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := fun x ↦ (f.hom.app U (ULift.up x)).down
          map_add' := ha U
          map_smul' := hs U }
      naturality := by
        intro U V g
        ext x
        exact congrArg ULift.down (congrArg (fun k ↦ k (ULift.up x))
          (f.hom.naturality g)) }


attribute [-instance] hasSheafCompose_of_preservesMulticospan in
/-- Underlying comparison for an arbitrary algebraic transport, with the canonical
underlying-module identification retained. Source: Stacks 08TQ, free identifications
(auxiliary; not a blueprint node). -/
def normalizedFreeComparison
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B BI)
    (E : Sheaf J (Type w))
    (p : F.modules.obj ((free B).obj E) ≅ (free BI).obj (L.obj E)) :
    L.obj ((moduleSets B).obj ((free B).obj E)) ⟶
      (moduleSets BI).obj ((free BI).obj (L.obj E)) :=
  F.moduleUnderlying.inv.app ((free B).obj E) ≫ (moduleSets BI).map p.hom

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
/-- The stated representing hypothesis is precisely bijectivity of restriction along
L of the canonical generator, for every target module sheaf. Source: Stacks 04BL and
08TQ, conditional free identification
(auxiliary; not a blueprint node). -/
def HasTransportedFreeUniversalProperty
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B BI)
    (E : Sheaf J (Type w)) : Prop :=
  ∀ M : SheafOfModules.{w} (ring BI),
    Function.Bijective (fun h : F.modules.obj ((free B).obj E) ⟶ M ↦
      L.map (generator B E) ≫ F.moduleUnderlying.inv.app ((free B).obj E) ≫
        (moduleSets BI).map h)

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
/-- The source and target underlying identifications applied to L of a coefficient and
 generator change. Source: Stacks 04BL and 08TQ, semilinear generator extension
(auxiliary; not a blueprint node). -/
def transportedFreeChange
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    {B B' : Sheaf J CommRingCat.{w}} {BI BI' : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B BI)
    (F' : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B' BI')
    (b : B ⟶ B') {E E' : Sheaf J (Type w)} (u : E ⟶ E') :
    (moduleSets BI).obj (F.modules.obj ((free B).obj E)) ⟶
      (moduleSets BI').obj (F'.modules.obj ((free B').obj E')) :=
  F.moduleUnderlying.hom.app ((free B).obj E) ≫ L.map (changeSets b u) ≫
    F'.moduleUnderlying.inv.app ((free B').obj E')

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
/-- Sectionwise form of the transported change, descending the interface's `ULift`.
Source: Stacks 04BL and 08TQ, semilinear generator extension
(auxiliary; not a blueprint node). -/
def transportedFreeChangeSection
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    {B B' : Sheaf J CommRingCat.{w}} {BI BI' : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B BI)
    (F' : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B' BI')
    (b : B ⟶ B') {E E' : Sheaf J (Type w)} (u : E ⟶ E')
    (V : Dᵒᵖ) (x : (F.modules.obj ((free B).obj E)).val.obj V) :
    (F'.modules.obj ((free B').obj E')).val.obj V :=
  ((transportedFreeChange L F F' b u).hom.app V (ULift.up x)).down


variable {H : Type uH} [Category.{vH} H] [EssentiallySmall.{w} H]
  {T : GrothendieckTopology H}

local instance : T.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance
local instance : T.HasSheafCompose (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance
local instance : T.HasSheafCompose (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
private def compositePresentation
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (N : Sheaf K (Type w) ⥤ Sheaf T (Type w))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    {BII : Sheaf T CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B BI)
    (G : SheafOfModules.AlgebraicInverseImageOfUniverses.{uD, vD, uH, vH, w, w} N BI BII) :
    SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uH, vH, w, w} (L ⋙ N) B BII where
  ringUnderlying := N.mapIso F.ringUnderlying ≪≫ G.ringUnderlying
  ringAdd := by
    intro S a b t h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.ringAdd (L.obj S) (L.map a ≫ F.ringUnderlying.hom)
      (L.map b ≫ F.ringUnderlying.hom) (L.map t ≫ F.ringUnderlying.hom)
      (F.ringAdd S a b t h) V x
  ringMul := by
    intro S a b t h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.ringMul (L.obj S) (L.map a ≫ F.ringUnderlying.hom)
      (L.map b ≫ F.ringUnderlying.hom) (L.map t ≫ F.ringUnderlying.hom)
      (F.ringMul S a b t h) V x
  ringZero := by
    intro S a h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.ringZero (L.obj S) (L.map a ≫ F.ringUnderlying.hom)
      (F.ringZero S a h) V x
  ringOne := by
    intro S a h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.ringOne (L.obj S) (L.map a ≫ F.ringUnderlying.hom)
      (F.ringOne S a h) V x
  modules := F.modules ⋙ G.modules
  moduleUnderlying := Functor.isoWhiskerLeft F.modules G.moduleUnderlying ≪≫
    Functor.isoWhiskerRight F.moduleUnderlying N
  moduleAdd := by
    intro M S a b t h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.moduleAdd (F.modules.obj M) (L.obj S)
      (L.map a ≫ F.moduleUnderlying.inv.app M)
      (L.map b ≫ F.moduleUnderlying.inv.app M)
      (L.map t ≫ F.moduleUnderlying.inv.app M) (F.moduleAdd M S a b t h) V x
  moduleZero := by
    intro M S a h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.moduleZero (F.modules.obj M) (L.obj S)
      (L.map a ≫ F.moduleUnderlying.inv.app M) (F.moduleZero M S a h) V x
  moduleSMul := by
    intro M S a b t h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.moduleSMul (F.modules.obj M) (L.obj S)
      (L.map a ≫ F.ringUnderlying.hom)
      (L.map b ≫ F.moduleUnderlying.inv.app M)
      (L.map t ≫ F.moduleUnderlying.inv.app M) (F.moduleSMul M S a b t h) V x


end CategoryTheory.SheafFreeModule
