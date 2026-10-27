/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q104
-/
module

public import Sheaf.AlgebraicGeometry.SchemeBigFppfQuasicoherentEquivalence
public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-! # Canonical big fppf to small etale module comparison

Source: Stacks Project, Descent, Tags 03FH and 0756; Modules on Sites, Tag 03DA.
(blueprint: def-sfb-scheme-fppf-etale-module-comparison).

Section rings retain universe u; module carriers lie in u+1, which contains the
objects of the big site. All functors use the existing ring sheaves and Mathlib's
module pullback, pushforward and right derived functors.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u c d v w r

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The inclusion of small etale objects in the big fppf slice is continuous.
Source: Stacks, Tags 03FH and 021L
(blueprint: def-sfb-scheme-fppf-etale-module-comparison).
Proof: a jointly surjective etale covering is an fppf covering, since etale
maps are flat and locally finitely presented. The same statement holds after
base change, so restriction of an fppf sheaf satisfies etale descent. -/
@[instance] theorem sfbEtaleForgetContinuous (U : Scheme.{u}) :
    (Etale.forget U).IsContinuous U.smallEtaleTopology (fppfTopology.over U) := by
  sorry

/-- The structure-ring map of small etale restriction is identity on functions.
Source: Stacks, Tag 03FH
(blueprint: def-sfb-scheme-fppf-etale-module-comparison). -/
def sfbFppfEtaleRingMap (U : Scheme.{u}) :
    Modules.smallEtaleModuleRing U ⟶
      ((Etale.forget U).sheafPushforwardContinuous RingCat.{u}
        U.smallEtaleTopology (fppfTopology.over U)).obj (sfbFppfRings U) :=
  ⟨𝟙 _⟩

/-- Restriction to the small etale site, with its actual scalar action.
Source: Stacks, Tag 03FH
(blueprint: def-sfb-scheme-fppf-etale-module-comparison). -/
def sfbFppfEtaleRestriction (U : Scheme.{u}) :
    ringedSiteModules.{u + 1} (sfbFppfRings U) ⥤
      SheafOfModules.{u + 1} (Modules.smallEtaleModuleRing U) :=
  SheafOfModules.pushforward (sfbFppfEtaleRingMap U)

/-- Module direct image has its canonical tensor left adjoint in the common universe.
Source: Stacks, Modules on Sites, construction of pullback, Tag 03DA
(blueprint: def-sfb-scheme-fppf-etale-module-comparison).
Proof: present a presheaf of modules by coproducts of free representables.
The left adjoint takes a free representable on C to the free representable on
its image in D. Extend through coproducts and cokernels, then sheafify.
All indexing sets fit in the maximum of the object, arrow and ring universes.
The free-module and sheafification universal properties give the adjunction
there, in particular for section rings in u and module carriers in u+1. -/
@[instance] theorem sfbModulePushforwardRightAdjoint
    {C : Type c} {D : Type d} [Category.{v} C] [Category.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    (R : Sheaf K RingCat.{r}) (S : Sheaf J RingCat.{r})
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R) :
    (SheafOfModules.pushforward.{max c d v w r} φ).IsRightAdjoint := by
  sorry

/-- Small etale tensor pullback at the common module universe.
Source: Stacks, Tag 03FH
(blueprint: def-sfb-scheme-fppf-etale-module-comparison). -/
def sfbEtaleModulePullback {V U : Scheme.{u}} (g : V ⟶ U) :
    SheafOfModules.{u + 1} (Modules.smallEtaleModuleRing U) ⥤
      SheafOfModules.{u + 1} (Modules.smallEtaleModuleRing V) :=
  SheafOfModules.pullback (Modules.smallEtaleModuleRingMap g)

/-- Small etale direct image at the common module universe.
Source: Stacks, Tag 03FH
(blueprint: def-sfb-scheme-fppf-etale-module-comparison). -/
def sfbEtaleModulePushforward {V U : Scheme.{u}} (g : V ⟶ U) :
    SheafOfModules.{u + 1} (Modules.smallEtaleModuleRing V) ⥤
      SheafOfModules.{u + 1} (Modules.smallEtaleModuleRing U) :=
  SheafOfModules.pushforward (Modules.smallEtaleModuleRingMap g)

/-- The postcomposition inclusion is continuous, since it preserves covering families.
Source: Stacks, Tag 03FH
(blueprint: def-sfb-scheme-fppf-etale-module-comparison).
Proof: a covering in V_et is still the same jointly surjective etale family
after postcomposition to U, hence is an fppf covering over U. -/
@[instance] theorem sfbEtaleOverContinuous {V U : Scheme.{u}} (g : V ⟶ U) :
    (Etale.forget V ⋙ Over.map g).IsContinuous V.smallEtaleTopology
      (fppfTopology.over U) := by
  sorry

/-- The postcomposition restriction has the identity map on section rings.
Source: Stacks, Tag 03FH
(blueprint: def-sfb-scheme-fppf-etale-module-comparison). -/
def sfbFppfEtaleOverRingMap {V U : Scheme.{u}} (g : V ⟶ U) :
    Modules.smallEtaleModuleRing V ⟶
      ((Etale.forget V ⋙ Over.map g).sheafPushforwardContinuous RingCat.{u}
        V.smallEtaleTopology (fppfTopology.over U)).obj (sfbFppfRings U) :=
  ⟨𝟙 _⟩

/-- Restrict to the small etale site over V by postcomposing its structure maps with g.
Source: Stacks, Tag 03FH
(blueprint: def-sfb-scheme-fppf-etale-module-comparison). -/
def sfbFppfEtaleOver {V U : Scheme.{u}} (g : V ⟶ U) :
    ringedSiteModules.{u + 1} (sfbFppfRings U) ⥤
      SheafOfModules.{u + 1} (Modules.smallEtaleModuleRing V) :=
  SheafOfModules.pushforward (sfbFppfEtaleOverRingMap g)

/-- The projection from the base changed etale scheme, regarded over U.
Source: Stacks, Tag 03FH
(blueprint: def-sfb-scheme-fppf-etale-module-comparison). -/
def sfbEtaleProjection {V U : Scheme.{u}} (g : V ⟶ U) (W : U.Etale) :
    (Over.map g).obj ((Etale.forget V).obj (g.Etale.obj W)) ⟶
      (Etale.forget U).obj W :=
  Over.homMk (pullback.fst W.hom g) pullback.condition

/-- Projection restriction preserves addition.
Source: Stacks, Tag 03FH
(blueprint: def-sfb-scheme-fppf-etale-module-comparison).
Proof: this is preservation of addition by the restriction map of G. -/
theorem sfbEtaleRestriction_add {V U : Scheme.{u}} (g : V ⟶ U)
    (G : ringedSiteModules.{u + 1} (sfbFppfRings U)) (W : U.Etaleᵒᵖ)
    (x y : ((sfbFppfEtaleRestriction U).obj G).val.obj W) :
    G.val.map (sfbEtaleProjection g W.unop).op (x + y) =
      G.val.map (sfbEtaleProjection g W.unop).op x +
        G.val.map (sfbEtaleProjection g W.unop).op y := by
  sorry

/-- Projection restriction is linear for the prescribed pulled-back scalar action.
Source: Stacks, Tag 03FH
(blueprint: def-sfb-scheme-fppf-etale-module-comparison).
Proof: semilinearity of G multiplies the restricted section by the pullback
of the scalar along the first projection. That is exactly the scalar action
in small-etale module direct image, by smallEtaleModuleRingMap. -/
theorem sfbEtaleRestriction_smul {V U : Scheme.{u}} (g : V ⟶ U)
    (G : ringedSiteModules.{u + 1} (sfbFppfRings U)) (W : U.Etaleᵒᵖ)
    (a : (Modules.smallEtaleModuleRing U).obj.obj W)
    (x : ((sfbFppfEtaleRestriction U).obj G).val.obj W) :
    G.val.map (sfbEtaleProjection g W.unop).op (a • x) =
      @SMul.smul ((Modules.smallEtaleModuleRing U).obj.obj W)
        (((sfbEtaleModulePushforward g).obj ((sfbFppfEtaleOver g).obj G)).val.obj W)
        (ModuleCat.isModule _).toSMul a
        (G.val.map (sfbEtaleProjection g W.unop).op x) := by
  sorry

/-- The linear component of projection restriction, with the same section map as G.
Source: Stacks, Tag 03FH
(blueprint: def-sfb-scheme-fppf-etale-module-comparison). -/
def sfbEtaleRestrictionComponent {V U : Scheme.{u}} (g : V ⟶ U)
    (G : ringedSiteModules.{u + 1} (sfbFppfRings U)) (W : U.Etaleᵒᵖ) :
    ((sfbFppfEtaleRestriction U).obj G).val.obj W ⟶
      (((sfbEtaleModulePushforward g).obj ((sfbFppfEtaleOver g).obj G)).val.obj W) :=
  ModuleCat.ofHom
    (X := ((sfbFppfEtaleRestriction U).obj G).val.obj W)
    (Y := ((sfbEtaleModulePushforward g).obj ((sfbFppfEtaleOver g).obj G)).val.obj W)
    { toFun := fun x ↦ G.val.map (sfbEtaleProjection g W.unop).op x
      map_add' := sfbEtaleRestriction_add g G W
      map_smul' := sfbEtaleRestriction_smul g G W }

/-- Projection restriction is natural as a linear map.
Source: Stacks, Tag 03FH
(blueprint: def-sfb-scheme-fppf-etale-module-comparison).
Proof: the two composites of projections from a base changed etale morphism
are equal by the pullback universal property. Contravariant functoriality of
G gives naturality, with the prescribed restriction of scalars. -/
theorem sfbEtaleRestrictionMap_naturality {V U : Scheme.{u}} (g : V ⟶ U)
    (G : ringedSiteModules.{u + 1} (sfbFppfRings U))
    {W W' : U.Etaleᵒᵖ} (f : W ⟶ W') :
    ((sfbFppfEtaleRestriction U).obj G).val.map f ≫
        (ModuleCat.restrictScalars
          ((Modules.smallEtaleModuleRing U).obj.map f).hom).map
          (sfbEtaleRestrictionComponent g G W') =
      sfbEtaleRestrictionComponent g G W ≫
        (((sfbEtaleModulePushforward g).obj ((sfbFppfEtaleOver g).obj G)).val.map f) := by
  sorry

/-- The direct-image comparison is restriction along the actual pullback projections.
Source: Stacks, Tag 03FH
(blueprint: def-sfb-scheme-fppf-etale-module-comparison). -/
def sfbEtaleRestrictionMap {V U : Scheme.{u}} (g : V ⟶ U)
    (G : ringedSiteModules.{u + 1} (sfbFppfRings U)) :
    (sfbFppfEtaleRestriction U).obj G ⟶
      (sfbEtaleModulePushforward g).obj ((sfbFppfEtaleOver g).obj G) where
  val.app W := sfbEtaleRestrictionComponent g G W
  val.naturality f := sfbEtaleRestrictionMap_naturality g G f

/-- The canonical comparison is the adjunction transpose of projection restriction.
Source: Stacks, Tag 0756, hypothesis (2), and Tag 03FH
(blueprint: def-sfb-scheme-fppf-etale-module-comparison). -/
def sfbFppfEtaleComparison {V U : Scheme.{u}} (g : V ⟶ U)
    (G : ringedSiteModules.{u + 1} (sfbFppfRings U)) :
    (sfbEtaleModulePullback g).obj ((sfbFppfEtaleRestriction U).obj G) ⟶
      (sfbFppfEtaleOver g).obj G :=
  ((SheafOfModules.pullbackPushforwardAdjunction.{u + 1}
    (Modules.smallEtaleModuleRingMap g)).homEquiv _ _).symm (sfbEtaleRestrictionMap g G)

/-- Raise module carriers to the common universe without changing scalars.
Source: Stacks, size convention and sectionwise description of module sheaves
(blueprint: def-sfb-scheme-fppf-etale-module-comparison). -/
def sfbModuleULiftPresheaf {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) : _root_.PresheafOfModules.{u + 1} R.obj where
  obj W := (ModuleCat.uliftFunctor.{u + 1} _).obj (M.val.obj W)
  map f := (ModuleCat.uliftFunctor.{u + 1} _).map (M.val.map f)

/-- Raising section carriers preserves the sheaf condition.
Source: Stacks, size convention and sheaf gluing
(blueprint: def-sfb-scheme-fppf-etale-module-comparison).
Proof: lower a matching family through ULift.down, glue uniquely in M, and
raise its amalgamation through ULift.up. The two inverse equations show
existence and uniqueness on every covering sieve. -/
theorem sfbModuleULift_isSheaf {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) :
    Presheaf.IsSheaf J (sfbModuleULiftPresheaf M).presheaf := by
  sorry

/-- The same module sheaf with ULift section carriers in the common universe.
Source: Stacks, size convention
(blueprint: def-sfb-scheme-fppf-etale-module-comparison). -/
def sfbModuleULift {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) : SheafOfModules.{u + 1} R :=
  ⟨sfbModuleULiftPresheaf M, sfbModuleULift_isSheaf M⟩

/-- Tensor extension from the Zariski site to the small etale site in the common universe.
Its continuity is the proved upstream theorem `gabberOpenEtale_continuous`;
its ring map is the recorded map on functions.
Source: Stacks, Tags 03FH and 03DX
(blueprint: def-sfb-scheme-fppf-etale-module-comparison). -/
def sfbZariskiEtaleExtension (U : Scheme.{u}) :
    SheafOfModules.{u + 1} U.ringCatSheaf ⥤
      SheafOfModules.{u + 1} (Modules.smallEtaleModuleRing U) :=
  letI := AlgebraicGeometry.gabberOpenEtale_continuous U
  SheafOfModules.pullback (Modules.zariskiEtaleOpenRingMap U)

/-- Module sheaves on this site have enough injectives in the common universe.
Source: Stacks, Modules on Sites, Tag 03DA; Injectives, Tag 079Q
(blueprint: def-sfb-scheme-fppf-etale-module-comparison).
Proof: sectionwise filtered colimits are exact after sheafification. The
sheafified free modules on the u+1-small family of representables generate.
Their coproduct is a generator, so the module category is Grothendieck
abelian and consequently has enough injectives. Ring carriers in u do not
change this argument: the free modules are formed in u+1. -/
@[instance] theorem sfbFppfModulesEnoughInjectives (U : Scheme.{u}) :
    EnoughInjectives (ringedSiteModules.{u + 1} (sfbFppfRings U)) := by
  sorry

/-- Global sections of a module sheaf are evaluation at the terminal structure arrow.
Source: Stacks, Tag 03DA and Tag 0756
(blueprint: def-sfb-scheme-fppf-etale-module-comparison). -/
def sfbFppfModuleGlobalSections (U : Scheme.{u}) :
    ringedSiteModules.{u + 1} (sfbFppfRings U) ⥤ AddCommGrpCat.{u + 1} :=
  SheafOfModules.toSheaf (sfbFppfRings U) ⋙
    sheafToPresheaf (fppfTopology.over U) AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation (Over U)ᵒᵖ AddCommGrpCat.{u + 1}).obj (op (Over.mk (𝟙 U)))

/-- Module global sections preserve addition of maps.
Source: Stacks, Modules on Sites, Tag 03DA
(blueprint: def-sfb-scheme-fppf-etale-module-comparison).
Proof: module maps add sectionwise; evaluation retains their sum. -/
@[instance] theorem sfbFppfModuleGlobalSections_additive (U : Scheme.{u}) :
    (sfbFppfModuleGlobalSections U).Additive := by
  sorry

end AlgebraicGeometry.Scheme
