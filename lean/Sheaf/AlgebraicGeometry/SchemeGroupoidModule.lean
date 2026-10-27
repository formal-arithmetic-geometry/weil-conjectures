/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.AlgebraicGeometry.SchemeGroupoidLaws
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Quasi-coherent modules on a scheme groupoid

Source: Stacks Project, Groupoids, Definition `definition-groupoid-module`
(blueprint: def-sfb-scheme-groupoid-module).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The existing tensor pullback, with an opaque interface for descent equations.
Source: Stacks Project, Groupoids, `definition-groupoid-module`
(blueprint: def-sfb-scheme-groupoid-module).
This is exactly the recorded tensor functor; opacity avoids expanding its sheafification
construction when checking repeated occurrences in descent equations. -/
@[irreducible] noncomputable def groupoidModulePullback {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Y.Modules ⥤ X.Modules := Modules.tensorPullback g

/-- The canonical identification of iterated pullbacks with equal composite maps.
Source: Stacks Project, Groupoids, `definition-groupoid-module`, canonical identifications
(blueprint: def-sfb-scheme-groupoid-module). -/
@[irreducible] noncomputable def groupoidModuleCompComparison {P R U : Scheme.{u}}
    (a b : P ⟶ R) (f g : R ⟶ U) (h : a ≫ f = b ≫ g) (M : U.Modules) :
    (groupoidModulePullback a).obj ((groupoidModulePullback f).obj M) ≅
      (groupoidModulePullback b).obj ((groupoidModulePullback g).obj M) := by
  unfold groupoidModulePullback
  exact (Modules.tensorPullbackSectionComp a f).symm.app M ≪≫
    eqToIso (congrArg (fun k : P ⟶ U => (Modules.tensorPullback k).obj M) h) ≪≫
    (Modules.tensorPullbackSectionComp b g).app M

/-- The canonical identification along a section of a scheme morphism.
Source: Stacks Project, Groupoids, `definition-groupoid-module`, identity law
(blueprint: def-sfb-scheme-groupoid-module). -/
@[irreducible] noncomputable def groupoidModuleUnitComparison {U R : Scheme.{u}}
    (e : U ⟶ R) (f : R ⟶ U) (h : e ≫ f = 𝟙 U) (M : U.Modules) :
    (groupoidModulePullback e).obj ((groupoidModulePullback f).obj M) ≅ M := by
  unfold groupoidModulePullback
  exact (Modules.tensorPullbackSectionComp e f).symm.app M ≪≫
    eqToIso (congrArg (fun k : U ⟶ U => (Modules.tensorPullback k).obj M) h) ≪≫
    (Modules.tensorPullbackSectionId U).app M

/-- The identity law for the descent isomorphism, using canonical comparisons.
Source: Stacks Project, Groupoids, `definition-groupoid-module`
(blueprint: def-sfb-scheme-groupoid-module). -/
def groupoidModuleUnitLaw {U R : Scheme.{u}} (s t : R ⟶ U) (e : U ⟶ R)
    (hs : e ≫ s = 𝟙 U) (ht : e ≫ t = 𝟙 U) (M : U.Modules)
    (beta : (groupoidModulePullback t).obj M ≅ (groupoidModulePullback s).obj M) : Prop :=
  (groupoidModulePullback e).map beta.hom ≫
      (groupoidModuleUnitComparison e s hs M).hom =
    (groupoidModuleUnitComparison e t ht M).hom

/-- The cocycle law for the descent isomorphism, using canonical comparisons.
Source: Stacks Project, Groupoids, `definition-groupoid-module`
(blueprint: def-sfb-scheme-groupoid-module). -/
def groupoidModuleCocycleLaw {U R : Scheme.{u}} (s t : R ⟶ U)
    (c : pullback s t ⟶ R)
    (hs : c ≫ s = pullback.snd s t ≫ s) (ht : c ≫ t = pullback.fst s t ≫ t)
    (M : U.Modules)
    (beta : (groupoidModulePullback t).obj M ≅ (groupoidModulePullback s).obj M) : Prop :=
  (groupoidModulePullback c).map beta.hom ≫
      (groupoidModuleCompComparison c (pullback.snd s t) s s hs M).hom =
    (groupoidModuleCompComparison c (pullback.fst s t) t t ht M).hom ≫
      (groupoidModulePullback (pullback.fst s t)).map beta.hom ≫
      (groupoidModuleCompComparison (pullback.fst s t) (pullback.snd s t) s t
        pullback.condition M).hom ≫
      (groupoidModulePullback (pullback.snd s t)).map beta.hom

/-- A quasi-coherent module with the specified groupoid descent isomorphism.
Source: Stacks Project, Groupoids, `definition-groupoid-module` and `lemma-isomorphism`
(blueprint: def-sfb-scheme-groupoid-module).
The two laws use the section-normalized tensor-pullback comparisons. The first
projection of the scheme pullback is the later arrow, as in `Scheme.IsGroupoid`. -/
structure GroupoidModule {U R : Scheme.{u}} (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s t ⟶ R) (hG : IsGroupoid s t e i c) where
  /-- The underlying module on the object scheme. -/
  moduleObj : U.Modules
  /-- Quasi-coherence, with no finiteness assumption. -/
  quasiCoherent : SheafOfModules.IsQuasicoherent (R := U.ringCatSheaf) moduleObj
  /-- Descent isomorphism, from target pullback to source pullback. -/
  beta : (groupoidModulePullback t).obj moduleObj ≅
    (groupoidModulePullback s).obj moduleObj
  /-- Pulling descent back along the identity gives the identity. -/
  unit : groupoidModuleUnitLaw s t e hG.source_id hG.target_id moduleObj beta
  /-- Descent along a composite is descent along its two successive arrows. -/
  cocycle : groupoidModuleCocycleLaw s t c hG.source_comp hG.target_comp moduleObj beta

namespace GroupoidModule

variable {U R : Scheme.{u}} {s t : R ⟶ U} {e : U ⟶ R} {i : R ⟶ R}
  {c : pullback s t ⟶ R} {hG : IsGroupoid s t e i c}

/-- Morphisms are precisely module maps intertwining descent.
Source: Stacks Project, Groupoids, morphisms following `definition-groupoid-module`
(blueprint: def-sfb-scheme-groupoid-module). -/
def Hom (M N : GroupoidModule s t e i c hG) :=
  {f : M.moduleObj ⟶ N.moduleObj //
    (groupoidModulePullback t).map f ≫ N.beta.hom =
      M.beta.hom ≫ (groupoidModulePullback s).map f}

/-- Composition and identities of equivariant module maps are the underlying ones.
Source: Stacks Project, Groupoids, `definition-groupoid-module`
(blueprint: def-sfb-scheme-groupoid-module). -/
instance category : Category (GroupoidModule s t e i c hG) where
  Hom := GroupoidModule.Hom
  id M := ⟨𝟙 M.moduleObj, by simp⟩
  comp f g := ⟨f.val ≫ g.val, by
    simp only [Functor.map_comp, Category.assoc]
    rw [g.property, ← Category.assoc, f.property]
    simp only [Category.assoc]⟩
  id_comp f := by apply Subtype.ext; simp
  comp_id f := by apply Subtype.ext; simp
  assoc f g h := by apply Subtype.ext; simp only [Category.assoc]

/-- Forgetting descent to the existing full subcategory of quasi-coherent modules.
Source: Stacks Project, Groupoids, `definition-groupoid-module`
(blueprint: def-sfb-scheme-groupoid-module). -/
def forgetToQuasiCoherent : GroupoidModule s t e i c hG ⥤
    (SheafOfModules.isQuasicoherent (R := U.ringCatSheaf)).FullSubcategory where
  obj M := ⟨M.moduleObj, M.quasiCoherent⟩
  map f := ObjectProperty.homMk f.val
  map_id _M := rfl
  map_comp _f _g := rfl

/-- The underlying module functor, including quasi-coherent modules in all modules.
Source: Stacks Project, Groupoids, `definition-groupoid-module`
(blueprint: def-sfb-scheme-groupoid-module). -/
def forgetToModules : GroupoidModule s t e i c hG ⥤ U.Modules where
  obj M := M.moduleObj
  map f := f.val
  map_id _M := rfl
  map_comp _f _g := rfl

end GroupoidModule
end AlgebraicGeometry.Scheme
