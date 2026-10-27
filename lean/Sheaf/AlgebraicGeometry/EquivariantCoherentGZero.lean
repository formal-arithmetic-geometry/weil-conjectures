/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.AlgebraicGeometry.SchemeGroupoidModule
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import Sheaf.RingTheory.HopfActionModuleData
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

/-! # Equivariant coherent modules and their integral Grothendieck groups

Source: Stacks Project, Groupoids, definition-groupoid-module (03LF), and the
integral coherent Grothendieck-group conventions of
lem-sfb-equivariant-regular-self-intersection.
(blueprint: def-sfb-equivariant-coherent-gzero)

Linearizations use the existing groupoid-module definition. Operation predicates
specify objects up to equivariant isomorphism; no module is chosen from an
unconstrained existence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.EquivariantCoherent

variable {S : Scheme.{u}} (G Y : Over S) [GrpObj G] [ModObj G Y]

/-- Source of the action groupoid. Source: Stacks 03LF
(blueprint: def-sfb-equivariant-coherent-gzero). -/
abbrev source : (G ⊗ Y).left ⟶ Y.left := (snd G Y).left

/-- Target of the action groupoid. Source: Stacks 03LF
(blueprint: def-sfb-equivariant-coherent-gzero). -/
abbrev target : (G ⊗ Y).left ⟶ Y.left := (ModObj.smul (M := G) (X := Y)).left

/-- The identity arrow `(1,y)`. Source: Stacks 03LF
(blueprint: def-sfb-equivariant-coherent-gzero). -/
def identityArrow : Y.left ⟶ (G ⊗ Y).left :=
  (lift (1 : Y ⟶ G) (𝟙 Y)).left

/-- The inverse arrow `(g⁻¹,gy)`. Source: Stacks 03LF
(blueprint: def-sfb-equivariant-coherent-gzero). -/
def inverseArrow : (G ⊗ Y).left ⟶ (G ⊗ Y).left :=
  (lift ((fst G Y)⁻¹) (ModObj.smul (M := G) (X := Y))).left

/-- A presentation of the action groupoid on the chosen scheme pullback.
Composition is pinned on all test schemes to `(g,h,y) ↦ (gh,y)`.
Source: Stacks 03LF (blueprint: def-sfb-equivariant-coherent-gzero). -/
structure ActionGroupoidModel where
  comp : pullback (source G Y) (target G Y) ⟶ (G ⊗ Y).left
  laws : Scheme.IsGroupoid (source G Y) (target G Y)
    (identityArrow G Y) (inverseArrow G Y) comp
  group_coordinate : ∀ (T : Over S) (a b : T ⟶ G ⊗ Y)
    (h : a.left ≫ source G Y = b.left ≫ target G Y),
    pullback.lift a.left b.left h ≫ comp ≫ (fst G Y).left =
      ((a ≫ fst G Y) * (b ≫ fst G Y)).left

variable {G Y}

/-- Coherent linearized modules: the existing descent category, restricted to the
recorded coherence predicate. Source: Stacks 03LF and 01BV
(blueprint: def-sfb-equivariant-coherent-gzero). -/
abbrev Coherent (D : ActionGroupoidModel G Y) :=
  ObjectProperty.FullSubcategory (fun M : Scheme.GroupoidModule (source G Y) (target G Y)
    (identityArrow G Y) (inverseArrow G Y) D.comp D.laws =>
      RingedSpace.IsCoherent Y.left.toRingedSpace M.moduleObj)

/-- The underlying module. Source: Stacks 03LF
(blueprint: def-sfb-equivariant-coherent-gzero). -/
abbrev underlying {D : ActionGroupoidModel G Y} (M : Coherent D) : Y.left.Modules :=
  M.obj.moduleObj

/-- Unwrap the opaque pullback interface, without changing the functor.
Source: Stacks 0096 (blueprint: def-sfb-equivariant-coherent-gzero). -/
def pullbackIso {X Z : Scheme.{u}} (f : X ⟶ Z) :
    Scheme.groupoidModulePullback f ≅ Scheme.Modules.tensorPullback f := by
  unfold Scheme.groupoidModulePullback
  exact Iso.refl _

/-- The recorded linearization, transported through the opaque interface.
Source: Stacks 03LF (blueprint: def-sfb-equivariant-coherent-gzero). -/
def linearization {D : ActionGroupoidModel G Y} (M : Coherent D) :
    (Scheme.Modules.tensorPullback (target G Y)).obj (underlying M) ≅
      (Scheme.Modules.tensorPullback (source G Y)).obj (underlying M) :=
  (pullbackIso (target G Y)).symm.app (underlying M) ≪≫ M.obj.beta ≪≫
    (pullbackIso (source G Y)).app (underlying M)

/-- The underlying equivariant module map. Source: Stacks 03LF
(blueprint: def-sfb-equivariant-coherent-gzero). -/
abbrev underlyingMap {D : ActionGroupoidModel G Y} {M N : Coherent D} (f : M ⟶ N) :
    underlying M ⟶ underlying N := f.hom.val

/-- The two kinds of defining relation, including all equivariant short exact sequences.
Source: the integral G-zero presentation in the item
(blueprint: def-sfb-equivariant-coherent-gzero). -/
def IsGZeroRelation (D : ActionGroupoidModel G Y)
    (z : FreeAbelianGroup (Coherent D)) : Prop :=
  (∃ M N : Coherent D, Nonempty (M ≅ N) ∧
    z = FreeAbelianGroup.of M - FreeAbelianGroup.of N) ∨
  (∃ (A B C : Coherent D) (f : A ⟶ B) (g : B ⟶ C)
    (h : underlyingMap f ≫ underlyingMap g = 0),
    (ShortComplex.mk (underlyingMap f) (underlyingMap g) h).ShortExact ∧
    z = FreeAbelianGroup.of B - FreeAbelianGroup.of A - FreeAbelianGroup.of C)

/-- The subgroup generated by isomorphism and short-exact-sequence relations.
Source: the integral G-zero presentation in the item
(blueprint: def-sfb-equivariant-coherent-gzero). -/
def relations (D : ActionGroupoidModel G Y) : AddSubgroup (FreeAbelianGroup (Coherent D)) :=
  AddSubgroup.closure {z | IsGZeroRelation D z}

/-- The integral equivariant coherent Grothendieck group, constructed as a quotient.
Source: the integral G-zero presentation in the item
(blueprint: def-sfb-equivariant-coherent-gzero). -/
abbrev GZero (D : ActionGroupoidModel G Y) := FreeAbelianGroup (Coherent D) ⧸ relations D

/-- The class of a coherent linearized module. Source: the integral G-zero presentation
in the item (blueprint: def-sfb-equivariant-coherent-gzero). -/
def classOf {D : ActionGroupoidModel G Y} (M : Coherent D) : GZero D :=
  QuotientAddGroup.mk (FreeAbelianGroup.of M)

/-- The existing sheaf tensor, with its commutative-ring structure explicit.
Source: Stacks 01CA (blueprint: def-sfb-equivariant-coherent-gzero). -/
def moduleTensor {X : Scheme.{u}} (M N : X.Modules) : X.Modules :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  M ⊗ N

/-- Tensoring module maps, for the existing sheaf tensor.
Source: Stacks 01CA (blueprint: def-sfb-equivariant-coherent-gzero). -/
def moduleTensorMap {X : Scheme.{u}} {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') : moduleTensor M N ⟶ moduleTensor M' N' :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  f ⊗ₘ g

/-- The canonical tensor comparison from the recorded module-pullback theorem.
Source: Stacks 01CD (blueprint: def-sfb-equivariant-coherent-gzero). -/
def tensorComparison {X Z : Scheme.{u}} (f : X ⟶ Z) (M N : Z.Modules) :
    (Scheme.Modules.tensorPullback f).obj (moduleTensor M N) ≅
      moduleTensor ((Scheme.Modules.tensorPullback f).obj M)
        ((Scheme.Modules.tensorPullback f).obj N) :=
  (Classical.choose (Scheme.Modules.module_pullback_tensor f)) M N

/-- A tensor product with the induced linearization, characterized by the canonical
pullback-tensor comparison. Source: Stacks 03LF and 01CD
(blueprint: def-sfb-equivariant-coherent-gzero). -/
def IsTensor {D : ActionGroupoidModel G Y} (M N P : Coherent D) : Prop :=
  ∃ e : underlying P ≅ moduleTensor (underlying M) (underlying N),
    (Scheme.Modules.tensorPullback (target G Y)).map e.hom ≫
        (tensorComparison (target G Y) (underlying M) (underlying N)).hom ≫
        moduleTensorMap (linearization M).hom (linearization N).hom =
      (linearization P).hom ≫ (Scheme.Modules.tensorPullback (source G Y)).map e.hom ≫
        (tensorComparison (source G Y) (underlying M) (underlying N)).hom

/-- Comparison of pullbacks along equal composites with different intermediate schemes.
Source: Stacks 0097 (blueprint: def-sfb-equivariant-coherent-gzero). -/
def mixedCompComparison {P A B X : Scheme.{u}} (a : P ⟶ A) (b : P ⟶ B)
    (f : A ⟶ X) (g : B ⟶ X) (h : a ≫ f = b ≫ g) (M : X.Modules) :
    (Scheme.Modules.tensorPullback a).obj ((Scheme.Modules.tensorPullback f).obj M) ≅
      (Scheme.Modules.tensorPullback b).obj ((Scheme.Modules.tensorPullback g).obj M) := by
  exact (Scheme.Modules.tensorPullbackSectionComp a f).symm.app M ≪≫
    eqToIso (congrArg (fun k : P ⟶ X => (Scheme.Modules.tensorPullback k).obj M) h) ≪≫
    (Scheme.Modules.tensorPullbackSectionComp b g).app M

/-- Equivariance of a map from an ordinary pullback. Its square uses the canonical
composition comparisons of the existing groupoid module interface.
Source: Stacks 03LF and 0097 (blueprint: def-sfb-equivariant-coherent-gzero). -/
def IsPullbackMap {W : Over S} [ModObj G W]
    {DY : ActionGroupoidModel G Y} {DW : ActionGroupoidModel G W}
    (i : W ⟶ Y) [IsModHom G i] (M : Coherent DY) (N : Coherent DW)
    (f : (Scheme.Modules.tensorPullback i.left).obj (underlying M) ⟶ underlying N) : Prop :=
  ∀ (ha : target G W ≫ i.left =
      (G ◁ i).left ≫ target G Y)
    (hp : source G W ≫ i.left = (G ◁ i).left ≫ source G Y),
    (Scheme.Modules.tensorPullback (target G W)).map f ≫ (linearization N).hom =
      (mixedCompComparison (target G W) (G ◁ i).left
        i.left (target G Y) ha (underlying M)).hom ≫
      (Scheme.Modules.tensorPullback (G ◁ i).left).map (linearization M).hom ≫
      (mixedCompComparison (source G W) (G ◁ i).left
        i.left (source G Y) hp (underlying M)).inv ≫
      (Scheme.Modules.tensorPullback (source G W)).map f

/-- Pullback with its induced equivariance, specified up to equivariant isomorphism.
Source: Stacks 03LF and 0096 (blueprint: def-sfb-equivariant-coherent-gzero). -/
def IsPullback {W : Over S} [ModObj G W]
    {DY : ActionGroupoidModel G Y} {DW : ActionGroupoidModel G W}
    (i : W ⟶ Y) [IsModHom G i] (M : Coherent DY) (N : Coherent DW) : Prop :=
  ∃ f : (Scheme.Modules.tensorPullback i.left).obj (underlying M) ⟶ underlying N,
    IsIso f ∧ IsPullbackMap i M N f

/-- Pushforward with its induced equivariance: the adjoint map is invertible, and
its counit is equivariant. Source: Stacks 03LF and 0096
(blueprint: def-sfb-equivariant-coherent-gzero). -/
def IsPushforward {W : Over S} [ModObj G W]
    {DY : ActionGroupoidModel G Y} {DW : ActionGroupoidModel G W}
    (i : W ⟶ Y) [IsModHom G i] (N : Coherent DW) (M : Coherent DY) : Prop :=
  ∃ f : (Scheme.Modules.tensorPullback i.left).obj (underlying M) ⟶ underlying N,
    IsPullbackMap i M N f ∧
      IsIso ((Scheme.Modules.tensorPullbackSectionAdjunction i.left).homEquiv _ _ f)

/-- The structure sheaf with its natural linearization.
Source: Stacks 03LF (blueprint: def-sfb-equivariant-coherent-gzero). -/
def IsUnitIso {D : ActionGroupoidModel G Y} (M : Coherent D)
    (e : underlying M ≅ SheafOfModules.unit Y.left.ringCatSheaf) : Prop :=
  (Scheme.Modules.tensorPullback (target G Y)).map e.hom ≫
      Scheme.Modules.tensorPullbackObjUnitToUnit (target G Y) =
    (linearization M).hom ≫ (Scheme.Modules.tensorPullback (source G Y)).map e.hom ≫
      Scheme.Modules.tensorPullbackObjUnitToUnit (source G Y)

/-- The structure sheaf with its natural linearization, up to equivariant isomorphism.
Source: Stacks 03LF (blueprint: def-sfb-equivariant-coherent-gzero). -/
def IsUnit {D : ActionGroupoidModel G Y} (M : Coherent D) : Prop :=
  ∃ e : underlying M ≅ SheafOfModules.unit Y.left.ringCatSheaf, IsUnitIso M e

/-- The ideal of an invariant closed subscheme, as an equivariant submodule of O_Y.
Source: Stacks 03LF and 0473 (blueprint: def-sfb-equivariant-coherent-gzero). -/
def IsIdeal {D : ActionGroupoidModel G Y} {W : Scheme.{u}} (i : W ⟶ Y.left)
    (K : Coherent D) : Prop :=
  ∃ (O : Coherent D) (eO : underlying O ≅ SheafOfModules.unit Y.left.ringCatSheaf)
    (eK : underlying K ≅ i.ker.toModules) (f : K ⟶ O),
    IsUnitIso O eO ∧ underlyingMap f ≫ eO.hom = eK.hom ≫ i.ker.toModulesι

/-- Exterior powers with induced linearization. Pullback comparisons are normalized
on wedge sections; their equivariance is tested on all wedge generators.
Source: Stacks 03LF, 01CD, and the exterior-power universal property
(blueprint: def-sfb-equivariant-coherent-gzero). -/
def IsExterior {D : ActionGroupoidModel G Y} (N : Coherent D) (q : ℕ)
    (P : Coherent D) : Prop :=
  ∃ (e : underlying P ≅ Scheme.Modules.exteriorPower (underlying N) q)
    (ea : (Scheme.Modules.tensorPullback (target G Y)).obj (underlying P) ≅
      Scheme.Modules.exteriorPower
        ((Scheme.Modules.tensorPullback (target G Y)).obj (underlying N)) q)
    (ep : (Scheme.Modules.tensorPullback (source G Y)).obj (underlying P) ≅
      Scheme.Modules.exteriorPower
        ((Scheme.Modules.tensorPullback (source G Y)).obj (underlying N)) q),
    (∀ (U : Y.left.Opens) (v : Fin q → Γ(underlying N, U)),
      ea.hom.app ((target G Y) ⁻¹ᵁ U)
          (Scheme.Modules.tensorPullbackSection (target G Y) (underlying P) U
            (e.inv.app U (Scheme.Modules.wedge v))) =
        Scheme.Modules.wedge (fun k =>
          Scheme.Modules.tensorPullbackSection (target G Y) (underlying N) U (v k))) ∧
    (∀ (U : Y.left.Opens) (v : Fin q → Γ(underlying N, U)),
      ep.hom.app ((source G Y) ⁻¹ᵁ U)
          (Scheme.Modules.tensorPullbackSection (source G Y) (underlying P) U
            (e.inv.app U (Scheme.Modules.wedge v))) =
        Scheme.Modules.wedge (fun k =>
          Scheme.Modules.tensorPullbackSection (source G Y) (underlying N) U (v k))) ∧
    ∀ (V : (G ⊗ Y).left.Opens)
      (v : Fin q → Γ((Scheme.Modules.tensorPullback (target G Y)).obj (underlying N), V)),
      (linearization P).hom.app V (ea.inv.app V (Scheme.Modules.wedge v)) =
        ep.inv.app V (Scheme.Modules.wedge (fun k => (linearization N).hom.app V (v k)))

end AlgebraicGeometry.EquivariantCoherent
