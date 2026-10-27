/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import WeilConjectures.AlgebraicGeometry.Thickening
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Topology.SheafCotangentComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Marked flat scheme lifts

Source: Stacks Project, Deformation Theory, Tag 0D14
(blueprint: def-sfb-marked-scheme-lifts).

The full subcategory retains all marking-preserving arrows, so its categorical
isomorphisms and automorphisms have exactly the required meaning.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.SchemeDeformation

/-- Flat cartesian marked lifts, as a full subcategory of schemes over the thickened
base under the fixed special fibre. Source: Stacks 0D14
(blueprint: def-sfb-marked-scheme-lifts). -/
abbrev Lift {X S S' : Scheme.{u}} (f : X ⟶ S) (i : S ⟶ S') :=
  ObjectProperty.FullSubcategory (fun Y : Under (Over.mk (f ≫ i)) ↦
    Flat Y.right.hom ∧ IsPullback Y.hom.left f Y.right.hom i)

/-- The thickened scheme. Source: Stacks 0D14
(blueprint: def-sfb-marked-scheme-lifts). -/
abbrev Lift.space {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'}
    (Y : Lift f i) : Scheme.{u} := Y.obj.right.left

/-- The flat structure map. Source: Stacks 0D14
(blueprint: def-sfb-marked-scheme-lifts). -/
abbrev Lift.projection {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'}
    (Y : Lift f i) : Y.space ⟶ S' := Y.obj.right.hom

/-- The marked special fibre, given as a cartesian reduction arrow. Source: Stacks 0D14
(blueprint: def-sfb-marked-scheme-lifts). -/
abbrev Lift.marking {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'}
    (Y : Lift f i) : X ⟶ Y.space := Y.obj.hom.left

/-- Actual isomorphism classes of marked flat lifts. Source: Stacks 0D14
(blueprint: def-sfb-marked-scheme-lifts). -/
def Classes {X S S' : Scheme.{u}} (f : X ⟶ S) (i : S ⟶ S') :=
  Quot (fun Y Z : Lift f i ↦ Nonempty (Y ≅ Z))

/-- The class of a lift. Source: Stacks 0D14
(blueprint: def-sfb-marked-scheme-lifts). -/
def Lift.class {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'}
    (Y : Lift f i) : Classes f i := Quot.mk _ Y

/-- A marked cartesian restriction, also used for arbitrary maps of the reduced
scheme. Source: Stacks 0D14, 0GQ1
(blueprint: def-sfb-marked-scheme-lifts). -/
def IsRestriction {X U S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'}
    (j : U ⟶ X) (Y : Lift f i) (Z : Lift (j ≫ f) i) (q : Z.space ⟶ Y.space) : Prop :=
  IsPullback Z.marking j q Y.marking ∧ q ≫ Y.projection = Z.projection

/-- Marked base change along a map of thickened bases fixing their reduction.
Source: Stacks 0D14, 0GQ1 (blueprint: def-sfb-marked-scheme-lifts). -/
def IsBaseChange {X S S₁ S₂ : Scheme.{u}} {f : X ⟶ S}
    {i₁ : S ⟶ S₁} {i₂ : S ⟶ S₂} (b : S₂ ⟶ S₁)
    (Y : Lift f i₁) (Z : Lift f i₂) (q : Z.space ⟶ Y.space) : Prop :=
  i₂ ≫ b = i₁ ∧ IsPullback q Z.projection Y.projection b ∧ Z.marking ≫ q = Y.marking

/-- The special-fibre module `f* (I/I²)`, which equals `f* I` for a first-order
thickening. The two pullbacks are the recorded tensor pullbacks.
Source: Stacks 0D14 (blueprint: def-sfb-marked-scheme-lifts). -/
def coefficient {X S S' : Scheme.{u}} (f : X ⟶ S) (i : S ⟶ S') : X.Modules :=
  (Scheme.Modules.tensorPullback f).obj
    ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)

/-- The standard sheaf cotangent complex attached to the actual inverse-image
ring map. Source: Stacks 08SS, 08UW (blueprint: def-sfb-marked-scheme-lifts). -/
def cotangentComplex
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Algebra.CotangentResolution.Coherence.{u})
    (D : TopCat.SheafCotangent.Comparison C) {X S : Scheme.{u}} (f : X ⟶ S) :
    CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ :=
  TopCat.SheafCotangent.sheafComplex
    (D.sheaves X.carrier (Arrow.mk (Scheme.Modules.tensorPullbackRingMap f))).sections

/-- Cotangent Ext is a derived Hom into the shifted degree-zero module.
Source: Stacks 0D14, 08UZ (blueprint: def-sfb-marked-scheme-lifts). -/
abbrev Ext
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Algebra.CotangentResolution.Coherence.{u})
    (D : TopCat.SheafCotangent.Comparison C) {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)] (G : X.Modules) (n : ℤ) :=
  (DerivedCategory.Q.obj (cotangentComplex C D f) ⟶
    ((DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).obj G)⟦n⟧)

/-- The right module structure associated to a commutative coefficient field.
Source: Stacks 0D14, split square-zero bases
(blueprint: def-sfb-marked-scheme-lifts). -/
instance directionOppositeModule (k : Type u) [Field k] (M : ModuleCat.{u} k) :
    Module kᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id k).fromOpposite (fun a b ↦ Commute.all a b))

/-- The right and left actions agree. Source: Stacks 0D14
(blueprint: def-sfb-marked-scheme-lifts). -/
instance directionCentralScalar (k : Type u) [Field k] (M : ModuleCat.{u} k) :
    IsCentralScalar k M where
  op_smul_eq_smul _ _ := rfl

/-- Split square-zero bases use Mathlib's actual ring `k ⊕ M`.
Source: Stacks 0D14, 0GPZ (blueprint: def-sfb-marked-scheme-lifts). -/
def directionReduction (k : Type u) [Field k] (M : ModuleCat.{u} k) :
    Spec (.of k) ⟶ Spec (.of (TrivSqZeroExt k M)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k M).toRingHom)

/-- Projection of the split base to the field. Source: Stacks 0GPZ
(blueprint: def-sfb-marked-scheme-lifts). -/
def directionProjection (k : Type u) [Field k] (M : ModuleCat.{u} k) :
    Spec (.of (TrivSqZeroExt k M)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom k M))

/-- A linear coefficient map induces the actual map of split bases.
Source: Stacks 0GQ1, 0GQ2 (blueprint: def-sfb-marked-scheme-lifts). -/
def directionMap {k : Type u} [Field k] {M N : ModuleCat.{u} k} (a : M ⟶ N) :
    Spec (.of (TrivSqZeroExt k N)) ⟶ Spec (.of (TrivSqZeroExt k M)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map a.hom).toRingHom)

/-- A zero deformation is the actual trivial family, characterized by its cartesian
projection to the original scheme and identity marking. Source: Stacks 0GPZ
(blueprint: def-sfb-marked-scheme-lifts). -/
def IsTrivial {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (M : ModuleCat.{u} k)
    (Y : Lift f (directionReduction k M)) : Prop :=
  ∃ q : Y.space ⟶ X, IsPullback q Y.projection f (directionProjection k M) ∧
    Y.marking ≫ q = 𝟙 X

/-- Addition of split deformations: glue two directions, then apply their addition.
Every arrow is a cartesian marked base change. Source: Stacks 0GQ0, 0GQ2
(blueprint: def-sfb-marked-scheme-lifts). -/
def IsSum {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (M : ModuleCat.{u} k) (Y Z W : Lift f (directionReduction k M)) : Prop :=
  ∃ T : Lift f (directionReduction k (ModuleCat.of k (M × M))),
    ∃ (q₁ : Y.space ⟶ T.space) (q₂ : Z.space ⟶ T.space) (q₃ : W.space ⟶ T.space),
      IsBaseChange (directionMap (ModuleCat.ofHom (LinearMap.fst k M M))) T Y q₁ ∧
      IsBaseChange (directionMap (ModuleCat.ofHom (LinearMap.snd k M M))) T Z q₂ ∧
      IsBaseChange (directionMap
        (ModuleCat.ofHom (LinearMap.fst k M M + LinearMap.snd k M M))) T W q₃

/-- The coefficient sheaf `O_X ⊗_k M`, constructed by module sheafification and
actual tensor pullback. Source: Stacks 0GPZ
(blueprint: def-sfb-marked-scheme-lifts). -/
def directionModule {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (M : ModuleCat.{u} k) : X.Modules :=
  (Scheme.Modules.tensorPullback f).obj ((tilde.functor (.of k)).obj M)

/-- The map `1 ⊗ a` on coefficient sheaves. Source: Stacks 0GQ1
(blueprint: def-sfb-marked-scheme-lifts). -/
def directionModuleMap {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {M N : ModuleCat.{u} k} (a : M ⟶ N) :
    directionModule f M ⟶ directionModule f N :=
  (Scheme.Modules.tensorPullback f).map ((tilde.functor (.of k)).map a)

end AlgebraicGeometry.SchemeDeformation
