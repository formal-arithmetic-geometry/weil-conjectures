/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory

/-! # The category of line bundles in a scheme family

Source: Stacks Project, examples-stacks.tex, section-picard-stack
(blueprint: def-sfb-line-bundle-moduli).

Objects retain the actual invertible module on the base change. Arrows retain the
actual tensor-pullback isomorphism, with its canonical identity and composition.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A test scheme over the base together with a line bundle on the pulled-back family.
Source: Stacks, examples-stacks.tex, section-picard-stack
(blueprint: def-sfb-line-bundle-moduli). -/
structure LineBundleModuli {X S : Scheme.{u}} (f : X ⟶ S) where
  base : Over S
  module : (pullback f base.hom).Modules
  invertible : module.IsInvertible

namespace LineBundleModuli

/-- An arrow over `a.base` is an isomorphism from the pulled-back target line bundle.
Source: Stacks, examples-stacks.tex, section-picard-stack
(blueprint: def-sfb-line-bundle-moduli). -/
structure Hom {X S : Scheme.{u}} {f : X ⟶ S} (A B : LineBundleModuli f) where
  base : A.base ⟶ B.base
  iso : (Scheme.Modules.moduleBaseChange f base).obj B.module ≅ A.module

/-- The identity arrow uses the section-normalized identity tensor-pullback comparison.
Source: Stacks, examples-stacks.tex, section-picard-stack; Sheaves, Tag 0097
(blueprint: def-sfb-line-bundle-moduli). -/
def identity {X S : Scheme.{u}} {f : X ⟶ S} (A : LineBundleModuli f) : Hom A A where
  base := 𝟙 A.base
  iso := eqToIso (congrArg (fun g ↦ (Scheme.Modules.tensorPullback g).obj A.module)
      (baseChangeMap_id f A.base)) ≪≫
    (Scheme.Modules.tensorPullbackSectionId _).app A.module

/-- Composition is pullback of the second isomorphism followed by the first one.
Source: Stacks, examples-stacks.tex, section-picard-stack; Sheaves, Tag 0097
(blueprint: def-sfb-line-bundle-moduli). -/
def composition {X S : Scheme.{u}} {f : X ⟶ S} {A B C : LineBundleModuli f}
    (a : Hom A B) (b : Hom B C) : Hom A C where
  base := a.base ≫ b.base
  iso := eqToIso (congrArg (fun g ↦ (Scheme.Modules.tensorPullback g).obj C.module)
      (baseChangeMap_comp f a.base b.base)) ≪≫
    (Scheme.Modules.tensorPullbackSectionComp
      (baseChangeMap f a.base) (baseChangeMap f b.base)).app C.module ≪≫
    (Scheme.Modules.moduleBaseChange f a.base).mapIso b.iso ≪≫ a.iso

/-- The specified pullback operations satisfy the category laws.
Source: Stacks, examples-stacks.tex, section-picard-stack; Sheaves, Tag 0097
(blueprint: def-sfb-line-bundle-moduli).
Proof: base arrows obey the category laws in `Over S`. The normalized identity
and composition comparisons are induced by tensor-pullback adjunctions with unit
`m ↦ 1 tensor m` (def-pc-module-pullback). Evaluate both identity composites and
both associations of a triple composite on local pure tensors. The identity
comparisons give the original tensor, and both associations give the same
iterated tensor. Pure tensors generate locally, so the module morphisms agree;
the isomorphisms then agree. The base-change map identity and composition
equalities (def-pc-base-change) account for the displayed transports. Thus the
explicit operations obey all three laws. Only proof fields are postponed. -/
theorem category_laws {X S : Scheme.{u}} (f : X ⟶ S) :
    (∀ {A B : LineBundleModuli f} (a : Hom A B), composition (identity A) a = a) ∧
    (∀ {A B : LineBundleModuli f} (a : Hom A B), composition a (identity B) = a) ∧
    (∀ {A B C D : LineBundleModuli f} (a : Hom A B) (b : Hom B C) (c : Hom C D),
      composition (composition a b) c = composition a (composition b c)) := by
  sorry

/-- The category with the specified pullback-isomorphism arrows and operations.
Source: Stacks, examples-stacks.tex, section-picard-stack
(blueprint: def-sfb-line-bundle-moduli). -/
instance {X S : Scheme.{u}} {f : X ⟶ S} : Category (LineBundleModuli f) where
  Hom := Hom
  id := identity
  comp := composition
  id_comp := (category_laws f).1
  comp_id := (category_laws f).2.1
  assoc := (category_laws f).2.2

/-- Projection remembers the test scheme and the base arrow of each isomorphism.
Source: Stacks, examples-stacks.tex, section-picard-stack
(blueprint: def-sfb-line-bundle-moduli). -/
def forget {X S : Scheme.{u}} (f : X ⟶ S) : LineBundleModuli f ⥤ Over S where
  obj A := A.base
  map a := a.base

/-- The actual line-bundle category over schemes over the base.
Source: Stacks, examples-stacks.tex, section-picard-stack
(blueprint: def-sfb-line-bundle-moduli). -/
def category {X S : Scheme.{u}} (f : X ⟶ S) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor (forget f)

end LineBundleModuli

end AlgebraicGeometry
